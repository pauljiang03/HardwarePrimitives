"""Run exact regressions with: python3 validation/check_revision.py.

All results are model-derived, never device measurements. The independent
rounding oracle searches neighboring FP32 encodings; it does not call encode.
"""
import json
import random
from pathlib import Path
from exact_model import *

def neighbor_round(x, mode='rne'):
    x = Q(x)
    if not x:
        return 0
    sign = 0x80000000 if x < 0 else 0
    x = abs(x)
    assert x <= oracle_value(0x7f7fffff, 'fp32')
    low, high = 0, 0x7f7fffff
    while low < high:
        mid = (low + high + 1) // 2
        if oracle_value(mid, 'fp32') <= x:
            low = mid
        else:
            high = mid - 1
    if mode == 'rtz' or oracle_value(low, 'fp32') == x:
        return low | sign
    assert mode == 'rne'
    up = low + 1
    dl, du = x - oracle_value(low, 'fp32'), oracle_value(up, 'fp32') - x
    return (low if dl < du or (dl == du and low % 2 == 0) else up) | sign

def integer_block_oracle(a, b, c, profile):
    """Independent implementation of the specified raw-alignment model.

    Direct bit fields -> integer significand products -> magnitude shifts.
    Does not use decode, value, exponent, trunc, encode, or recovery components.
    Profiles are the shared specification, not independent hardware evidence.
    """
    fmt, k, p, floor = PROFILES[profile]
    eb, fb = FORMATS[fmt]
    bias = (1 << (eb - 1)) - 1
    terms = []  # signed integer, integer's value scale, raw alignment scale
    for x, y in zip(a, b):
        ex, fx = divmod(x & ((1 << (eb + fb)) - 1), 1 << fb)
        ey, fy = divmod(y & ((1 << (eb + fb)) - 1), 1 << fb)
        mx, my = fx + ((1 << fb) if ex else 0), fy + ((1 << fb) if ey else 0)
        rho = max(ex, 1) + max(ey, 1) - 2 * bias
        sign = -1 if (x ^ y) >> (eb + fb) else 1
        terms.append((sign * mx * my, rho - 2 * fb, rho))
    ec, fc = divmod(c & 0x7fffffff, 1 << 23)
    mc = fc + ((1 << 23) if ec else 0)
    rho_c = max(ec, 1) - 127
    terms.append((-mc if c >> 31 else mc, rho_c - 23, rho_c))
    active = [rho for m, _, rho in terms if m]
    if not active:
        return dict(eta=None, acc=Q(0), bits=0)
    eta = max(active + ([] if floor is None else [floor]))
    ell = eta - 23 - p
    integers = []
    for m, scale, _ in terms:
        shift = scale - ell
        magnitude = abs(m) << shift if shift >= 0 else abs(m) >> -shift
        integers.append(-magnitude if m < 0 else magnitude)
    z = sum(integers)
    acc = Q(z << ell) if ell >= 0 else Q(z, 1 << -ell)
    bits = neighbor_round(acc, 'rtz') if abs(acc) <= oracle_value(0x7f7fffff, 'fp32') else None
    return dict(eta=eta, acc=acc, bits=bits)

def vector(profile, av, bv, cv=0):
    fmt,k,_,_ = PROFILES[profile]
    assert len(av) == len(bv) <= k
    a=[encode(Q(x),fmt) for x in av]+[0]*(k-len(av))
    b=[encode(Q(x),fmt) for x in bv]+[0]*(k-len(bv))
    for x,y in zip(av,a): assert value(y,fmt)==x
    for x,y in zip(bv,b): assert value(y,fmt)==x
    c=encode(Q(cv)); assert value(c,'fp32')==cv
    return a,b,c

def check(a,b,c,profile):
    r=model(a,b,c,profile)
    independent=integer_block_oracle(a,b,c,profile)
    assert r['acc']==independent['acc'] and r['bits']==independent['bits']
    assert independent['eta'] is None or r['eta']==independent['eta']
    ideal=ideal_oracle(a,b,c,PROFILES[profile][0])
    fmt=PROFILES[profile][0]
    assert all(value(x,fmt)==oracle_value(x,fmt) for x in a+b)
    assert value(c,'fp32')==oracle_value(c,'fp32')
    assert r['recovered']==ideal
    assert r['d']+r['rout']+sum(r['residuals'])==ideal
    assert r['cr']==neighbor_round(ideal)
    if r['scalar_cr'] is not None:
        assert r['scalar_cr']==neighbor_round(ideal)
    assert abs(ideal-r['d'])<len(r['terms'])*r['qa']+r['qd']
    assert abs(r['rout'])<r['qd']
    assert all(abs(x)<r['qa'] for x in r['residuals'])
    assert sum(trunc(x,r['qa']) for x in r['eps'])-r['rout']==r['eo']
    if grid_predicate(r['eps']):
        for items in [r['eps'],r['eps'][::-1],sorted(r['eps']),sorted(r['eps'],key=abs)]:
            s=Q(0)
            for x in items:
                rounded=value(encode(s+x),'fp32')
                assert rounded==s+x
                s=rounded
    return r

def main():
    named=[]
    def run(name,profile,a,b,c,expected=None):
        r=check(a,b,c,profile)
        if expected is not None: assert r['bits']==expected,(name,hex(r['bits']))
        named.append(dict(name=name,profile=profile,a=[hex(x) for x in a],b=[hex(x) for x in b],
                          c=hex(c),eta=r['eta'],qa=str(r['qa']),D=f'{r["bits"]:08x}',
                          CR=f'{r["cr"]:08x}',exact_sum=str(r['recovered']),
                          alignment_residuals=[str(x) for x in r['residuals']],
                          output_residual=str(r['rout']),overlap_correction=str(r['eo']),
                          scalar_epsilon_predicate=grid_predicate(r['eps'])))
        return r
    a=[0x3e00,0x3c01,0x3c01,0x3c00];b=[0x3e00,0x3001,0x3001,0x3000];c=0x3e000000
    r=run('C1','v100-fp16',a,b,c,0x40300801)
    assert r['recovered']==Q(11536385,4194304) and r['eo']==pow2(-22)
    # Reproduce the old printed scalar formulas, with explicit RTZ.
    rz=lambda x:value(encode(x,mode='rtz'),'fp32')
    old_eps=[rz(t-rz(rz(2+t)-2)) for t in r['terms']]
    old_phi=[rz(rz(x+2)-2) for x in old_eps]
    old_eo=rz(rz(sum(old_phi)+2)-2)
    assert encode(r['d']-old_eo+sum(old_eps))==0x40300802
    assert 24 >= (1-(-3))+2*3
    r=run('B2','v100-fp16',*[ [0x3e00]*4,[0x3d00]*4,0x3f7fffff ])
    assert r['recovered']-r['d']==Q(15,2)*pow2(-23)
    for name,av,bv,expected in [
        ('factorization-raw',[Q(3,2),pow2(-11),pow2(-11)],[Q(3,2),pow2(-12),pow2(-12)],0x40100001),
        ('factorization-normal',[1,pow2(-11),pow2(-11)],[Q(9,4),pow2(-12),pow2(-12)],0x40100000)]:
        run(name,'v100-fp16',*vector('v100-fp16',av,bv),expected)
    # Compatible reconstruction of the manuscript's five printed cancellation terms.
    run('cancellation-reconstruction','v100-fp16',
        [0xd83d,0x5061,0x444c,0x5810],[0x5a03,0x5722,0x49d5,0x5976],0x4416cfe5,0x449fbe50)
    assert named[-1]['CR']=='449fbe62'
    for profile in ['v100-fp16','a100-fp16','h100-fp16']:
        _,k,p,_=PROFILES[profile]
        for before,cv,out in [(True,Q(1),0x3f800000),(False,1-pow2(-24),0x3f800001)]:
            run('monotonicity-'+('before' if before else 'after'),profile,
                *vector(profile,[pow2(-12)]*k,[pow2(-12-p)]*k,cv),out)
    # Enumerate the theorem's threshold and extent in a synthetic fixed-grid family.
    family_count=0
    for p in range(5):
        t=pow2(-24-p)
        for k in range(1,100):
            jumps=[]
            for j in range(1,100):
                d=value(encode(1+(k-j*(1<<p))*t,mode='rtz'),'fp32')
                assert (d>1)==(j <= (k//(1<<p))-2)
                if d>1: jumps.append((j,d-1))
                family_count+=1
            if jumps:
                assert max(x[0] for x in jumps)==k//(1<<p)-2
                assert max(x[1] for x in jumps)==pow2(-23)*((k-(1<<p))//(1<<(p+1)))
    for profile in ['a100-bf16','a100-tf32']:
        run('alignment-floor-retained',profile,*vector(profile,
            [pow2(-75),pow2(-78),pow2(-78)],
            [Q(63,32)*pow2(-75),pow2(-78),pow2(-78)]),1)
        run('alignment-floor-lost',profile,*vector(profile,
            [pow2(-75),pow2(-78),pow2(-78),pow2(-78)],
            [Q(63,32)*pow2(-75),pow2(-78),pow2(-79),pow2(-79)]),0)
    for profile in ['h100-bf16','h100-tf32']:
        run('alignment-floor-retained',profile,*vector(profile,
            [pow2(-75),pow2(-78),pow2(-79),pow2(-79)],
            [Q(127,64)*pow2(-75),pow2(-79),pow2(-79),pow2(-79)]),1)
        run('alignment-floor-lost',profile,*vector(profile,
            [pow2(-75),pow2(-78),pow2(-79),pow2(-79)],
            [Q(127,64)*pow2(-75),Q(3,2)*pow2(-79),pow2(-80),pow2(-80)]),0)
    for profile in ['a100-bf16','a100-tf32','h100-bf16','h100-tf32']:
        shift=1 if profile.startswith('h100') else 0
        run('nonzero-subnormal-c',profile,*vector(profile,
            [pow2(-75),pow2(-75),pow2(-75)],
            [pow2(-75-shift),pow2(-76-shift),pow2(-76-shift)],pow2(-127)),0x00400000)
        run('wide-product-cancellation',profile,*vector(profile,
            [pow2(127),-pow2(127)],[pow2(127),pow2(127)],1),0)
    for profile,(fmt,k,p,floor) in PROFILES.items():
        run('all-zero',profile,[0]*k,[0]*k,0,0)
        run('subnormal-multiplicand',profile,[1]+[0]*(k-1),
            [encode(1,fmt)]+[0]*(k-1),0)
        run('exact-signed-cancellation',profile,*vector(profile,[Q(3,2),Q(-3,2)],[Q(3,2),Q(3,2)]),0)
        run('small-negative-output',profile,*vector(profile,[-pow2(-14)],[pow2(-14)],0))
    # Independent rounding at binade boundaries, ties and the subnormal boundary.
    rounding_count=0
    for low in [0,1,2,0x007ffffe,0x007fffff,0x00800000,0x3f7fffff,0x3f800000,0x3f800001,0x7f7ffffd]:
        x,y=value(low,'fp32'),value(low+1,'fp32')
        for t in [Q(0),Q(1,4),Q(1,2),Q(3,4),Q(1)]:
            for s in [-1,1]:
                exact=s*(x+t*(y-x))
                assert encode(exact)==neighbor_round(exact)
                rounding_count+=1
    # 800 deterministic finite blocks, covering signs, zeros, normal/subnormal inputs.
    rng=random.Random(20260905)
    random_count=0
    for profile,(fmt,k,p,floor) in PROFILES.items():
        eb,fb=FORMATS[fmt];bias=(1<<(eb-1))-1
        for _ in range(100):
            def operand():
                if rng.randrange(10)==0: return rng.randrange(1<<fb)
                e=rng.randrange(-10,11)+bias
                return (rng.randrange(2)<<(eb+fb))|(e<<fb)|rng.randrange(1<<fb)
            a,b=[operand() for _ in range(k)],[operand() for _ in range(k)]
            c=rng.choice([0,rng.randrange(1<<23),encode(Q(rng.randrange(-10000,10001),128))])
            check(a,b,c,profile)
            random_count+=1
    report=dict(model='Accurate Models v4, finite FP32 paths',
        matlab_tag='v0.5',matlab_commit='bbcf00a273868172494eaacaa8d6128ab0fb8704',
        named_regressions=named,random_blocks=random_count,
        synthetic_perturbations=family_count,rounding_cases=rounding_count,
        result='PASS',gpu_measurements=0)
    Path(__file__).with_name('results.json').write_text(json.dumps(report,indent=2)+'\n')
    print(f'PASS: {len(named)} named regressions, {random_count} random blocks, '
          f'{family_count} synthetic perturbations, {rounding_count} rounding cases; no GPU runs.')

if __name__=='__main__':
    main()
