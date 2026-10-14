#!/usr/bin/env python3
"""Compare first-principles and FloatLib outputs on identical encoded inputs."""
if not __debug__:
    raise SystemExit('Run without python -O or PYTHONOPTIMIZE: these checks rely on assert.')
from pathlib import Path
import argparse, hashlib, itertools, json, random, shutil, subprocess
PORT = Path(__file__).resolve().parents[1]
ROOT = PORT.parent
OUT = PORT/'test-results/equivalence'
SOURCE = PORT/'test-results/reference-source'
REV = '9882a52c8f24ee1cce3ab7a840d2735261b51dbc'

def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()

def build_reference():
    SOURCE.mkdir(parents=True,exist_ok=True)
    # Copy the current implementation, preserving caches but removing stale source modules.
    for name in ['TensorCore', 'Main', 'tests']:
        dest = SOURCE/name
        if dest.exists(): shutil.rmtree(dest)
        shutil.copytree(ROOT/name, dest)
    for source in [*ROOT.glob('*.lean'), ROOT/'lakefile.toml', ROOT/'lake-manifest.json', ROOT/'lean-toolchain']:
        shutil.copy2(source, SOURCE/source.name)
    p=subprocess.run(['lake','build','tc_eft_reference'],cwd=SOURCE,text=True,capture_output=True)
    (OUT/'reference-build.log').write_text(p.stdout+p.stderr)
    p.check_returncode()
    shutil.copyfile(PORT/'tests/DecodeOriginal.lean',SOURCE/'DecodeOriginal.lean')

def compare_outputs(a,b,inputs):
    count=0
    with a.open() as aa,b.open() as bb,inputs.open() as ii:
        for i,(x,y,row) in enumerate(itertools.zip_longest(aa,bb,ii),1):
            assert x is not None and y is not None and row is not None,('length',i)
            left,right=json.loads(x),json.loads(y)
            assert left==right,('mismatch',i,row.strip(),left,right)
            count+=1
    return count

def execute_pair(name,rows,decode=False):
    inp=OUT/(name+'.txt'); inp.write_text('\n'.join(rows)+'\n')
    a,b=OUT/(name+'-original.jsonl'),OUT/(name+'-floatlib.jsonl')
    if decode:
        original=['lake','env','lean','--run','DecodeOriginal.lean',str(inp)]
        port=['lake','env','lean','--run','tests/DecodeFloatLib.lean',str(inp)]
    else:
        original=[str(SOURCE/'.lake/build/bin/tc_eft_reference'),str(inp)]
        port=[str(PORT/'.lake/build/bin/tc_floatlib'),str(inp)]
    for cmd,cwd,target in [(original,SOURCE,a),(port,PORT,b)]:
        with target.open('w') as f:
            subprocess.run(cmd,cwd=cwd,stdout=f,check=True)
    count=compare_outputs(a,b,inp)
    print(f'{name}: {count} exact record comparisons passed',flush=True)
    return dict(cases=count,mismatches=0,input_sha256=sha(inp),
                original_output_sha256=sha(a),floatlib_output_sha256=sha(b))

def block_rows():
    for row in (PORT/'test-results/eft-paper/inputs.txt').read_text().splitlines():yield row
    for row in (PORT/'test-results/scalar-coverage.txt').read_text().splitlines():yield row
    # Feature fixtures converted to the shared packed-word EFT interface. supplied D is intentional: correction must also work independently of model D.
    paths=[*sorted((PORT/'test-results/validation').glob('*.txt')),
           *[PORT/f'test-results/{gpu}-{fmt}.txt' for gpu in ['A100','H100'] for fmt in ['bf16','tf32']]]
    for path in paths:
        for row in path.read_text().splitlines():
            fmt,k,extra,floor,*ws=row.split(); k=int(k)
            if len(ws)!=2*k+1:continue  # shared paper CLI rejects malformed shape at parsing
            if fmt=='canonical':fmt='fp16'
            if fmt=='tf32':ws=[str(int(w)//8192) for w in ws[:-1]]+[ws[-1]]
            yield ' '.join(['block',fmt,str(k),extra,floor,*ws,'0'])
    rng=random.Random(20260923)
    for _ in range(2000):
        fmt,width=rng.choice([('fp16',16),('bf16',16),('tf32',19)])
        k=rng.choice([0,1,3,4,8,16,31])
        extra=rng.choice([0,1,2,5,24,104,253])
        floor=rng.choice(['none','-149','-133','-132','0','127'])
        words=[rng.randrange(2**width) for _ in range(2*k)]
        c=rng.randrange(2**32)
        d=rng.choice([0,0x80000000,0x7f7fffff,0xff7fffff,rng.randrange(2**32)])
        yield ' '.join(map(str,['block',fmt,k,extra,floor,*words,c,d]))
    for _ in range(2000):
        n=rng.randrange(-2**80,2**80)
        d=rng.randrange(1,2**60)
        e=rng.randrange(-300,301)
        if e>=0:n*=2**e
        else:d*=2**(-e)
        yield f'round {n} {d}'

def decode_rows():
    for fmt,width in [('fp16',16),('bf16',16),('tf32',19)]:
        for n in range(2**width):yield f'{fmt} {n}'
    for sign in [0,1]:
        for e in range(256):
            for f in [0,1,2,2**22-1,2**22,2**23-2,2**23-1]:
                yield f'fp32 {(sign<<31)|(e<<23)|f}'
    rng=random.Random(20260923)
    for _ in range(10000):yield f'fp32 {rng.randrange(2**32)}'

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--skip-decode',action='store_true')
    args=parser.parse_args()
    OUT.mkdir(parents=True,exist_ok=True)
    assert (PORT/'test-results/eft-paper/inputs.txt').exists(),'Run scripts/check_all.py first'
    build_reference()
    result={'reference_base_commit':REV,
            'reference_source_sha256':{str(p.relative_to(SOURCE)):sha(p) for p in sorted(SOURCE.rglob('*.lean')) if '.lake' not in p.parts},'scope':'Differential tests; not a universal equivalence theorem',
            'observations':execute_pair('observations',list(block_rows()))}
    if not args.skip_decode: result['decoding']=execute_pair('decoding',list(decode_rows()),True)
    # Verify the equality comparator rejects a one-bit mutation.
    probe=OUT/'negative-control.jsonl';probe.write_text('{"bits": 1}\n')
    good=OUT/'negative-control-good.jsonl';good.write_text('{"bits": 0}\n')
    inp=OUT/'negative-control.txt';inp.write_text('test\n')
    try:compare_outputs(good,probe,inp)
    except AssertionError:result['comparator_negative_control']='passed'
    else:raise AssertionError('Comparator accepted mutated output')
    result['status']='passed'
    (OUT/'report.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
