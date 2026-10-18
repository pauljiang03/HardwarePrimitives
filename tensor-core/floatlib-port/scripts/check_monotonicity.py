#!/usr/bin/env python3
"""Boundary regressions for the universally proved nonmonotonicity family."""
if not __debug__:
    raise SystemExit('Run without python -O or PYTHONOPTIMIZE: these checks rely on assert.')
from pathlib import Path
from fractions import Fraction as Q
import json, subprocess
PORT = Path(__file__).resolve().parents[1]
OUT = PORT/'test-results/monotonicity'

def half_power(e):
    assert -24 <= e <= 15
    return (e+15)*1024 if e >= -14 else 1 << (e+24)

def main():
    OUT.mkdir(parents=True,exist_ok=True)
    rows,cases=[],[]
    for p in range(9):
        threshold=3*2**p
        for k in sorted({0,1,2**p-1,2**p,threshold-1,threshold,threshold+1}):
            for floor in ['none',-133,-1]:
                for c in [0x3f800000,0x3f7fffff]:
                    pairs=[half_power(-12),half_power(-12-p)]*k
                    rows.append(' '.join(map(str,['block','fp16',k,p,floor,*pairs,c,0])))
                    cases.append((p,k,floor,c))
    path=OUT/'inputs.txt';path.write_text('\n'.join(rows)+'\n')
    with (OUT/'outputs.jsonl').open('w') as output:
        subprocess.run([str(PORT/'.lake/build/bin/tc_floatlib'),str(path)],cwd=PORT,stdout=output,check=True)
    data=[json.loads(s) for s in (OUT/'outputs.jsonl').read_text().splitlines()]
    assert len(data)==len(cases)
    for (p,k,floor,c),out in zip(cases,data):
        m=out['model']
        expected=Q(1) if c==0x3f800000 else Q(1)-Q(2)**-24+k*Q(2)**(-24-p)
        assert Q(m['accumulator'])==expected,(p,k,floor,c,'alignment')
        assert m['alignExp']==(0 if c==0x3f800000 else -1),(p,k,floor,c,'grid selection')
        if c==0x3f800000:
            assert m['bits']==0x3f800000,(p,k,floor,'base')
        else:
            # All outputs are positive finite, where unsigned encoding order is numerical order.
            assert (m['bits']>0x3f800000)==(k>=3*2**p),(p,k,floor,'threshold',m)
    report={'status':'passed','cases':len(cases),'p':list(range(9)),
            'floors':['none',-133,-1],'mismatches':0,
            'scope':'Boundary regressions; universal theorem is nonmonotone_perturbation/nonmonotone_encoded'}
    (PORT/'test-results/monotonicity-report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
