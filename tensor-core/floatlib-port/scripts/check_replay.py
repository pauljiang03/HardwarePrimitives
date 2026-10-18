#!/usr/bin/env python3
"""Replay all recorded BF16/TF32 hardware rows and the source scalar-guard corpus."""
if not __debug__:
    raise SystemExit('Run without python -O or PYTHONOPTIMIZE: these checks rely on assert.')
from pathlib import Path
from fractions import Fraction as Q
import sys, json, subprocess, hashlib
PORT = Path(__file__).resolve().parents[1]
ROOT = PORT.parent
sys.dont_write_bytecode = True
sys.path.insert(0, str(ROOT / 'scripts'))
from check_device import read_hex_rows, read_bin
OUT = PORT / 'test-results'
OUT.mkdir(exist_ok=True)

def run(rows, name):
    p = OUT / (name + '.txt')
    p.write_text('\n'.join(rows)+'\n')
    r = subprocess.run([str(PORT/'.lake/build/bin/tc_floatlib'), str(p)], check=True, capture_output=True, text=True)
    data = [json.loads(x) for x in r.stdout.splitlines()]
    assert len(data) == len(rows)
    (OUT/(name+'.jsonl')).write_text(r.stdout)
    return data

def hardware():
    reports = {}
    pins = json.loads((ROOT/'vendor/SOURCES.json').read_text())
    for name, h in pins['sha256'].items():
        assert hashlib.sha256((ROOT/'vendor/matlab-tensor-core-v0.5'/name).read_bytes()).hexdigest() == h
    for gpu,fmt,k,e,floor in [('A100','bf16',8,1,-132),('H100','bf16',16,2,-133),
                              ('A100','tf32',4,1,-132),('H100','tf32',4,2,-133)]:
        base=ROOT/'vendor/matlab-tensor-core-v0.5/model_validation'/gpu/fmt
        aa=read_hex_rows(base/f'a_{gpu}_{fmt}.txt'); bb=read_hex_rows(base/f'b_{gpu}_{fmt}.txt')
        cc=read_bin(base/f'c_{gpu}_fp32.txt'); dd=read_bin(base/f'd_{gpu}_fp32.txt')
        assert len(aa)==len(bb)==len(cc)==len(dd)==5000
        rows=[]
        for a,b,c in zip(aa,bb,cc):
            assert len(a)==len(b)==k
            words=[w for pair in zip(a,b) for w in pair]
            if fmt=='bf16':
                assert all(w%2**16==0 for w in words)
                words=[w>>16 for w in words]
            else:
                assert all(w%2**13==0 for w in words)
            rows.append(' '.join(map(str,[fmt,k,e,floor,*words,c])))
        results=run(rows, f'{gpu}-{fmt}')
        for i,(r,d) in enumerate(zip(results,dd)):
            assert r.get('bits')==d,(gpu,fmt,i,r,d)
        reports[f'{gpu}-{fmt}']={'rows':len(rows),'mismatches':0}
    return reports

def coverage():
    path=ROOT/'data/regressions/eft-coverage-cases.json'
    cases=json.loads(path.read_text())
    rows=[]
    for c in cases:
        ws=[int(w,16) for w in c['words']]
        floor='none'  # source check_eft_coverage.py deliberately uses no minimum alignment exponent
        rows.append(' '.join(map(str,['block','fp16',c['k'],c['extra'],floor,*ws,c.get('bits',0)])))
    outputs=run(rows,'scalar-coverage')
    counts={True:0,False:0}
    for i,(c,r) in enumerate(zip(cases,outputs)):
        m=r['model']
        if 'error' in c:
            assert m.get('error')==c['error'],(i,m,c)
            continue
        counts[c['accepted']]+=1
        assert m['bits']==c['bits'],(i,'TC bits')
        assert m['scalar_predicate']==c['accepted'],(i,'guard')
        assert m['scalar_bits']==c['tceft'],(i,'scalar bits')
        assert list(map(Q,m['low_parts']))==list(map(Q,c['low_parts'])),(i,'low parts')
        assert m['algorithm_bits']==c['oracle'],(i,'full EFT')
        assert r['correction']['bits']==c['oracle'],(i,'supplied D')
    return {'cases':len(cases),'accepted':counts[True],'rejected':counts[False],
            'mismatches':0,'source_sha256':hashlib.sha256(path.read_bytes()).hexdigest()}

if __name__=='__main__':
    report={'hardware':hardware(),'scalar':coverage(),'new_gpu_measurements':False}
    (OUT/'replay-report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
