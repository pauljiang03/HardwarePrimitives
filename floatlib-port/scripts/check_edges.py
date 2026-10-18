#!/usr/bin/env python3
"""Supplied-D independence, signed underflow, TF32 register-padding validation and negative controls."""
if not __debug__:
    raise SystemExit('Run without python -O or PYTHONOPTIMIZE: these checks rely on assert.')
import json, os, shutil, sys, subprocess, tempfile
from pathlib import Path
from fractions import Fraction as Q
PORT=Path(__file__).resolve().parents[1]
sys.dont_write_bytecode=True
sys.path.insert(0,str(PORT.parent/'vendor/tc-eft-validation'))
import exact_model as ref
import check_revision as oracle
from check_replay import run

def check_reference_preparation():
    reference=json.loads((PORT/'reference-compat/manifest.json').read_text())
    checks={}
    with tempfile.TemporaryDirectory(prefix='tc-reference-archive-') as directory:
        root=Path(directory)
        port=root/'floatlib-port'
        (port/'scripts').mkdir(parents=True)
        shutil.copy2(PORT/'scripts/prepare_reference.py',port/'scripts/prepare_reference.py')
        shutil.copy2(PORT/'reference-manifest.json',port/'reference-manifest.json')
        shutil.copy2(PORT/'renamed-identifiers.json',port/'renamed-identifiers.json')
        shutil.copytree(PORT/'TCFloat/Equivalence',port/'TCFloat/Equivalence')
        for name in reference['source_sha256']:
            target=root/name
            target.parent.mkdir(parents=True,exist_ok=True)
            shutil.copy2(PORT.parent/name,target)
        environment={**os.environ,'PATH':str(root/'no-external-commands')}

        def prepare(label,error=None):
            proc=subprocess.run([sys.executable,str(port/'scripts/prepare_reference.py')],
                                cwd=port,env=environment,capture_output=True,text=True)
            if error is None:
                assert proc.returncode==0,(label,proc.stdout,proc.stderr)
            else:
                assert proc.returncode and error in proc.stderr,(label,proc.stdout,proc.stderr)
            checks[label]='passed'

        prepare('archive_without_git')
        generated=port/'reference-compat/manifest.json'
        assert json.loads(generated.read_text())==reference
        for name in reference['source_sha256']:
            assert (port/'reference-compat'/name).read_bytes()==(PORT/'reference-compat'/name).read_bytes(),name
        block=root/'TensorCore/TC/Block.lean'
        original=block.read_text()
        expression='b.alignExp.getD 0 - b.model.alignMantissaBits'
        assert original.count(expression)==1
        block.write_text('-- Archive regression\n'+original.replace(expression,expression.replace(' - ','   -   ')))
        prepare('comments_and_whitespace')
        block.write_text(original.replace(expression,expression.replace(' - ',' + ')))
        prepare('arithmetic_mutation','Original arithmetic/proof source differs')
        block.write_text(original)
        notation=root/'TensorCore/Numerics/Notation.lean'
        text=notation.read_text()
        assert 'notation "ℕ"' in text
        notation.write_text(text.replace('notation "ℕ"','notation " ℕ"'))
        prepare('string_literal_mutation','Original arithmetic/proof source differs')
        notation.write_text(text)
        block.write_text('import Std.Data.HashMap\n'+original)
        prepare('added_import','Original imports are not a subset')
        block.write_text(original)
        manifest=port/'reference-manifest.json'
        data=manifest.read_bytes()
        manifest.write_bytes(data+b'\n')
        prepare('manifest_mutation','Pinned reference manifest checksum mismatch')
        manifest.write_bytes(data)
        (port/'TCFloat/Equivalence/Unpinned.lean').write_text('import TensorCore.Numerics.Unpinned\n')
        prepare('unpinned_dependency','Unpinned original dependency')
    return checks

def main():
    # Exact 1 + 2^-24 is a midpoint: RNE gives 1 for every supplied D.
    values=[0,0x80000000,1,0x80000001,0x3f000000,0x3f800000,0xbf800000,0x7f7fffff,0xff7fffff]
    rows=[f'block fp16 1 0 none 3072 3072 1065353216 {d}' for d in values]
    results=run(rows,'supplied-D')
    for d,r in zip(values,results):
        assert Q(r['ideal'])==1+Q(2)**-24
        assert r['correction']['bits']==0x3f800000,(d,r)
    # Exact zero rounds to +0; negative underflow keeps its sign.
    xs=[Q(0),-Q(2)**-151,Q(2)**-150,-Q(2)**-150,
        ref.MAX32, -ref.MAX32,ref.MAX32+1,-ref.MAX32-1]
    results=run([f'round {x.numerator} {x.denominator}' for x in xs],'round-edges')
    for x,r in zip(xs,results):
        for key,mode in [('rne','rne'),('trunc','rtz')]:
            want=oracle.neighbor_round(x,mode) if abs(x)<=ref.MAX32 else None
            assert r[key]==want,(x,key,r,want)
    # Supplied nonfinite D and nonfinite inputs are rejected before the zero shortcut.
    rows=['block fp16 0 0 none 0 2139095040',
          'block fp16 1 0 none 31744 0 0 0',
          'tf32 1 1 -132 1065353217 1065353216 0']
    out=run(rows,'domain-edges')
    assert out[0]['correction']['error'].endswith('nonfiniteOutput')
    assert out[1]['model']['error'].endswith('nonfiniteInput')
    assert out[2]['error'].endswith('nonfiniteInput')
    # Negative controls for the dependency audits.
    audit=(PORT/'tests/Audit.lean').read_text()
    bad=PORT/'test-results/dependency-negative.lean'
    bad.write_text(audit+'\ndef contaminated := TCFloat.evalWords\nrun_cmd checkDependencies ``contaminated\n')
    proc=subprocess.run(['lake','env','lean',str(bad)],cwd=PORT,capture_output=True,text=True)
    assert proc.returncode and 'Forbidden executable dependencies' in proc.stdout+proc.stderr
    bad_source=PORT/'test-results/source-dependency-negative.lean'
    bad_source.write_text(audit+'\ndef contaminatedSource := TensorCore.round32\nrun_cmd checkSourceIndependence ``contaminatedSource\n')
    proc=subprocess.run(['lake','env','lean',str(bad_source)],cwd=PORT,capture_output=True,text=True)
    assert proc.returncode and 'Original implementation in executable dependencies' in proc.stdout+proc.stderr
    report={'supplied_D_cases':len(values),'rounding_cases':len(xs),'domain_cases':len(rows),
            'dependency_negative_control':'passed','source_independence_negative_control':'passed',
            'reference_preparation':check_reference_preparation(),'mismatches':0}
    (PORT/'test-results/edges-report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
