#!/usr/bin/env python3
"""Build and check the isolated FloatLib port; all generated files stay in this folder."""
if not __debug__:
    raise SystemExit('Run without python -O or PYTHONOPTIMIZE: these checks rely on assert.')
from pathlib import Path
import os, subprocess, sys, json, re, hashlib
PORT=Path(__file__).resolve().parents[1]
OUT=PORT/'test-results'
OUT.mkdir(exist_ok=True)
COMMANDS=[[sys.executable,'scripts/prepare_reference.py'],['lake','build'],['lake','env','lean','tests/Audit.lean'],
          ['lake','env','lean','tests/RepresentationFacts.lean'],
          [sys.executable,'scripts/check_features.py'],
          [sys.executable,'scripts/check_replay.py'],
          [sys.executable,'scripts/check_tc_eft_paper.py'],
          [sys.executable,'scripts/check_edges.py'],
          [sys.executable,'scripts/check_monotonicity.py']]

def main():
    logs=[]
    for i,cmd in enumerate(COMMANDS):
        print('Running: '+' '.join(cmd),flush=True)
        p=subprocess.run(cmd,cwd=PORT,text=True,capture_output=True,env={k:v for k,v in os.environ.items() if k!='PYTHONOPTIMIZE'})
        log=p.stdout+p.stderr
        (OUT/f'check-{i}.log').write_text(log)
        if p.returncode:
            print(log);p.check_returncode()
        if cmd==['lake','build']:
            warnings=re.findall(r'^warning: (.*)$',log,re.M)
            assert all(w.startswith('reference-compat/TensorCore/') and 'has been deprecated:' in w for w in warnings),log
        if cmd==['lake','env','lean','tests/Audit.lean']:
            assert 'floatlib_port_audit:' in log
            assert log.count('checked executable dependencies:')==4
            assert log.count('checked source independence:')==10
            for name in ['round32_rtz_normal', 'nonmonotone_perturbation', 'nonmonotone_encoded', 'construction_not_monotone', 'Equivalence.universal_equivalence',
                         'Equivalence.floatlib_eq_reference', 'Equivalence.floatlib_eq_reference_inverse',
                         'Equivalence.floatlib_error_bound', 'Equivalence.floatlib_nonmonotone_range',
                         'Equivalence.general_flowback_necessary', 'Equivalence.general_flowback_sufficient',
                         'Equivalence.floatlib_scalar_correct_of_inputGrid', 'Equivalence.floatlib_bitSpan_exact',
                         'Equivalence.e4m3x_decodesLikeReference', 'Equivalence.e4m3fn_decode_widen',
                         'Equivalence.fp8_models', 'Equivalence.e4m3_equivalence', 'Equivalence.e5m2_equivalence']:
                assert f"'TCFloat.{name}' depends on axioms:" in log, name
        logs.append({'command':cmd,'exit_code':p.returncode})
    sources=[*sorted((PORT/'TCFloat').rglob('*.lean')),PORT/'Main.lean',PORT/'TCFloat.lean']
    for source in sources:
        s=source.read_text()
        assert not re.search(r'\b(sorry|admit|axiom|native_decide|ofReduceBool|skipKernelTC)\b',s),source
        if 'Equivalence' not in source.parts:
            assert not re.search(r'^import TensorCore',s,re.M),source
    reports={n:json.loads((OUT/n).read_text()) for n in
             ['feature-report.json','replay-report.json','eft-paper-report.json','edges-report.json','monotonicity-report.json']}
    summary={'status':'passed','reference_commit':'9882a52c8f24ee1cce3ab7a840d2735261b51dbc',
             'floatlib_commit':'0d91825727839f597fd06b22fdd038ea21480f0c',
             'lean':'4.34.0','commands':logs,'reports':reports,
             'reference_build':json.loads((PORT/'reference-compat/manifest.json').read_text()),
             'source_sha256':{str(p.relative_to(PORT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sources},
             'verification_sha256':{str(p.relative_to(PORT)):hashlib.sha256(p.read_bytes()).hexdigest()
               for p in [*sorted((PORT/'scripts').glob('*.py')), *sorted((PORT/'tests').glob('*.lean')),
                         PORT/'reference-manifest.json',PORT/'lakefile.toml',PORT/'lake-manifest.json',PORT/'lean-toolchain']}}
    (OUT/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print('All FloatLib-port checks passed. Reports: floatlib-port/test-results/')

if __name__=='__main__':main()
