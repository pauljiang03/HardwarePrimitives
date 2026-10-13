#!/usr/bin/env python3
"""Build the independent paper specification, universal proofs, and negative controls."""
if not __debug__:
    raise SystemExit('Run without python -O or PYTHONOPTIMIZE: these checks rely on assert.')
from pathlib import Path
import hashlib
import json
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def run(args, source=None):
    return subprocess.run(args, cwd=ROOT, input=source, text=True, capture_output=True)


def main():
    build = run(['lake', 'build', 'TensorCoreTests.Specification.Audit'])
    if build.returncode:
        raise RuntimeError(build.stdout + build.stderr)
    audit = run(['lake', 'env', 'lean', 'scripts/lean/IndependentSpecAudit.lean'])
    if audit.returncode:
        raise RuntimeError(audit.stdout + audit.stderr)
    declarations = re.search(r'paper_spec_audit: (\d+) specification declarations', audit.stdout)
    roots = re.search(r'paper_proof_audit: (\d+) theorem roots', audit.stdout)
    assert declarations and roots, audit.stdout
    contaminated = '''import TensorCoreTests.Specification.Audit
def hiddenImplementationCall (x : Rat) := TensorCore.round32 .truncate x
def contaminatedProposition (x : Rat) (b : BitVec 32) : Prop :=
  hiddenImplementationCall x = some b
run_cmd TensorCore.IndependentSpec.Audit.check ``contaminatedProposition
'''
    negative = run(['lake', 'env', 'lean', '--stdin'], contaminated)
    failure = negative.stdout + negative.stderr
    assert negative.returncode != 0, 'Contaminated specification was accepted'
    assert 'Paper specification has forbidden dependencies' in failure, failure
    assert 'TensorCore.round32' in failure, failure
    contaminated_scalar = """import TensorCoreTests.Specification.Audit
def hiddenScalarStage := TensorCore.RoundingStage.roundValue
def contaminatedScalar := hiddenScalarStage
run_cmd TensorCore.IndependentSpec.Audit.check ``contaminatedScalar
"""
    negative_scalar = run(['lake', 'env', 'lean', '--stdin'], contaminated_scalar)
    failure_scalar = negative_scalar.stdout + negative_scalar.stderr
    assert negative_scalar.returncode != 0, 'Implementation-dependent scalar stage was accepted'
    assert 'Paper specification has forbidden dependencies' in failure_scalar, failure_scalar
    assert 'TensorCore.RoundingStage.roundValue' in failure_scalar, failure_scalar
    sources = (sorted((ROOT / 'TensorCore/TC/Specification').glob('*.lean')) +
               sorted((ROOT / 'tests/TensorCoreTests/Specification').glob('*.lean')) +
               [ROOT / 'scripts/lean/IndependentSpecAudit.lean', ROOT / 'examples/IndependentSpecification.lean',
                Path(__file__)])
    for source in sources:
        if source.suffix != '.lean':
            continue
        assert not re.search(r'\b(sorry|admit|axiom|native_decide|ofReduceBool|skipKernelTC)\b',
                             source.read_text()), source
    report = dict(
        status='passed',
        theorem='TensorCore.IndependentSpec.supported_eq_spec',
        generic_theorem='TensorCore.IndependentSpec.evalBlock_eq_spec',
        supported_paths=8,
        scope='FP16/BF16/packed-TF32 inputs; FP32 c/output; finite reference domain; one block FMA and ordered lists of block FMAs',
        all_encoded_inputs_including_rejections=True,
        independent_validity_success_proved=True,
        signed_zero_bit_uniqueness_proved=True,
        padded_tf32_register_bridge=True,
        adequate_machine_accumulator_bridge=True,
        all_intermediate_schedule_bits_proved=True,
        scalar_dependency_negative_control_rejected=True,
        specification_declarations_audited=int(declarations.group(1)),
        theorem_roots_audited=int(roots.group(1)),
        dependency_negative_control_rejected=True,
        semantic_negative_controls=['premature_product_normalization', 'per_term_ieee_rtz_alignment',
                                    'ampere_bf16_eAlignMin_removal', 'hopper_bf16_eAlignMin_removal', 'block_reversal'],
        boundary_controls=['negative_underflow_signed_zero', 'all_zero_plus_zero', 'nonfinite_rejection'],
        axioms_allowed=['propext', 'Classical.choice', 'Quot.sound'],
        source_sha256={str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sources},
        limitations=['Paper-to-formula correspondence remains a human review obligation',
                     'Specification output selection is mathematical/noncomputable',
                     'No physical GPU conformance or full encoded hardware pipeline theorem',
                     'No FP16-output stage-order resolution or independent FP8 path',
                     'Rejections agree as none; implementation-specific error tags are not part of the independent specification'],
    )
    (ROOT / 'data/regressions/independent-spec-report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
