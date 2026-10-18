import TensorCoreTests.Specification.Audit

open Lean Elab Command

/-- Audit every proof in the independent-specification namespace, including generated roots. -/
elab "paper_proof_audit" : command => do
  let env ← getEnv
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let roots := env.constants.fold (init := (#[] : Array Name)) fun acc n ci =>
    if ci.isTheorem && (`TensorCore.IndependentSpec).isPrefixOf n && !n.isInternal then acc.push n else acc
  for n in roots do
    let deps ← liftCoreM (collectAxioms n)
    unless deps.all allowed.contains do throwError "Nonstandard paper-proof dependencies: {n}: {deps}"
  logInfo m!"paper_proof_audit: {roots.size} theorem roots; standard axioms only"

paper_spec_audit
paper_proof_audit
