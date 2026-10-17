import Lean
import MMAlgebraMC
import MMAlgebraMCTests.Examples

/-! # Trust audit

Every theorem of the reduction algebra on the matrix-core model, and of its worked examples, depends
only on Lean's standard axioms `propext`, `Classical.choice` and `Quot.sound`. -/

open Lean Elab Command

namespace MMAlgebraMCTests.Audit

elab "axiom_audit" : command => do
  let env ← getEnv
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let roots := env.constants.fold (init := (#[] : Array Name)) fun acc n ci =>
    if ci.isTheorem && ((`MMAlgebra).isPrefixOf n || (`MMAlgebraMCTests).isPrefixOf n) &&
        !n.isInternal then acc.push n else acc
  for n in roots do
    let deps ← liftCoreM (collectAxioms n)
    unless deps.all allowed.contains do throwError "nonstandard axioms in {n}: {deps}"
  logInfo m!"axiom_audit: {roots.size} theorems, standard axioms only"

axiom_audit

end MMAlgebraMCTests.Audit
