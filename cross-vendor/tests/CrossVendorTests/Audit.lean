import Lean
import CrossVendor

/-! # Trust audit

Every `CrossVendor` theorem uses only the standard axioms. Both libraries are imported here, and
each one's `ℕ`/`ℤ`/`ℚ` notation works when its namespace is opened. -/

open Lean Elab Command

namespace CrossVendorTests.Audit

elab "axiom_audit" : command => do
  let env ← getEnv
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let roots := env.constants.fold (init := (#[] : Array Name)) fun acc n ci =>
    if ci.isTheorem && (`CrossVendor).isPrefixOf n && !n.isInternal then acc.push n else acc
  for n in roots do
    let deps ← liftCoreM (collectAxioms n)
    unless deps.all allowed.contains do throwError "nonstandard axioms in {n}: {deps}"
  logInfo m!"axiom_audit: {roots.size} theorems, standard axioms only"

end CrossVendorTests.Audit

axiom_audit

section
open scoped TensorCore
example : TensorCore.pow2 (-1) = (1 : ℚ) / 2 := by decide +kernel
end

section
open scoped MatrixCore
example : MatrixCore.pow2 (-1) = (1 : ℚ) / 2 := by decide +kernel
end
