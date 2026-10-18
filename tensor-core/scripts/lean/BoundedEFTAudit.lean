import Lean
import TensorCoreTests.EFT.BoundedEFT
import TensorCore.Kernels.EFT.Success
import TensorCoreTests.EFT.NativeEFT

open Lean Elab Command

namespace BoundedEFTAudit

/-- Follow compiled definition bodies transitively, through helper wrappers. -/
partial def visit (env : Environment) (n : Name) : StateM NameSet Unit := do
  if (← get).contains n then return
  modify (·.insert n)
  match env.find? n with
  | some (.defnInfo d) => d.value.getUsedConstants.forM (visit env)
  | some (.opaqueInfo d) => d.value.getUsedConstants.forM (visit env)
  | _ => pure ()

def check (root : Name) : CommandElabM Unit := do
  let deps := ((visit (← getEnv) root).run {}).2
  let forbidden := [``TensorCore.evalBlock, ``TensorCore.evalPrepared,
    ``TensorCore.exactDot, ``TensorCore.PreparedBlock.exactDot, ``TensorCore.round32,
    ``TensorCore.EFMachine.Word.value, ``TensorCore.EFMachine.Word.coefficient,
    ``BitVec.clz, ``BitVec.ctz, ``BitVec.reverse]
  let mut bad : Array Name := #[]
  for n in deps do
    if forbidden.contains n || n.getRoot == `Rat then bad := bad.push n
  unless bad.isEmpty do throwError "Forbidden bounded execution dependencies: {bad}"
  logInfo m!"bounded_execution_audit: {root}; {deps.size} transitive declarations; no Rat/model/ideal"

elab "bounded_eft_audit" : command => do
  for root in [``TensorCore.EFMachine.tcEft, ``TensorCore.EFMachine.prepare,
    ``TensorCore.EFMachine.extract, ``TensorCore.EFMachine.Components.scalarGuard,
    ``TensorCore.EFMachine.Components.scalar, ``TensorCore.EFMachine.Word.round32,
    ``TensorCore.EFMachine.leadingZeros, ``TensorCore.EFMachine.trailingZeros,
    ``TensorCore.EFMachine.tcEftWithLean, ``TensorCore.EFMachine.Components.scalarWithLean,
    ``TensorCore.EFMachine.naiveSum32WithLeanFrom, ``TensorCore.EFMachine.add32WithLean] do check root
  let env ← getEnv
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let roots := env.constants.fold (init := (#[] : Array Name)) fun acc n ci =>
    if ci.isTheorem && ((`TensorCore.EFMachine).isPrefixOf n ||
      (`TensorCore.Regression.BoundedEFT).isPrefixOf n ||
      (`TensorCore.Regression.NativeEFT).isPrefixOf n) && !n.isInternal then acc.push n else acc
  for n in roots do
    let deps ← liftCoreM (collectAxioms n)
    unless deps.all allowed.contains do throwError "Nonstandard bounded proof dependencies: {n}: {deps}"
  logInfo m!"bounded_proof_audit: {roots.size} theorem roots; standard axioms only"

end BoundedEFTAudit

bounded_eft_audit
