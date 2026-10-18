import Lean
import MatrixCore

/-! # Trust audit

Every library theorem uses only the standard axioms, and the specification depends only on the
standard library and the notation module. -/

open Lean Elab Command

namespace MatrixCoreTests.Audit

def moduleOf (env : Environment) (n : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? n
  env.header.moduleNames[idx.toNat]?

def standardModule (m : Name) : Bool :=
  m.getRoot == `Init || m.getRoot == `Std || m.getRoot == `Lean

/-- Modules the specification may depend on. -/
def specAllowed (m : Name) : Bool :=
  standardModule m || m == `MatrixCore.Numerics.Notation || m == `MatrixCore.Specification.Defs

/-- Constants reachable from `n` through types and bodies, stopping at the standard library. -/
partial def reach (env : Environment) (n : Name) : StateM NameSet Unit := do
  if (← get).contains n then return
  modify (·.insert n)
  if (moduleOf env n).any standardModule then return
  match env.find? n with
  | none => pure ()
  | some info =>
    info.type.getUsedConstants.forM (reach env)
    match info with
    | .defnInfo d => d.value.getUsedConstants.forM (reach env)
    | .opaqueInfo d => d.value.getUsedConstants.forM (reach env)
    | .thmInfo d => d.value.getUsedConstants.forM (reach env)
    | _ => pure ()

/-- Constants reachable from `root` outside the specification's allowed modules. -/
def forbidden (env : Environment) (root : Name) : Array Name := Id.run do
  let deps := ((reach env root).run {}).2
  let mut bad := #[]
  for n in deps do
    if n == root then continue
    match moduleOf env n with
    | some m => unless specAllowed m do bad := bad.push n
    | none => bad := bad.push n
  return bad

elab "spec_independence_audit" : command => do
  let env ← getEnv
  let roots := env.constants.fold (init := (#[] : Array Name)) fun acc n _ =>
    if (moduleOf env n) == some `MatrixCore.Specification.Defs then acc.push n else acc
  for n in roots do
    let bad := forbidden env n
    unless bad.isEmpty do throwError "specification declaration {n} depends on {bad}"
  logInfo m!"spec_independence_audit: {roots.size} specification declarations, \
    standard library and notation only"

elab "axiom_audit" : command => do
  let env ← getEnv
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let roots := env.constants.fold (init := (#[] : Array Name)) fun acc n ci =>
    if ci.isTheorem && (`MatrixCore).isPrefixOf n && !n.isInternal then acc.push n else acc
  for n in roots do
    let deps ← liftCoreM (collectAxioms n)
    unless deps.all allowed.contains do throwError "nonstandard axioms in {n}: {deps}"
  logInfo m!"axiom_audit: {roots.size} theorems, standard axioms only"

/-- Negative control: a declaration that uses the implementation must be reported. -/
def badSpec : ℚ := MatrixCore.pow2 3

elab "negative_control" : command => do
  let bad := forbidden (← getEnv) ``badSpec
  if bad.isEmpty then throwError "negative control: the audit missed an implementation dependency"
  logInfo m!"negative_control: detected {bad.size} implementation dependencies"

end MatrixCoreTests.Audit

spec_independence_audit
axiom_audit
negative_control
