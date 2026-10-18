import Lean
import TensorCoreTests.Specification.NegativeControls

/-! A compiled-dependency audit of the independently defined specification. -/

open Lean Elab Command

namespace TensorCore.IndependentSpec.Audit

def specificationModules : List Name :=
  [`TensorCore.TC.Specification.Defs, `TensorCore.TC.Specification.Variants,
    `TensorCore.TC.Specification.Schedule, `TensorCore.TC.Specification.MmaSyncFP8]

def moduleOf (env : Environment) (n : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? n
  env.header.moduleNames[idx.toNat]?

def standardModule (name : Name) : Bool :=
  name.getRoot == `Init || name.getRoot == `Std || name.getRoot == `Lean

partial def visit (env : Environment) (n : Name) : StateM NameSet Unit := do
  if (← get).contains n then return
  modify (·.insert n)
  -- Standard-library arithmetic/types are the deliberately shared foundation.
  if (moduleOf env n).any standardModule then return
  match env.find? n with
  | none => pure ()
  | some info =>
    info.type.getUsedConstants.forM (visit env)
    match info with
    | .defnInfo d => d.value.getUsedConstants.forM (visit env)
    | .opaqueInfo d => d.value.getUsedConstants.forM (visit env)
    | .thmInfo d => d.value.getUsedConstants.forM (visit env)
    | _ => pure ()

def check (root : Name) : CommandElabM Unit := do
  let env ← getEnv
  let deps := ((visit env root).run {}).2
  let mut bad : Array Name := #[]
  for n in deps do
    if n == root then continue
    match moduleOf env n with
    | some m =>
      unless standardModule m || specificationModules.contains m do bad := bad.push n
    | none => bad := bad.push n
  unless bad.isEmpty do
    throwError "Paper specification has forbidden dependencies: {bad}"

elab "paper_spec_audit" : command => do
  let env ← getEnv
  let roots := env.constants.fold (init := (#[] : Array Name)) fun acc n _ =>
    if (moduleOf env n).any specificationModules.contains then acc.push n else acc
  for n in roots do check n
  logInfo m!"paper_spec_audit: {roots.size} specification declarations; no implementation dependencies"

end TensorCore.IndependentSpec.Audit

paper_spec_audit
