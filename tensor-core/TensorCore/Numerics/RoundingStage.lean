import TensorCore.Numerics.Binary.RoundOp

/-! Rounding stages and finite encoded results. -/

namespace TensorCore

structure FiniteBinary (f : Format) where
  bits : BitVec f.width
  decoded : Decoded
  valid : (classify f bits).finite = some decoded
  deriving Repr, DecidableEq

def FiniteBinary.value {f : Format} (d : FiniteBinary f) : ℚ := d.decoded.value

def finiteBinary (f : Format) (bits : BitVec f.width) : Option (FiniteBinary f) :=
  match h : (classify f bits).finite with
  | none => none
  | some d => some ⟨bits, d, h⟩

theorem finiteBinary_none {f : Format} {bits : BitVec f.width}
    (hd : (classify f bits).finite = none) : finiteBinary f bits = none := by
  unfold finiteBinary
  split
  · rfl
  · rename_i d h
    rw [hd] at h
    contradiction

theorem finiteBinary_some {f : Format} {bits : BitVec f.width} {d : Decoded}
    (hd : (classify f bits).finite = some d) : finiteBinary f bits = some ⟨bits, d, hd⟩ := by
  unfold finiteBinary
  split
  · rename_i h
    rw [hd] at h
    contradiction
  · rename_i d' h
    rw [hd] at h
    cases Option.some.inj h
    rfl

structure RoundingStage where
  format : Format
  mode : BinaryRoundingMode
  deriving Repr, DecidableEq

def RoundingStage.roundValue (s : RoundingStage) (x : ℚ) : Option (FiniteBinary s.format) := do
  finiteBinary s.format (← roundBinary s.format s.mode x)

structure RoundingEvent where
  stage : RoundingStage
  input : ℚ
  output : FiniteBinary stage.format
  deriving Repr, DecidableEq

def RoundingEvent.loss (e : RoundingEvent) : ℚ := e.input - e.output.value

structure RoundingRun where
  events : List RoundingEvent
  value : ℚ
  deriving Repr, DecidableEq

def RoundingRun.loss (r : RoundingRun) : ℚ := sumQ (r.events.map RoundingEvent.loss)

/-- Each following conversion receives the decoded encoding of its predecessor. -/
def runRoundings : List RoundingStage → ℚ → Option RoundingRun
  | [], x => some ⟨[], x⟩
  | s :: ss, x => do
    let d ← s.roundValue x
    let rest ← runRoundings ss d.value
    return ⟨⟨s, x, d⟩ :: rest.events, rest.value⟩

theorem roundingStage_output {s : RoundingStage} {x : ℚ} {d : FiniteBinary s.format}
    (h : s.roundValue x = some d) : roundBinary s.format s.mode x = some d.bits := by
  unfold RoundingStage.roundValue at h
  cases hr : roundBinary s.format s.mode x with
  | none => simp [hr] at h
  | some bits =>
    simp [hr] at h
    unfold finiteBinary at h
    split at h
    · simp at h
    · simp only [Option.some.injEq] at h
      subst d
      rfl

theorem roundingStage_range {s : RoundingStage} {x : ℚ} {d : FiniteBinary s.format}
    (h : s.roundValue x = some d) : s.format.WellFormed ∧ absQ x ≤ s.format.maxFinite :=
  roundBinary_range (roundingStage_output h)

/-- The input is the final value plus the sum of the stage losses. -/
theorem runRoundings_recovery (ss : List RoundingStage) (x : ℚ) (r : RoundingRun)
    (h : runRoundings ss x = some r) : x = r.value + r.loss := by
  induction ss generalizing x r with
  | nil =>
    simp [runRoundings] at h
    subst r
    simp [RoundingRun.loss, sumQ]
    grind
  | cons s ss ih =>
    cases hd : s.roundValue x with
    | none => simp [runRoundings, hd] at h
    | some d =>
      cases hr : runRoundings ss d.value with
      | none => simp [runRoundings, hd, hr] at h
      | some rest =>
        simp [runRoundings, hd, hr] at h
        subst r
        have hi := ih d.value rest hr
        simp only [RoundingRun.loss, List.map_cons, sumQ, RoundingEvent.loss] at *
        grind

/-- The events follow the stages, and each one is a successful conversion. -/
theorem runRoundings_events (ss : List RoundingStage) (x : ℚ) (r : RoundingRun)
    (h : runRoundings ss x = some r) :
    r.events.map RoundingEvent.stage = ss ∧
      ∀ e ∈ r.events, e.stage.roundValue e.input = some e.output := by
  induction ss generalizing x r with
  | nil => simp [runRoundings] at h; subst r; simp
  | cons s ss ih =>
    cases hd : s.roundValue x with
    | none => simp [runRoundings, hd] at h
    | some d =>
      cases hr : runRoundings ss d.value with
      | none => simp [runRoundings, hd, hr] at h
      | some rest =>
        simp [runRoundings, hd, hr] at h
        subst r
        have hi := ih d.value rest hr
        constructor
        · simpa using hi.1
        · intro e he
          simp only [List.mem_cons] at he
          rcases he with he | he
          · subst e; exact hd
          · exact hi.2 e he

end TensorCore
