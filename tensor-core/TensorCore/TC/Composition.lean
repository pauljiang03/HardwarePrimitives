import TensorCore.TC.StageResiduals

/-! Chained block FMAs and their loss accounting. -/

namespace TensorCore

def foldState (step : σ → α → σ) : σ → List α → σ
  | s, [] => s
  | s, a :: as => foldState step (step s a) as

def foldLoss (step : σ → α → σ) (loss : σ → α → ℚ) : σ → List α → ℚ
  | _, [] => 0
  | s, a :: as => loss s a + foldLoss step loss (step s a) as

theorem fold_residual_ledger
    (value : σ → ℚ) (step : σ → α → σ) (loss : σ → α → ℚ)
    (contribution : α → ℚ)
    (localLaw : ∀ s a, value s + contribution a = value (step s a) + loss s a)
    (s : σ) (as : List α) :
    value s + sumQ (as.map contribution) =
      value (foldState step s as) + foldLoss step loss s as := by
  induction as generalizing s with
  | nil => rfl
  | cons a as ih =>
    simp only [List.map_cons, sumQ, foldState, foldLoss]
    have h := localLaw s a
    have h' := ih (step s a)
    grind

/-- Each later `c` is the decoded encoded output of the previous call. -/
def EncodedChain : Finite32 → List BlockTrace → Prop
  | _, [] => True
  | d, t :: ts => t.block.c = d.decoded ∧ EncodedChain t.output ts

def lastOutput : Finite32 → List BlockTrace → Finite32
  | d, [] => d
  | _, t :: ts => lastOutput t.output ts

/-- Residual ledger of block traces chained through their encoded outputs. -/
theorem encoded_trace_ledger (initial : Finite32) (ts : List BlockTrace)
    (chain : EncodedChain initial ts) :
    initial.value + sumQ (ts.map fun t => t.block.exactProducts) =
      (lastOutput initial ts).value + sumQ (ts.map BlockTrace.residual) := by
  induction ts generalizing initial with
  | nil => rfl
  | cons t ts ih =>
    obtain ⟨hc, ht⟩ := chain
    have h := returned_residual_identity t
    change t.block.c.value + t.block.exactProducts = t.output.value + t.residual at h
    rw [hc] at h
    have h' := ih t.output ht
    simp only [List.map_cons, sumQ, lastOutput]
    change initial.decoded.value + (t.block.exactProducts + _) = _
    change t.output.value + _ = _ at h'
    grind

/-- Runnable schedule under one model. -/
def runBlocks (p : Model) :
    F32 → List (List (p.Word × p.Word)) → Except ModelError (List BlockTrace)
  | _, [] => .ok []
  | c, ps :: rest =>
    match evalBlock (p := p) ⟨ps, c⟩ with
    | .error e => .error e
    | .ok t => match runBlocks p t.output.bits rest with
      | .error e => .error e
      | .ok ts => .ok (t :: ts)

abbrev runV100 := runBlocks v100F16F32

theorem runBlocks_chain (p : Model) (initial : Finite32)
    (ps : List (List (p.Word × p.Word)))
    (ts : List BlockTrace) (h : runBlocks p initial.bits ps = .ok ts) :
    EncodedChain initial ts := by
  induction ps generalizing initial ts with
  | nil => simp [runBlocks] at h; cases h; trivial
  | cons q ps ih =>
    cases he : evalBlock (p := p) ⟨q, initial.bits⟩ with
    | error e => simp [runBlocks, he] at h
    | ok t =>
      cases hr : runBlocks p t.output.bits ps with
      | error e => simp [runBlocks, he, hr] at h
      | ok rest =>
        simp [runBlocks, he, hr] at h
        cases h
        constructor
        · have hc := evalBlock_c he
          change decode32 initial.bits = some t.block.c at hc
          rw [initial.valid] at hc
          exact (Option.some.inj hc).symm
        · exact ih t.output rest hr

/-- Every successful executable schedule inherits the encoded-boundary ledger. -/
theorem runBlocks_residual_ledger (p : Model) (initial : Finite32)
    (ps : List (List (p.Word × p.Word))) (ts : List BlockTrace)
    (h : runBlocks p initial.bits ps = .ok ts) :
    initial.value + sumQ (ts.map fun t => t.block.exactProducts) =
      (lastOutput initial ts).value + sumQ (ts.map BlockTrace.residual) :=
  encoded_trace_ledger initial ts (runBlocks_chain p initial ps ts h)

end TensorCore
