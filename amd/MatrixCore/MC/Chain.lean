import MatrixCore.MC.Composition
import MatrixCore.MC.AcceptedDomain
import MatrixCore.MC.Prepared
import MatrixCore.MC.SpecialAgreement

/-! # Chained blocks

An inner product runs `⌈k / N_FMA⌉` blocks, each block's `d` being the next block's `c`.
`runBlocks` keeps every block's trace, and `dotBits` is its last output
(`dotBits_eq_runBlocks`). Results about one block carry over to a whole run:

* every trace of a run is an accepted block (`runBlocks_mem`, `runBlocks_all`), so any
  block-level theorem applies to each block;
* consecutive blocks are linked through the binary32 word passed between them (`Chain`);
* a per-block identity telescopes over the run (`fold_residual_ledger`); in particular the exact
  products and the initial `c` equal the final output plus the sum of the blocks' residuals
  (`runBlocks_residual_ledger`, `dotBits_residual_ledger`). -/

namespace MatrixCore

/-! ## Runs of blocks -/

/-- Evaluate blocks from `c`, each block's `d` being the next block's `c`, and keep every trace. -/
def runBlocks (P : Model) :
    F32 → List (List P.a.Word × List P.b.Word) → Except ModelError (List (BlockTrace P))
  | _, [] => .ok []
  | c, ab :: rest =>
    match evalBlock (P := P) ⟨ab.1, ab.2, c⟩ with
    | .error e => .error e
    | .ok t =>
      match runBlocks P t.d rest with
      | .error e => .error e
      | .ok ts => .ok (t :: ts)

/-- The output of a run: the last block's `d`, or `c` when there are no blocks. -/
def lastOutput : F32 → List (BlockTrace P) → F32
  | d, [] => d
  | _, t :: ts => lastOutput t.d ts

/-- Consecutive blocks are linked: each block's `c` is the decoding of the word before it (the
initial `c`, then the previous block's `d`). -/
def Chain : F32 → List (BlockTrace P) → Prop
  | _, [] => True
  | c, t :: ts => (fp32.decode c).toFinite = some t.prepared.c ∧ Chain t.d ts

theorem foldlM_blockBits (P : Model) (bs : List (List P.a.Word × List P.b.Word)) (c : F32) :
    bs.foldlM (fun c ab => blockBits (P := P) ⟨ab.1, ab.2, c⟩) c =
      (runBlocks P c bs).map (lastOutput c) := by
  induction bs generalizing c with
  | nil => rfl
  | cons ab rest ih =>
    rw [List.foldlM_cons]
    simp only [runBlocks]
    unfold blockBits
    cases he : evalBlock (P := P) ⟨ab.1, ab.2, c⟩ with
    | error e => rfl
    | ok t =>
      dsimp only
      show (rest.foldlM (fun c ab => blockBits (P := P) ⟨ab.1, ab.2, c⟩) t.d) = _
      rw [ih]
      cases runBlocks P t.d rest <;> rfl

/-- An inner product is the last output of its run of blocks. -/
theorem dotBits_eq_runBlocks (P : Model) {a : List P.a.Word} {b : List P.b.Word} (c : F32)
    (h : a.length = b.length) :
    dotBits P a b c = (runBlocks P c (blocks P a b)).map (lastOutput c) := by
  unfold dotBits
  rw [if_neg (by omega)]
  exact foldlM_blockBits P _ c

theorem dotBits_ok_iff (P : Model) {a : List P.a.Word} {b : List P.b.Word} (c d : F32)
    (h : a.length = b.length) :
    dotBits P a b c = .ok d ↔
      ∃ ts, runBlocks P c (blocks P a b) = .ok ts ∧ lastOutput c ts = d := by
  rw [dotBits_eq_runBlocks P c h]
  cases runBlocks P c (blocks P a b) with
  | error e => simp [Except.map]
  | ok ts => simp [Except.map]

theorem runBlocks_cons {P : Model} {c : F32} {ab : List P.a.Word × List P.b.Word}
    {rest : List (List P.a.Word × List P.b.Word)} {ts : List (BlockTrace P)}
    (h : runBlocks P c (ab :: rest) = .ok ts) :
    ∃ t ts', evalBlock (P := P) ⟨ab.1, ab.2, c⟩ = .ok t ∧ runBlocks P t.d rest = .ok ts' ∧
      ts = t :: ts' := by
  simp only [runBlocks] at h
  cases he : evalBlock (P := P) ⟨ab.1, ab.2, c⟩ with
  | error e => rw [he] at h; simp at h
  | ok t =>
    rw [he] at h
    dsimp only at h
    cases hr : runBlocks P t.d rest with
    | error e => rw [hr] at h; simp at h
    | ok ts' =>
      rw [hr] at h
      simp only [Except.ok.injEq] at h
      exact ⟨t, ts', rfl, hr, h.symm⟩

theorem runBlocks_length {P : Model} {c : F32} {bs : List (List P.a.Word × List P.b.Word)}
    {ts : List (BlockTrace P)} (h : runBlocks P c bs = .ok ts) : ts.length = bs.length := by
  induction bs generalizing c ts with
  | nil => simp [runBlocks] at h; subst h; rfl
  | cons ab rest ih =>
    obtain ⟨t, ts', _, hr, rfl⟩ := runBlocks_cons h
    simp [ih hr]

/-- Every block of a run is an accepted block. -/
theorem runBlocks_mem {P : Model} {c : F32} {bs : List (List P.a.Word × List P.b.Word)}
    {ts : List (BlockTrace P)} (h : runBlocks P c bs = .ok ts) :
    ∀ t ∈ ts, ∃ x : BlockInput P, evalBlock x = .ok t := by
  induction bs generalizing c ts with
  | nil => simp [runBlocks] at h; subst h; simp
  | cons ab rest ih =>
    obtain ⟨t, ts', he, hr, rfl⟩ := runBlocks_cons h
    intro u hu
    rcases List.mem_cons.mp hu with rfl | hu
    · exact ⟨_, he⟩
    · exact ih hr u hu

/-- **Lifting.** Any property that every accepted block has holds for every block of a run. -/
theorem runBlocks_all {P : Model} {Q : BlockInput P → BlockTrace P → Prop}
    (hQ : ∀ x t, evalBlock x = .ok t → Q x t) {c : F32}
    {bs : List (List P.a.Word × List P.b.Word)} {ts : List (BlockTrace P)}
    (h : runBlocks P c bs = .ok ts) : ∀ t ∈ ts, ∃ x, Q x t := by
  intro t ht
  obtain ⟨x, hx⟩ := runBlocks_mem h t ht
  exact ⟨x, hQ x t hx⟩

theorem evalBlock_c {P : Model} {x : BlockInput P} {t : BlockTrace P} (h : evalBlock x = .ok t) :
    (fp32.decode x.c).toFinite = some t.prepared.c :=
  prepare_c (evalBlock_ok h).2.2.1

/-- A run is linked through the words it passes on. -/
theorem runBlocks_chain {P : Model} {c : F32} {bs : List (List P.a.Word × List P.b.Word)}
    {ts : List (BlockTrace P)} (h : runBlocks P c bs = .ok ts) : Chain c ts := by
  induction bs generalizing c ts with
  | nil => simp [runBlocks] at h; subst h; trivial
  | cons ab rest ih =>
    obtain ⟨t, ts', he, hr, rfl⟩ := runBlocks_cons h
    exact ⟨evalBlock_c he, ih hr⟩

/-! ## Finite observations -/

theorem decode_infinity32 (s : Bool) : fp32.decode (infinity32 s) = .infinity s := by
  cases s <;> decide

/-- No block accepts an infinite `c`. -/
theorem blockBits_infinity32 {P : Model} (a : List P.a.Word) (b : List P.b.Word) (s : Bool)
    (d : F32) : blockBits (P := P) ⟨a, b, infinity32 s⟩ ≠ .ok d := by
  intro h
  unfold blockBits at h
  cases he : evalBlock (P := P) ⟨a, b, infinity32 s⟩ with
  | error e => rw [he] at h; simp [Except.map] at h
  | ok t =>
    have hc := evalBlock_c he
    simp only [decode_infinity32, Datum.toFinite] at hc
    exact absurd hc (by simp)

theorem foldlM_outcome_finite {P : Model} (bs : List (List P.a.Word × List P.b.Word)) (d : F32) :
    ∀ o : Outcome, bs.foldlM (fun o ab =>
        match o with
        | .finite c => blockOutcome (P := P) ⟨ab.1, ab.2, c⟩
        | .infinity s => blockOutcome (P := P) ⟨ab.1, ab.2, infinity32 s⟩
        | .nan => some .nan) o = some (.finite d) →
      ∃ c, o = .finite c ∧
        bs.foldlM (fun c ab => blockBits (P := P) ⟨ab.1, ab.2, c⟩) c = .ok d := by
  induction bs with
  | nil =>
    intro o h
    simp only [List.foldlM_nil] at h
    exact ⟨d, by simpa using h, rfl⟩
  | cons ab rest ih =>
    intro o h
    rw [List.foldlM_cons] at h
    cases hs : (match o with
        | .finite c => blockOutcome (P := P) ⟨ab.1, ab.2, c⟩
        | .infinity s => blockOutcome (P := P) ⟨ab.1, ab.2, infinity32 s⟩
        | .nan => some .nan) with
    | none => rw [hs] at h; simp at h
    | some o' =>
      rw [hs] at h
      obtain ⟨c', rfl, hrest⟩ := ih o' h
      cases o with
      | finite c =>
        have hb := (blockOutcome_finite_iff _ c').mp hs
        refine ⟨c, rfl, ?_⟩
        rw [List.foldlM_cons, hb]
        exact hrest
      | infinity s =>
        exact absurd ((blockOutcome_finite_iff _ c').mp hs) (blockBits_infinity32 _ _ s c')
      | nan => simp at hs

/-- A finite observed inner product is the finite-domain inner product. -/
theorem dotOutcome_finite (P : Model) {a : List P.a.Word} {b : List P.b.Word} {c d : F32}
    (h : dotOutcome P a b c = some (.finite d)) : a.length = b.length ∧ dotBits P a b c = .ok d := by
  unfold dotOutcome at h
  split at h
  · simp at h
  · rename_i hlen
    obtain ⟨c', hc', hfold⟩ := foldlM_outcome_finite _ d _ h
    have hcc : c' = c := by
      unfold observe32 at hc'
      split at hc' <;> simp_all
    subst hcc
    refine ⟨by omega, ?_⟩
    unfold dotBits
    rw [if_neg hlen]
    exact hfold

/-! ## Loss accounting over a run -/

/-- Execute a fixed-input schedule. -/
def foldState (step : σ → α → σ) : σ → List α → σ
  | s, [] => s
  | s, a :: as => foldState step (step s a) as

def foldLoss (step : σ → α → σ) (loss : σ → α → ℚ) : σ → List α → ℚ
  | _, [] => 0
  | s, a :: as => loss s a + foldLoss step loss (step s a) as

/-- Induction for arbitrary schedules, from a local law for one step. -/
theorem fold_residual_ledger
    (value : σ → ℚ) (step : σ → α → σ) (loss : σ → α → ℚ)
    (contribution : α → ℚ)
    (localLaw : ∀ s a, value s + contribution a = value (step s a) + loss s a)
    (s : σ) (as : List α) :
    value s + sumQ (as.map contribution) =
      value (foldState step s as) + foldLoss step loss s as := by
  induction as generalizing s with
  | nil => show value s + 0 = value s + 0; rfl
  | cons a as ih =>
    simp only [List.map_cons, sumQ, foldState, foldLoss]
    have h := localLaw s a
    have h' := ih (step s a)
    grind

/-- The exact `Σ p_ℓ` of a block, without `c`. -/
def Prepared.products (x : Prepared) : ℚ := sumQ (x.p.map Unpacked.value)

/-- What a block loses: its exact `Σ p_ℓ + c` minus the value of its output. -/
def BlockTrace.residual (t : BlockTrace P) : ℚ := t.prepared.exact - wordValue t.d

theorem wordValue_of_decode {c : F32} {u : Unpacked} (h : (fp32.decode c).toFinite = some u) :
    wordValue c = u.value := by
  simp [wordValue, value32, h]

/-- Over linked blocks, the initial `c` and every block's products equal the final output plus
every block's residual. -/
theorem chain_residual_ledger (c : F32) (ts : List (BlockTrace P)) (hc : Chain c ts) :
    wordValue c + sumQ (ts.map fun t => t.prepared.products) =
      wordValue (lastOutput c ts) + sumQ (ts.map BlockTrace.residual) := by
  induction ts generalizing c with
  | nil => rfl
  | cons t ts ih =>
    obtain ⟨h1, h2⟩ := hc
    have hv := wordValue_of_decode h1
    have h' := ih t.d h2
    have hex : t.prepared.exact = t.prepared.products + t.prepared.c.value := rfl
    simp only [List.map_cons, sumQ, lastOutput, BlockTrace.residual]
    grind

theorem runBlocks_residual_ledger {P : Model} {c : F32}
    {bs : List (List P.a.Word × List P.b.Word)} {ts : List (BlockTrace P)}
    (h : runBlocks P c bs = .ok ts) :
    wordValue c + sumQ (ts.map fun t => t.prepared.products) =
      wordValue (lastOutput c ts) + sumQ (ts.map BlockTrace.residual) :=
  chain_residual_ledger c ts (runBlocks_chain h)

/-- **Inner products.** An accepted inner product decomposes into accepted, linked blocks whose
products and initial `c` equal the output plus the blocks' residuals. -/
theorem dotBits_residual_ledger (P : Model) {a : List P.a.Word} {b : List P.b.Word} {c d : F32}
    (hlen : a.length = b.length) (h : dotBits P a b c = .ok d) :
    ∃ ts, runBlocks P c (blocks P a b) = .ok ts ∧ lastOutput c ts = d ∧ Chain c ts ∧
      (∀ t ∈ ts, ∃ x : BlockInput P, evalBlock x = .ok t) ∧
      wordValue c + sumQ (ts.map fun t => t.prepared.products) =
        wordValue d + sumQ (ts.map BlockTrace.residual) := by
  obtain ⟨ts, hr, hd⟩ := (dotBits_ok_iff P c d hlen).mp h
  refine ⟨ts, hr, hd, runBlocks_chain hr, runBlocks_mem hr, ?_⟩
  rw [← hd]
  exact runBlocks_residual_ledger hr

end MatrixCore
