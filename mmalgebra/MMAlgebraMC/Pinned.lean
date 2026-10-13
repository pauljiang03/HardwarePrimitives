import OzakiMC

/-! # Pinned accumulation on CDNA 3

CDNA 3 (`global_alignment`) aligns the products of a block to their largest exponent `e_max`,
truncates each to `23 + n_eab` fractional bits, and then adds `c` late. If one nonzero product of
every block has exponent exactly `α` and none exceeds it (a pin, for example `+2^α, −2^α`), then
`e_max = α`; a `c` on the grid `2^(α−24)` with exponent at most `α` passes the late addition's
rounding down unchanged; and a sum on that grid below `2^α` is a binary32 value, which round to
nearest returns. So a pinned block returns `c + Σ trunc_{α−24}(p_ℓ)` (`evalBlock_pinned`), and a
pinned chain returns `c₀ + Σ_blocks Σ trunc_{α−24}(p_ℓ)` (`runBlocks_pinned`): the same function as
the Tensor Core pinned chain with `α_TC − F = α_CDNA3 − 24`. The conditions on each block's `c` are
derived along the chain, not assumed. -/

open MatrixCore
open Ozaki.MC

namespace MMAlgebra.MC


/-- The truncated sum `Σ trunc_{α−24}(p_ℓ)` of the products of a prepared block. -/
def truncSum (α : ℤ) (x : Prepared) : ℚ := sumQ (x.p.map fun p => truncFrac p.value α 24)

theorem maxExp_eq {ps : List Unpacked} {α : ℤ} (hle : ∀ p ∈ ps, p.m ≠ 0 → p.e ≤ α)
    (hpin : ∃ p ∈ ps, p.m ≠ 0 ∧ p.e = α) : maxExp ps = some α := by
  obtain ⟨q, hq, hqm, hqe⟩ := hpin
  cases hm : maxExp ps with
  | none => exact absurd (maxExp_none hm q hq) hqm
  | some e =>
    have h1 := maxExp_le hm q hq hqm
    have h2 := maxExp_upper hle e hm
    congr 1; omega

/-- The conditions of a pinned CDNA 3 block on its prepared operands. -/
structure Pinned (α : ℤ) (x : Prepared) : Prop where
  le : ∀ p ∈ x.p, p.m ≠ 0 → p.e ≤ α
  pin : ∃ p ∈ x.p, p.m ≠ 0 ∧ p.e = α
  cexp : x.c.m ≠ 0 → x.c.e ≤ α
  cgrid : OnGrid x.c.value (α - 24)

/-- CDNA 3's parameters: global alignment, one extra alignment bit, the default late alignment,
`e_{c=0} = −126`, and subnormals kept. -/
structure CDNA3Like (P : Model) : Prop where
  acc : P.accumulation = .globalAlignment
  neab : P.neab = 1
  late : P.late = {}
  cz : P.cZeroExp = some (-126)
  sub : P.subnormals = true

/-- **Pinned accumulation value.** `S_acc = Σ trunc_{α−24}(p_ℓ) + c`. -/
theorem alignedAccumulation_pinned {P : Model} (hP : CDNA3Like P) {x : Prepared} {α : ℤ}
    (hx : Pinned α x) (hα : -126 ≤ α) :
    alignedAccumulation P x = truncSum α x + x.c.value := by
  have hps : productSum P x.p = (some α, truncSum α x) := by
    unfold productSum; rw [hP.acc]; simp only
    unfold alignedSum; rw [maxExp_eq hx.le hx.pin]; simp only [truncSum, hP.neab]
  unfold alignedAccumulation; simp only
  rw [hps]
  rcases lateSum_cases P (some α) (truncSum α x) x.c with
    ⟨hc0, _⟩ | ⟨e, eC, he, hce, _, hl⟩ | ⟨eC, hce, hlt, _⟩
  · unfold cExp at hc0; rw [hP.cz] at hc0; split at hc0 <;> simp at hc0
  · have he' : e = α := by simp only [Option.some.injEq] at he; omega
    rw [hl]
    have hsc : shiftedC P e eC x.c = x.c.value := by
      unfold shiftedC; rw [hP.late]; simp only
      rw [he']; exact rdGrid_of_onGrid hx.cgrid
    rw [hsc]
  · exfalso
    have := hlt α rfl
    unfold cExp at hce; rw [hP.cz] at hce
    split at hce
    · cases hce; omega
    · rename_i hm; cases hce; have := hx.cexp hm; omega

/-- A sum on the grid `2^(α−24)` below `2^α` is a binary32 value. -/
theorem grid_finite {y : ℚ} {α : ℤ} (hg : OnGrid y (α - 24)) (hlo : -125 ≤ α) (hhi : α ≤ 128)
    (hy : absQ y < pow2 α) : FiniteValue32 y := by
  obtain ⟨k, rfl⟩ := hg
  refine ⟨k, α - 1, by omega, by omega, ?_, by rw [show α - 1 - 23 = α - 24 by omega]⟩
  have hp := pow2_pos (α - 24)
  have h1 : absQ ((k : ℚ) * pow2 (α - 24)) = absQ (k : ℚ) * pow2 (α - 24) :=
    absQ_mul_pos _ _ hp
  rw [h1] at hy
  have e : pow2 α = pow2 24 * pow2 (α - 24) := by rw [← pow2_add]; congr 1; omega
  rw [e] at hy
  have h2 : absQ (k : ℚ) < pow2 24 := by
    apply Classical.byContradiction; intro hn
    have : pow2 24 * pow2 (α - 24) ≤ absQ (k : ℚ) * pow2 (α - 24) :=
      Rat.mul_le_mul_of_nonneg_right (by grind) (Rat.le_of_lt hp)
    grind
  rw [absQ_intCast, show (24 : ℤ) = ((24 : ℕ) : ℤ) from rfl, pow2_natCast] at h2
  have := Rat.natCast_lt_natCast.mp h2
  omega

/-- RNE without flushing returns a binary32 value unchanged. -/
theorem fl32_finite {y : ℚ} (hf : FiniteValue32 y) : ∃ w, fl32 false y = some w ∧ value32 w = some y := by
  have hlt : absQ y < overflowThreshold32 := by
    obtain ⟨k, e, h1, h2, h3, rfl⟩ := hf
    have hp := pow2_pos (e - 23)
    have hk : absQ (k : ℚ) ≤ 16777215 := by
      rw [absQ_intCast]
      have : k.natAbs ≤ 16777215 := by omega
      exact_mod_cast this
    have hb : absQ ((k : ℚ) * pow2 (e - 23)) ≤ 16777215 * pow2 (e - 23) := by
      rw [absQ_mul_pos _ _ hp]
      exact Rat.mul_le_mul_of_nonneg_right hk (Rat.le_of_lt hp)
    have hm : (16777215 : ℚ) * pow2 (e - 23) ≤ 16777215 * pow2 104 :=
      Rat.mul_le_mul_of_nonneg_left (pow2_le_of_le (by omega)) (by decide)
    have ht : (16777215 : ℚ) * pow2 104 < overflowThreshold32 := by
      unfold overflowThreshold32 pow2; decide +kernel
    grind
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp ((rne32_isSome_iff _).mpr hlt)
  refine ⟨w, ?_, by rw [rne32_value hw, rneValue_of_finite hf]⟩
  unfold fl32; rw [hw]; simp

/-- **Pinned CDNA 3 block.** The output word has value `c + Σ trunc_{α−24}(p_ℓ)`. -/
theorem evalBlock_pinned {P : Model} (hP : CDNA3Like P) {x : BlockInput P} {t : BlockTrace P}
    (ht : evalBlock x = .ok t) {α : ℤ} (hx : Pinned α t.prepared) (hlo : -125 ≤ α) (hhi : α ≤ 128)
    (hrange : absQ (truncSum α t.prepared + t.prepared.c.value) < pow2 α) :
    value32 t.d = some (truncSum α t.prepared + t.prepared.c.value) := by
  unfold evalBlock at ht
  split at ht
  · cases ht
  · split at ht
    · cases ht
    · rename_i px hpx
      split at ht
      · cases ht
      · rename_i s hs
        split at ht
        · cases ht
        · rename_i d hd
          cases ht
          simp only at hx hrange ⊢
          have hs' : alignedAccumulation P px = s := by
            unfold accumulate at hs
            split at hs
            · cases hs
            · rw [hP.acc] at hs; simpa using hs
          rw [← hs', alignedAccumulation_pinned hP hx (by omega)] at hd
          have hg : OnGrid (truncSum α px + px.c.value) (α - 24) := by
            refine OnGrid.add ?_ hx.cgrid
            unfold truncSum
            generalize px.p = ps
            induction ps with
            | nil => exact OnGrid.zero _
            | cons q qs ih =>
              exact OnGrid.add (by simp only [truncFrac]; exact truncGrid_onGrid _ _) ih
          obtain ⟨w, hw, hv⟩ := fl32_finite (grid_finite hg hlo hhi hrange)
          rw [hP.sub] at hd; simp only [Bool.not_true] at hd
          rw [hw] at hd; cases hd; exact hv

/-! ## The conditions on `c`, derived -/

/-- The products of a block are pinned at `α`: none exceeds exponent `α`, and one nonzero product
has exponent exactly `α`. -/
structure PinnedProducts (α : ℤ) (x : Prepared) : Prop where
  le : ∀ p ∈ x.p, p.m ≠ 0 → p.e ≤ α
  pin : ∃ p ∈ x.p, p.m ≠ 0 ∧ p.e = α

/-- A nonzero binary32 value below `2^α` (`α ≥ −126`) has exponent at most `α`. -/
theorem decode32_exp_le {w : F32} {u : Unpacked} (h : (binary32.decode w).toFinite = some u)
    {α : ℤ} (hα : -126 ≤ α) (hv : absQ u.value < pow2 α) : u.m ≠ 0 → u.e ≤ α := by
  intro _
  have hd' : binary32.decodeNat w.toNat = .finite u := by
    cases hd : binary32.decodeNat w.toNat with
    | finite v =>
      have hdec : binary32.decode w = .finite v := hd
      rw [hdec] at h; simp only [Datum.toFinite, Option.some.injEq] at h; rw [h]
    | infinity _ =>
      have hdec : binary32.decode w = .infinity _ := hd
      rw [hdec] at h; simp [Datum.toFinite] at h
    | nan =>
      have hdec : binary32.decode w = .nan := hd
      rw [hdec] at h; simp [Datum.toFinite] at h
  by_cases hn : 2 ^ u.t ≤ u.m
  · have h1 := pow2_le_absQ hn
    apply Classical.byContradiction; intro hlt
    have : pow2 α ≤ pow2 u.e := pow2_le_of_le (by omega)
    grind
  · have := decodeNat_sub hd' (by omega)
    rw [this]; show (1 : ℤ) - 127 ≤ α; omega

theorem truncSum_onGrid (α : ℤ) (x : Prepared) : OnGrid (truncSum α x) (α - 24) := by
  unfold truncSum
  generalize x.p = ps
  induction ps with
  | nil => exact OnGrid.zero _
  | cons q qs ih => exact OnGrid.add (by simp only [truncFrac]; exact truncGrid_onGrid _ _) ih

/-- **Pinned CDNA 3 chain.** From `c₀` on the grid `2^(α−24)`, with the products of every block
pinned at `α` and the running value at every block boundary below `2^α`, the run returns
`c₀ + Σ_blocks Σ trunc_{α−24}(p_ℓ)`. The conditions on each block's `c` (exponent at most `α`, on
the grid) follow: every running value is a sum of grid values below `2^α`. -/
theorem runBlocks_pinned {P : Model} (hP : CDNA3Like P) {α : ℤ} (hlo : -125 ≤ α) (hhi : α ≤ 128) :
    ∀ (bs : List (List P.a.Word × List P.b.Word)) (c : F32) (v : ℚ) (ts : List (BlockTrace P)),
      value32 c = some v → OnGrid v (α - 24) → runBlocks P c bs = .ok ts →
      (∀ t ∈ ts, PinnedProducts α t.prepared) →
      (∀ n ≤ ts.length, absQ (v + sumQ ((ts.take n).map fun t => truncSum α t.prepared)) < pow2 α) →
      value32 (lastOutput c ts) = some (v + sumQ (ts.map fun t => truncSum α t.prepared))
  | [], c, v, ts, hc, _, hrun, _, _ => by
    simp only [runBlocks, Except.ok.injEq] at hrun; subst hrun
    simp [lastOutput, hc, sumQ]
    grind
  | ab :: rest, c, v, ts, hc, hgrid, hrun, hpin, hrange => by
    obtain ⟨t, ts', ht, hts', rfl⟩ := runBlocks_cons hrun
    have hcdec := evalBlock_c ht
    have hcv : t.prepared.c.value = v := by
      unfold value32 at hc; simp only at hcdec; rw [hcdec] at hc; simpa using hc
    have h0 := hrange 0 (by simp)
    simp only [List.take_zero, List.map_nil, sumQ, Rat.add_zero] at h0
    have hpt := hpin t (by simp)
    have hP' : Pinned α t.prepared :=
      ⟨hpt.le, hpt.pin, decode32_exp_le hcdec (by omega) (by rw [hcv]; exact h0),
        by rw [hcv]; exact hgrid⟩
    have h1 := hrange 1 (by simp)
    simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, sumQ] at h1
    have hb := evalBlock_pinned hP ht hP' hlo hhi
      (by rw [hcv]; rw [show v + (truncSum α t.prepared + 0) = truncSum α t.prepared + v by grind] at h1
          exact h1)
    rw [hcv] at hb
    simp only [lastOutput, List.map_cons, sumQ]
    have hrest := runBlocks_pinned hP hlo hhi rest t.d (truncSum α t.prepared + v) ts' hb
      (OnGrid.add (truncSum_onGrid α t.prepared) hgrid) hts'
      (fun t' ht' => hpin t' (by simp [ht']))
      (by
        intro n hn
        have := hrange (n + 1) (by simp; omega)
        simp only [List.take_succ_cons, List.map_cons, sumQ] at this
        rw [show truncSum α t.prepared + v + sumQ ((ts'.take n).map fun t => truncSum α t.prepared) =
          v + (truncSum α t.prepared + sumQ ((ts'.take n).map fun t => truncSum α t.prepared)) by grind]
        exact this)
    rw [hrest]; congr 1; grind

end MMAlgebra.MC
