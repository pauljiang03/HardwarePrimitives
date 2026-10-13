import TensorCore.Kernels.EFT.Scalar
import TensorCore.Kernels.EFT.Preparation

/-! Correctness of the bounded scalar branch: passing the guard makes every FP32 step exact. -/

namespace TensorCore.EFMachine

set_option exponentiation.threshold 1024

/-- A word whose value is representable in FP32 rounds to it exactly. -/
theorem Word.round32_of_finite {x : Word} (h : FiniteValue32 x.value) :
    ∃ b, x.round32 = some b ∧ TensorCore.value32 b = some x.value := by
  obtain ⟨b, hb, hv⟩ := round32_exact_of_finite h
  exact ⟨b, by rw [x.round32_eq]; exact hb, hv⟩

/-- Left-to-right FP32 summation of encoded words follows the value-level naive sum. -/
theorem foldlM_add32 (bs : List F32) (vs : List ℚ) (acc : F32) (a s : ℚ)
    (hacc : TensorCore.value32 acc = some a) (hbs : bs.map TensorCore.value32 = vs.map some)
    (hs : naiveSum32From a vs = some s) :
    ∃ r, bs.foldlM add32 acc = some r ∧ TensorCore.value32 r = some s := by
  induction bs generalizing vs acc a with
  | nil =>
    cases vs with
    | nil =>
      simp only [naiveSum32From, Option.some.injEq] at hs
      exact ⟨acc, rfl, hs ▸ hacc⟩
    | cons v vs => simp at hbs
  | cons b bs ih =>
    cases vs with
    | nil => simp at hbs
    | cons v vs =>
      simp only [List.map_cons, List.cons.injEq] at hbs
      obtain ⟨hb, hbs⟩ := hbs
      simp only [naiveSum32From, fp32Add] at hs
      cases hr : TensorCore.round32 .nearestEven (a + v) with
      | none => simp [hr] at hs
      | some r1 =>
        cases hv1 : TensorCore.value32 r1 with
        | none => simp [hr, hv1] at hs
        | some s1 =>
          simp only [hr, hv1, Option.bind_some] at hs
          have hadd : add32 acc b = some r1 := by
            rw [add32_eq, hacc, hb]
            simpa using hr
          obtain ⟨r, hr', hvr⟩ := ih vs r1 s1 hv1 hbs hs
          exact ⟨r, by simp [List.foldlM, hadd, hr'], hvr⟩

/-- An accepted unsigned magnitude sum is the exact sum of the magnitudes. -/
theorem magnitudeSumWords_toNat {ms : List Magnitude} {s : Magnitude}
    (h : magnitudeSumWords ms = some s) : s.toNat = (ms.map BitVec.toNat).sum := by
  induction ms generalizing s with
  | nil =>
    simp only [magnitudeSumWords, Option.some.injEq] at h
    subst h; rfl
  | cons m ms ih =>
    simp only [magnitudeSumWords] at h
    cases hy : magnitudeSumWords ms with
    | none => simp [hy] at h
    | some y =>
      simp only [hy, Option.bind_eq_bind, Option.bind_some] at h
      split at h
      · contradiction
      · rename_i hn
        simp only [Option.some.injEq] at h
        subst h
        have hlt := (magnitude_add_no_wrap m y).mp hn
        rw [BitVec.toNat_add, Nat.mod_eq_of_lt hlt, ih hy]
        simp

/-- Signed count of `2^e`-steps in a word whose magnitude is a multiple of `2^e`. -/
def Word.stepsAt (x : Word) (e : Magnitude) : ℤ :=
  if x.negative then -((x.magnitude >>> e).toNat : ℤ) else ((x.magnitude >>> e).toNat : ℤ)

/-- A magnitude with no set bit below `2^e` is that many `2^e`-steps. -/
theorem Word.value_eq_stepsAt {x : Word} {e : Magnitude}
    (h : ((x.magnitude >>> e) <<< e) = x.magnitude) :
    x.value = (x.stepsAt e : ℚ) * pow2 ((e.toNat : ℤ) - 272) := by
  have hm := congrArg BitVec.toNat h
  rw [BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft, BitVec.ushiftRight_eq',
    BitVec.toNat_ushiftRight, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow] at hm
  have hle : x.magnitude.toNat / 2 ^ e.toNat * 2 ^ e.toNat ≤ x.magnitude.toNat :=
    Nat.div_mul_le_self _ _
  rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hle x.magnitude.isLt)] at hm
  have hk : ((x.magnitude >>> e).toNat) = x.magnitude.toNat / 2 ^ e.toNat := by
    rw [BitVec.ushiftRight_eq', BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hp : pow2 ((e.toNat : ℤ) - 272) = ((2 ^ e.toNat : ℕ) : ℚ) * pow2 (-272) := by
    rw [show ((e.toNat : ℤ) - 272) = (e.toNat : ℤ) + (-272) by omega, pow2_add, pow2_natCast]
  have hmag : (x.magnitude.toNat : ℚ) =
      ((x.magnitude.toNat / 2 ^ e.toNat : ℕ) : ℚ) * ((2 ^ e.toNat : ℕ) : ℚ) := by
    exact_mod_cast hm.symm
  unfold Word.value Word.coefficient Word.stepsAt
  rw [hp, hk]
  cases x.negative <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Rat.intCast_neg, Rat.intCast_natCast] <;>
    rw [hmag] <;> grind

theorem natAbs_le_magnitudeSum {zs : List ℤ} {z : ℤ} (h : z ∈ zs) : z.natAbs ≤ magnitudeSum zs := by
  induction zs with
  | nil => simp at h
  | cons y ys ih =>
    simp only [magnitudeSum]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := ih h; omega

/-- Every word rounds exactly when every value is representable in FP32. -/
theorem mapM_round32 (xs : List Word) (hx : ∀ x ∈ xs, FiniteValue32 x.value) :
    ∃ bs, xs.mapM Word.round32 = some bs ∧
      bs.map TensorCore.value32 = (xs.map Word.value).map some := by
  induction xs with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons x xs ih =>
    obtain ⟨b, hb, hv⟩ := Word.round32_of_finite (hx x (by simp))
    obtain ⟨bs, hbs, hvs⟩ := ih (fun y hy => hx y (by simp [hy]))
    refine ⟨b :: bs, ?_, ?_⟩
    · simp [List.mapM_cons, hb, hbs]
    · simp [hv, hvs]

/-- FP32 summation of words lying on one grid, within a 24-bit coefficient bound, is exact. -/
theorem scalarSum_exact (xs : List Word) (ℓ : ℤ) (zs : List ℤ) (h1 : -149 ≤ ℓ) (h2 : ℓ ≤ 104)
    (hv : xs.map Word.value = zs.map fun (z : ℤ) => (z : ℚ) * pow2 ℓ) (hb : magnitudeSum zs < 2 ^ 24) :
    ∃ b, scalarSum xs = some b ∧ TensorCore.value32 b = some (sumQ (xs.map Word.value)) := by
  have hfin : ∀ x ∈ xs, FiniteValue32 x.value := by
    intro x hx
    have hmem : x.value ∈ zs.map fun (z : ℤ) => (z : ℚ) * pow2 ℓ := hv ▸ List.mem_map_of_mem hx
    obtain ⟨z, hz, hzx⟩ := List.mem_map.mp hmem
    rw [← hzx]
    exact grid_finiteValue32 z ℓ h1 h2 (by have := natAbs_le_magnitudeSum hz; omega)
  obtain ⟨bs, hbs, hvs⟩ := mapM_round32 xs hfin
  have hnaive := naiveSum32From_exact ℓ h1 h2 0 zs (by simpa using hb)
  have h0 : (((0 : ℤ) : ℚ) * pow2 ℓ) = 0 := by simp
  rw [h0] at hnaive
  have hz : TensorCore.value32 (0 : F32) = some 0 := by decide +kernel
  obtain ⟨r, hr, hvr⟩ := foldlM_add32 bs (zs.map fun (z : ℤ) => (z : ℚ) * pow2 ℓ) 0 0 _ hz
    (by rw [hvs, hv]) hnaive
  refine ⟨r, by simp [scalarSum, hbs]; exact hr, ?_⟩
  rw [hvr, hv, sum_coefficients]
  simp

theorem magnitudeSum_stepsAt (xs : List Word) (e : Magnitude) :
    magnitudeSum (xs.map (·.stepsAt e)) = ((xs.map fun x => x.magnitude >>> e).map BitVec.toNat).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, magnitudeSum, List.sum_cons]
    rw [ih]
    congr 1
    unfold Word.stepsAt
    cases x.negative
    · exact Int.natAbs_natCast _
    · exact (Int.natAbs_neg _).trans (Int.natAbs_natCast _)

/-- Under the guard's conditions on a common grid `ell`, the scalar branch returns RN of the exact sum. -/
theorem Components.scalar_of_conditions {p : Prepared} {c : Components} {ell s : Magnitude}
    (hc : extract p = some c) (hguard : c.scalarGuard = true)
    (h1 : 123 ≤ ell.toNat) (h2 : ell.toNat ≤ 376)
    (hgrid : ∀ x ∈ c.low, ((x.magnitude >>> ell) <<< ell) = x.magnitude)
    (hs : magnitudeSumWords (c.low.map fun x => x.magnitude >>> ell) = some s)
    (hs24 : s.toNat < 2 ^ 24)
    (hov : c.overlap.exact32.isSome = true) (hret : c.retained.exact32.isSome = true)
    (hout : FiniteValue32 p.output.value) :
    c.scalar = TensorCore.round32 .nearestEven p.ideal := by
  obtain ⟨hcp, _, _, _, hovv, hres, hrecv, hideal⟩ := extract_spec hc
  let ℓ : ℤ := (ell.toNat : ℤ) - 272
  let zs := c.low.map (·.stepsAt ell)
  have hv : c.low.map Word.value = zs.map fun (z : ℤ) => (z : ℚ) * pow2 ℓ := by
    simp only [zs, List.map_map]
    exact List.map_congr_left fun x hx => Word.value_eq_stepsAt (hgrid x hx)
  have hbound : magnitudeSum zs < 2 ^ 24 := by
    rw [magnitudeSum_stepsAt, ← magnitudeSumWords_toNat hs]; exact hs24
  obtain ⟨eb, he, hve⟩ := scalarSum_exact c.low ℓ zs (by omega) (by omega) hv hbound
  rw [← hres] at hve
  obtain ⟨db, hdb, hvdb⟩ := Word.round32_of_finite (x := c.prepared.output) (by rw [hcp]; exact hout)
  obtain ⟨ob0, hob0⟩ := Option.isSome_iff_exists.mp hov
  have hfo := value32_finite _ _ (Word.exact32_value hob0)
  obtain ⟨ob, hob, hvob⟩ := Word.round32_of_finite (x := c.overlap.neg)
    (by rw [Word.neg_value]; exact finiteValue32_neg hfo)
  obtain ⟨rb0, hrb0⟩ := Option.isSome_iff_exists.mp hret
  obtain ⟨hb, hhb, hvhb⟩ := round32_exact_of_finite (value32_finite _ _ (Word.exact32_value hrb0))
  have hsum : c.prepared.output.value + c.overlap.neg.value = c.retained.value := by
    rw [Word.neg_value, hovv, hcp]; grind
  have hadd : add32 db ob = some hb := by
    rw [add32_eq, hvdb, hvob]; simpa [hsum] using hhb
  have hfinal : add32 hb eb = TensorCore.round32 .nearestEven p.ideal := by
    rw [add32_eq, hvhb, hve, ← hideal, hrecv]; rfl
  simp only [Components.scalar, hguard, Bool.not_true, Bool.false_eq_true, ↓reduceIte, he,
    Option.bind_eq_bind, Option.bind_some, hdb, hob, hadd, hfinal]

/-- When the guard accepts, the scalar branch returns the correctly rounded exact sum. -/
theorem Components.scalar_of_guard {variant : Variant} {x : BlockInput variant.model} {D : F32}
    {p : Prepared} {c : Components} (hp : prepare variant x D = .ok p) (hc : extract p = some c)
    (hg : c.scalarGuard = true) :
    c.scalar = TensorCore.round32 .nearestEven p.ideal := by
  obtain ⟨_, _, hD, _⟩ := prepare_spec hp
  have hout := value32_finite _ _ hD
  have hg' := hg
  simp only [Components.scalarGuard, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    beq_iff_eq, Option.any_eq_true] at hg'
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, hgrid⟩, ⟨s, hs, hs24⟩⟩, hov⟩, hret⟩, _⟩ := hg'
  exact Components.scalar_of_conditions hc hg (BitVec.le_def.mp h1) (BitVec.le_def.mp h2)
    hgrid hs (by have := BitVec.lt_def.mp hs24; simpa using this) hov hret hout

/-- When the guard accepts, the scalar branch returns a value. -/
theorem Components.scalar_isSome_of_guard {variant : Variant} {x : BlockInput variant.model} {D : F32}
    {p : Prepared} {c : Components} (hp : prepare variant x D = .ok p) (hc : extract p = some c)
    (hg : c.scalarGuard = true) : c.scalar.isSome = true := by
  rw [Components.scalar_of_guard hp hc hg]
  have hrec := hg
  simp only [Components.scalarGuard, Bool.and_eq_true, decide_eq_true_eq] at hrec
  obtain ⟨_, _, _, _, _, _, hrecv, hideal⟩ := extract_spec hc
  rw [← hideal, ← Word.round32_eq]
  exact (Word.round32_isSome_iff _).mpr ((Word.range_iff _).mpr hrec.2)

/-- Any scalar-branch result is the correctly rounded exact sum. -/
theorem Components.scalar_correct {variant : Variant} {x : BlockInput variant.model} {D : F32}
    {p : Prepared} {c : Components} {b : F32} (hp : prepare variant x D = .ok p)
    (hc : extract p = some c) (hb : c.scalar = some b) :
    TensorCore.round32 .nearestEven p.ideal = some b := by
  cases hg : c.scalarGuard
  · simp [Components.scalar, hg] at hb
  · rw [← Components.scalar_of_guard hp hc hg, hb]

/-- A nonzero block that passes the guard takes the scalar branch, with the correctly rounded sum. -/
theorem tcEft_scalar_of_guard {variant : Variant} {x : BlockInput variant.model} {D : F32}
    {p : Prepared} {c : Components} (hp : prepare variant x D = .ok p) (hc : extract p = some c)
    (hnz : ¬ p.terms.all (fun t => t.word.magnitude == 0) = true) (hg : c.scalarGuard = true) :
    ∃ b, tcEft variant x D = .ok (.scalar b) ∧ TensorCore.round32 .nearestEven p.ideal = some b := by
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (Components.scalar_isSome_of_guard hp hc hg)
  refine ⟨b, ?_, (Components.scalar_of_guard hp hc hg).symm.trans hb⟩
  unfold tcEft
  simp only [hp, Bind.bind, Except.bind]
  rw [if_neg hnz, hc]
  dsimp +instances only
  rw [hb]
  rfl

end TensorCore.EFMachine
