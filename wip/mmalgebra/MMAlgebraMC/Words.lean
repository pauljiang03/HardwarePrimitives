import MMAlgebraMC.Exact
import OzakiMC

/-! # Binary32 words on the Matrix Core machine

Facts about binary32 words used by the reduction algebra on the AMD models: a finite word is
determined by its sign and value, so rounding the value of a finite word other than `−0` returns
the word (`fl32_value_self`); every binary32 value is a multiple of `2^-149`, and rounding a nonzero
multiple of `2^-149` to nearest never gives `−0` (`fl32_good`). Hence binary32 addition on the
machine is commutative, has `+0` as a unit on finite words other than `−0`, and never returns `−0`
(`mc_add_comm`, `mc_add_zero`, `mc_add_good`). -/

open MatrixCore Ozaki.MC

namespace MMAlgebra.MC

/-- A finite word other than `−0`. -/
def GoodW (w : F32) : Prop := (value32 w).isSome = true ∧ w ≠ 0x80000000

instance (w : F32) : Decidable (GoodW w) := by unfold GoodW; infer_instance

theorem decode32_val (w : F32) {u : Unpacked} (h : (fp32.decode w).toFinite = some u) :
    u = (if w.toNat / 8388608 % 256 = 0 then
      ⟨w.toNat / 2147483648 % 2 == 1, w.toNat % 8388608, -126, 23⟩ else
      ⟨w.toNat / 2147483648 % 2 == 1, 8388608 + w.toNat % 8388608,
        ((w.toNat / 8388608 % 256 : ℕ) : ℤ) - 127, 23⟩) := by
  rw [decode32_eq] at h
  simp only at h
  split at h
  · split at h <;> simp [Datum.toFinite] at h
  · simp only [Datum.toFinite, Option.some.injEq] at h
    exact h.symm

/-- The sign bit of a finite word is the sign of its nonzero value. -/
theorem value32_sign {w : F32} {v : ℚ} (h : value32 w = some v) (hv : v ≠ 0) :
    sign32 w = decide (v < 0) := by
  unfold value32 at h
  cases hd : (fp32.decode w).toFinite with
  | none => rw [hd] at h; cases h
  | some u =>
    rw [hd] at h
    simp only [Option.map_some, Option.some.injEq] at h
    have hu := decode32_val w hd
    subst h
    unfold sign32
    have hp := pow2_pos (u.e - u.t)
    cases hs : (w.toNat / 2147483648 % 2 == 1)
    · have hneg : u.negative = false := by rw [hu]; split <;> simp [hs]
      have : 0 ≤ u.value := by
        unfold Unpacked.value; rw [hneg]; simp only [Bool.false_eq_true, ↓reduceIte]
        exact Rat.mul_nonneg (by exact_mod_cast Nat.zero_le _) (Rat.le_of_lt hp)
      simp; grind
    · have hneg : u.negative = true := by rw [hu]; split <;> simp [hs]
      have hm : u.m ≠ 0 := by
        intro h0; apply hv; unfold Unpacked.value; simp [h0]
      have : u.value < 0 := by
        unfold Unpacked.value; rw [hneg]; simp only [↓reduceIte]
        have : (0 : ℚ) < (u.m : ℚ) := by exact_mod_cast Nat.pos_of_ne_zero hm
        have := Rat.mul_pos this hp
        grind
      simp [this]

/-- A finite word of value zero is `+0` or `−0`. -/
theorem value32_zero_word {w : F32} (h : value32 w = some 0) : w = 0 ∨ w = 0x80000000 := by
  unfold value32 at h
  cases hd : (fp32.decode w).toFinite with
  | none => rw [hd] at h; cases h
  | some u =>
    rw [hd] at h
    simp only [Option.map_some, Option.some.injEq] at h
    have hu := decode32_val w hd
    have hm : u.m = 0 := by
      apply Classical.byContradiction; intro hm
      have hp := pow2_pos (u.e - u.t)
      have : (0 : ℚ) < (u.m : ℚ) := by exact_mod_cast Nat.pos_of_ne_zero hm
      unfold Unpacked.value at h
      split at h
      · have := Rat.mul_pos this hp; grind
      · have := Rat.mul_pos this hp; grind
    have hlt := w.isLt
    have hfields := decode32_fields_eq w
    rw [hu] at hm
    split at hm
    · rename_i hE
      simp only at hm
      have hs : w.toNat / 2147483648 % 2 < 2 := Nat.mod_lt _ (by decide)
      rcases (by omega : w.toNat / 2147483648 % 2 = 0 ∨ w.toNat / 2147483648 % 2 = 1) with h0 | h1
      · left; apply BitVec.eq_of_toNat_eq; show w.toNat = 0; omega
      · right; apply BitVec.eq_of_toNat_eq; show w.toNat = 2147483648; omega
    · simp at hm

theorem finiteValue32_lt {v : ℚ} (h : FiniteValue32 v) : absQ v < overflowThreshold32 := by
  obtain ⟨k, e, h1, h2, h3, rfl⟩ := h
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

/-- **Rounding the value of a finite word other than `−0` returns the word.** -/
theorem fl32_value_self {w : F32} {v : ℚ} (h : value32 w = some v) (hw : w ≠ 0x80000000) :
    fl32 false v = some w := by
  rw [fl32_false]
  by_cases hv : v = 0
  · subst hv
    rcases value32_zero_word h with h0 | h0
    · subst h0; exact rne32_zero
    · exact absurd h0 hw
  · have hf := value32_finiteValue h
    obtain ⟨w', hw'⟩ := Option.isSome_iff_exists.mp ((rne32_isSome_iff v).mpr (finiteValue32_lt hf))
    rw [hw']
    have hval : value32 w' = some v := by rw [rne32_value hw', rneValue_of_finite hf]
    have hs : sign32 w' = sign32 w := by rw [rne32_sign hw', value32_sign h hv]
    rw [value32_injective hval h hs]

/-- Every binary32 value is a multiple of `2^-149`. -/
theorem value32_onGrid {w : F32} {v : ℚ} (h : value32 w = some v) : OnGrid v (-149) := by
  obtain ⟨k, e, h1, _, _, rfl⟩ := value32_finiteValue h
  exact onGrid_intCast_mul k (e - 23) (-149) (by omega)

theorem finiteValue32_pow2 : FiniteValue32 (pow2 (-149)) :=
  ⟨1, -126, by decide, by decide, by decide, by simp⟩

/-- **Rounding a multiple of `2^-149` to nearest never gives `−0`.** -/
theorem fl32_good {x : ℚ} (hg : OnGrid x (-149)) {w : F32} (h : fl32 false x = some w) : GoodW w := by
  rw [fl32_false] at h
  have hv := rne32_value h
  refine ⟨by rw [hv]; rfl, ?_⟩
  intro hneg
  by_cases hx : x = 0
  · subst hx; rw [rne32_zero] at h; cases h; exact absurd hneg (by decide)
  · rw [hneg] at hv
    have hv0 : value32 (0x80000000 : F32) = some 0 := by decide +kernel
    rw [hv0] at hv
    have hr : rneValue x = 0 := (Option.some.inj hv).symm
    obtain ⟨d, hd, hnear, _⟩ := rne32_nearestEven h
    rw [hneg, hv0] at hd
    cases hd
    obtain ⟨k, rfl⟩ := hg
    have hk : k ≠ 0 := by intro h0; subst h0; simp at hx
    have hp := pow2_pos (-149)
    obtain ⟨w₁, hw₁⟩ := Option.isSome_iff_exists.mp ((rne32_isSome_iff (pow2 (-149))).mpr
      (finiteValue32_lt finiteValue32_pow2))
    have hv₁ : value32 w₁ = some (pow2 (-149)) := by
      rw [rne32_value hw₁, rneValue_of_finite finiteValue32_pow2]
    have hfin : FiniteValue32 (-pow2 (-149)) := finiteValue32_pow2.neg
    obtain ⟨w₂, hw₂⟩ := Option.isSome_iff_exists.mp ((rne32_isSome_iff (-pow2 (-149))).mpr
      (finiteValue32_lt hfin))
    have hv₂ : value32 w₂ = some (-pow2 (-149)) := by
      rw [rne32_value hw₂, rneValue_of_finite hfin]
    have hsub : ∀ q : ℚ, q - 0 = q := fun q => by grind
    rcases (by omega : 1 ≤ k ∨ k ≤ -1) with h1 | h1
    · have hn := hnear w₁ _ hv₁
      rw [hsub] at hn
      have hk1 : (1 : ℚ) ≤ (k : ℚ) := by exact_mod_cast h1
      have e1 : absQ ((k : ℚ) * pow2 (-149)) = (k : ℚ) * pow2 (-149) :=
        absQ_of_nonneg (Rat.mul_nonneg (by grind) (Rat.le_of_lt hp))
      have e2 : absQ ((k : ℚ) * pow2 (-149) - pow2 (-149)) = ((k : ℚ) - 1) * pow2 (-149) := by
        rw [show (k : ℚ) * pow2 (-149) - pow2 (-149) = ((k : ℚ) - 1) * pow2 (-149) by grind]
        exact absQ_of_nonneg (Rat.mul_nonneg (by grind) (Rat.le_of_lt hp))
      rw [e1, e2] at hn
      grind
    · have hn := hnear w₂ _ hv₂
      rw [hsub] at hn
      have hk1 : (k : ℚ) ≤ -1 := by
        have : (k : ℚ) ≤ ((-1 : ℤ) : ℚ) := Rat.intCast_le_intCast.mpr h1
        simpa using this
      have e1 : absQ ((k : ℚ) * pow2 (-149)) = -((k : ℚ) * pow2 (-149)) := by
        rw [← absQ_neg]
        exact absQ_of_nonneg (by
          rw [show -((k : ℚ) * pow2 (-149)) = (-(k : ℚ)) * pow2 (-149) by grind]
          exact Rat.mul_nonneg (by grind) (Rat.le_of_lt hp))
      have e2 : absQ ((k : ℚ) * pow2 (-149) - -pow2 (-149)) = -(((k : ℚ) + 1) * pow2 (-149)) := by
        rw [← absQ_neg]
        rw [show -((k : ℚ) * pow2 (-149) - -pow2 (-149)) = (-((k : ℚ) + 1)) * pow2 (-149) by grind]
        rw [absQ_of_nonneg (Rat.mul_nonneg (by grind) (Rat.le_of_lt hp))]
        grind
      rw [e1, e2] at hn
      grind

/-! ## Binary32 addition on the machine -/

theorem val_onGrid (P : Model) (w : F32) : OnGrid ((mcMachine P).val w) (-149) := by
  show OnGrid ((value32 w).getD 0) (-149)
  cases h : value32 w with
  | none => exact OnGrid.zero _
  | some v => exact value32_onGrid h

theorem mc_add_comm (P : Model) (x y : F32) : (mcMachine P).add x y = (mcMachine P).add y x := by
  show fl32 false ((value32 x).getD 0 + (value32 y).getD 0) =
    fl32 false ((value32 y).getD 0 + (value32 x).getD 0)
  rw [Rat.add_comm]

theorem mc_add_zero (P : Model) (x : F32) (hx : GoodW x) : (mcMachine P).add x 0 = some x := by
  show fl32 false ((value32 x).getD 0 + (value32 (0 : F32)).getD 0) = some x
  rw [value32_zero]
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hx.1
  rw [hv]
  simp only [Option.getD_some, Rat.add_zero]
  exact fl32_value_self hv hx.2

theorem mc_add_good (P : Model) (x y o : F32) (h : (mcMachine P).add x y = some o) : GoodW o :=
  fl32_good (OnGrid.add (val_onGrid P x) (val_onGrid P y)) h

theorem mc_zero_good : GoodW 0 := by decide

end MMAlgebra.MC
