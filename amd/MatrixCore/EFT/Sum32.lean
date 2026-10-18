import MatrixCore.MC

/-! # Exact FP32 additions

FP32 addition on values, left-to-right FP32 summation, and when it is exact: all bits on one
grid, within one 24-bit span inside the FP32 range. -/

namespace MatrixCore

/-- FP32 addition on values: the RNE result, `none` on overflow. -/
def fp32Add (x y : ℚ) : Option ℚ := (rne32 (x + y)).bind value32

def naiveSum32From : ℚ → List ℚ → Option ℚ
  | acc, [] => some acc
  | acc, t :: ts => (fp32Add acc t).bind fun s => naiveSum32From s ts

/-- Left-to-right FP32 summation, starting from zero. -/
def naiveSum32 (ts : List ℚ) : Option ℚ := naiveSum32From 0 ts

/-- `x` is an FP32 value: RNE returns it unchanged. -/
def representable32 (x : ℚ) : Bool := (rne32 x).bind value32 == some x

/-- Exponent of the last bit of an FP32 value: `normExp |d| − 23`, or `−149` for zero. -/
def ulpExp32 (d : ℚ) : ℤ := if d = 0 then -149 else normExp (absQ d) - 23

/-- `⌈log₂ n⌉`, the carry bits of `n` summands. -/
def ceilLog2 (n : ℕ) : ℕ := if n ≤ 1 then 0 else (n - 1).log2 + 1

/-! ## Exact additions -/

theorem FiniteValue32.abs_le {y : ℚ} (h : FiniteValue32 y) : absQ y ≤ maxFinite32 := by
  obtain ⟨k, e, _, he2, hk, rfl⟩ := h
  rw [absQ_mul_pos _ _ (pow2_pos _), absQ_intCast]
  have hk' : ((k.natAbs : ℕ) : ℚ) ≤ 16777215 := by
    have : k.natAbs ≤ 16777215 := by omega
    exact_mod_cast this
  have hg : pow2 (e - 23) ≤ pow2 104 := pow2_le_of_le (by omega)
  unfold maxFinite32
  exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_left hg Rat.natCast_nonneg)
    (Rat.mul_le_mul_of_nonneg_right hk' (Rat.le_of_lt (pow2_pos _)))

theorem maxFinite32_lt_overflow : maxFinite32 < overflowThreshold32 := by decide +kernel

theorem FiniteValue32.abs_lt {y : ℚ} (h : FiniteValue32 y) : absQ y < overflowThreshold32 :=
  Std.lt_of_le_of_lt h.abs_le maxFinite32_lt_overflow

theorem fp32Add_exact {x y : ℚ} (h : FiniteValue32 (x + y)) : fp32Add x y = some (x + y) := by
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp ((rne32_isSome_iff (x + y)).mpr h.abs_lt)
  unfold fp32Add
  rw [hw, Option.bind_some, rne32_value hw, rneValue_of_finiteValue32 h]

theorem pow2_128 : pow2 128 = ((2 ^ 24 : ℕ) : ℚ) * pow2 104 := by
  rw [← pow2_natCast, ← pow2_add]; congr 1

theorem grid_finiteValue32 (k ℓ : ℤ) (h1 : -149 ≤ ℓ) (hk : k.natAbs < 2 ^ 24)
    (hr : ((k.natAbs : ℕ) : ℚ) * pow2 ℓ < pow2 128) : FiniteValue32 ((k : ℚ) * pow2 ℓ) := by
  by_cases h2 : ℓ ≤ 104
  · exact ⟨k, ℓ + 23, by omega, by omega, by simpa using hk, by rw [show ℓ + 23 - 23 = ℓ by omega]⟩
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, ℓ = 104 + n := ⟨(ℓ - 104).toNat, by omega⟩
    have hv : (k : ℚ) * pow2 ℓ = ((k * 2 ^ n : ℤ) : ℚ) * pow2 104 := by
      rw [hn, pow2_add, ← intCast_mul_pow2_nat]
      grind
    have hlt : ((k.natAbs * 2 ^ n : ℕ) : ℚ) < ((2 ^ 24 : ℕ) : ℚ) := by
      have e1 : ((k.natAbs : ℕ) : ℚ) * pow2 ℓ = ((k.natAbs * 2 ^ n : ℕ) : ℚ) * pow2 104 := by
        rw [hn, pow2_add, Rat.natCast_mul, ← pow2_natCast]
        grind
      rw [e1, pow2_128] at hr
      exact Rat.lt_of_mul_lt_mul_right hr (Rat.le_of_lt (pow2_pos 104))
    have hlt' : k.natAbs * 2 ^ n < 2 ^ 24 := by exact_mod_cast hlt
    refine ⟨k * 2 ^ n, 127, by omega, by omega, ?_, ?_⟩
    · rw [Int.natAbs_mul, Int.natAbs_pow]; simpa using hlt'
    · rw [hv]; rfl

theorem naiveSum32From_exact (ℓ : ℤ) (h1 : -149 ≤ ℓ) (a : ℤ) (zs : List ℤ)
    (hbound : a.natAbs + magnitudeSum zs < 2 ^ 24)
    (hrange : ((a.natAbs + magnitudeSum zs : ℕ) : ℚ) * pow2 ℓ < pow2 128) :
    naiveSum32From ((a : ℚ) * pow2 ℓ) (zs.map fun (z : ℤ) => (z : ℚ) * pow2 ℓ) =
      some (((a + sumZ zs : ℤ) : ℚ) * pow2 ℓ) := by
  induction zs generalizing a with
  | nil => simp [naiveSum32From, sumZ]
  | cons z zs ih =>
    have hsum : (a : ℚ) * pow2 ℓ + (z : ℚ) * pow2 ℓ = ((a + z : ℤ) : ℚ) * pow2 ℓ := by
      rw [Rat.intCast_add]; grind
    have habs := Int.natAbs_add_le a z
    have hnext : (a + z).natAbs + magnitudeSum zs ≤ a.natAbs + magnitudeSum (z :: zs) := by
      simp only [magnitudeSum]; omega
    have hrnext : (((a + z).natAbs + magnitudeSum zs : ℕ) : ℚ) * pow2 ℓ < pow2 128 :=
      Std.lt_of_le_of_lt (Rat.mul_le_mul_of_nonneg_right (Rat.natCast_le_natCast.mpr hnext)
        (Rat.le_of_lt (pow2_pos _))) hrange
    have hrstep : (((a + z).natAbs : ℕ) : ℚ) * pow2 ℓ < pow2 128 :=
      Std.lt_of_le_of_lt (Rat.mul_le_mul_of_nonneg_right
        (Rat.natCast_le_natCast.mpr (Nat.le_add_right _ _)) (Rat.le_of_lt (pow2_pos _))) hrnext
    have hstep : fp32Add ((a : ℚ) * pow2 ℓ) ((z : ℚ) * pow2 ℓ) =
        some (((a + z : ℤ) : ℚ) * pow2 ℓ) := by
      rw [← hsum]
      apply fp32Add_exact
      rw [hsum]
      exact grid_finiteValue32 _ ℓ h1 (by simp only [magnitudeSum] at hbound; omega) hrstep
    have ih' := ih (a + z) (by simp only [magnitudeSum] at hbound; omega) hrnext
    simp only [List.map_cons, naiveSum32From, hstep, Option.bind_some, ih']
    rw [show a + z + sumZ zs = a + sumZ (z :: zs) by simp only [sumZ]; omega]

/-- FP32 summation on the grid `2^ℓ` is exact when the coefficients need fewer than 24 bits. -/
theorem naiveSum32_exact (ℓ : ℤ) (h1 : -149 ≤ ℓ) (zs : List ℤ)
    (hbound : magnitudeSum zs < 2 ^ 24) (hrange : (magnitudeSum zs : ℚ) * pow2 ℓ < pow2 128) :
    naiveSum32 (zs.map fun (z : ℤ) => (z : ℚ) * pow2 ℓ) = some ((sumZ zs : ℚ) * pow2 ℓ) := by
  have h := naiveSum32From_exact ℓ h1 0 zs (by simpa using hbound) (by simpa using hrange)
  unfold naiveSum32
  simpa using h

theorem le_two_pow_ceilLog2 (n : ℕ) : n ≤ 2 ^ ceilLog2 n := by
  unfold ceilLog2
  split
  · simp; omega
  · have := Nat.lt_log2_self (n := n - 1)
    omega

/-- FP32 summation is exact when all bits fit one 24-bit span in the FP32 range. -/
theorem naiveSum32_exact_of_bitSpan (b ℓ : ℤ) (h1 : -149 ≤ ℓ) (zs : List ℤ)
    (hterm : ∀ z ∈ zs, absQ ((z : ℚ) * pow2 ℓ) < pow2 (b + 1))
    (hspan : b - ℓ + 1 + (ceilLog2 zs.length : ℤ) ≤ 24)
    (htop : b + 1 + (ceilLog2 zs.length : ℤ) ≤ 128) :
    naiveSum32 (zs.map fun (z : ℤ) => (z : ℚ) * pow2 ℓ) = some ((sumZ zs : ℚ) * pow2 ℓ) := by
  apply naiveSum32_exact ℓ h1
  · by_cases hb : ℓ ≤ b + 1
    · obtain ⟨w, hw⟩ : ∃ w : ℕ, b + 1 = ℓ + w := ⟨(b + 1 - ℓ).toNat, by omega⟩
      have hz : ∀ z ∈ zs, z.natAbs < 2 ^ w := by
        intro z hz'
        have h := hterm z hz'
        rw [absQ_mul_pos _ _ (pow2_pos _), absQ_intCast, hw, pow2_add, pow2_natCast,
          Rat.mul_comm (pow2 ℓ)] at h
        exact_mod_cast Rat.lt_of_mul_lt_mul_right h (Rat.le_of_lt (pow2_pos ℓ))
      have := coefficient_width_sufficient zs w (ceilLog2 zs.length) hz (le_two_pow_ceilLog2 _)
      have hle : 2 ^ ((w + ceilLog2 zs.length + 1) - 1) ≤ 2 ^ 24 :=
        Nat.pow_le_pow_right (by decide) (by omega)
      omega
    · have hz : ∀ z ∈ zs, z.natAbs = 0 := by
        intro z hz'
        have h := hterm z hz'
        rw [absQ_mul_pos _ _ (pow2_pos _), absQ_intCast] at h
        have h2 := pow2_le_of_le (show b + 1 ≤ ℓ by omega)
        have h3 : ((z.natAbs : ℕ) : ℚ) < 1 := by
          apply Rat.not_le.mp
          intro h4
          have := Rat.mul_le_mul_of_nonneg_right h4 (Rat.le_of_lt (pow2_pos ℓ))
          grind
        have : z.natAbs < 1 := by exact_mod_cast h3
        omega
      have : magnitudeSum zs = 0 := by
        have := magnitudeSum_le_length_mul zs 0 (fun z hz' => Nat.le_of_eq (hz z hz'))
        omega
      rw [this]; decide
  · by_cases hb : ℓ ≤ b + 1
    · obtain ⟨w, hw⟩ : ∃ w : ℕ, b + 1 = ℓ + w := ⟨(b + 1 - ℓ).toNat, by omega⟩
      have hz : ∀ z ∈ zs, z.natAbs < 2 ^ w := by
        intro z hz'
        have h := hterm z hz'
        rw [absQ_mul_pos _ _ (pow2_pos _), absQ_intCast, hw, pow2_add, pow2_natCast,
          Rat.mul_comm (pow2 ℓ)] at h
        exact_mod_cast Rat.lt_of_mul_lt_mul_right h (Rat.le_of_lt (pow2_pos ℓ))
      have hm := coefficient_width_sufficient zs w (ceilLog2 zs.length) hz (le_two_pow_ceilLog2 _)
      rw [show w + ceilLog2 zs.length + 1 - 1 = w + ceilLog2 zs.length by omega] at hm
      have hmq : (magnitudeSum zs : ℚ) < ((2 ^ (w + ceilLog2 zs.length) : ℕ) : ℚ) := by
        exact_mod_cast hm
      have h2 := Rat.mul_lt_mul_of_pos_right hmq (pow2_pos ℓ)
      rw [← pow2_natCast, ← pow2_add] at h2
      exact Std.lt_of_lt_of_le h2 (pow2_le_of_le (by push_cast; omega))
    · have hz : ∀ z ∈ zs, z.natAbs = 0 := by
        intro z hz'
        have h := hterm z hz'
        rw [absQ_mul_pos _ _ (pow2_pos _), absQ_intCast] at h
        have h2 := pow2_le_of_le (show b + 1 ≤ ℓ by omega)
        have h3 : ((z.natAbs : ℕ) : ℚ) < 1 := by
          apply Rat.not_le.mp
          intro h4
          have := Rat.mul_le_mul_of_nonneg_right h4 (Rat.le_of_lt (pow2_pos ℓ))
          grind
        have : z.natAbs < 1 := by exact_mod_cast h3
        omega
      have : magnitudeSum zs = 0 := by
        have := magnitudeSum_le_length_mul zs 0 (fun z hz' => Nat.le_of_eq (hz z hz'))
        omega
      rw [this]
      rw [show ((0 : ℕ) : ℚ) = 0 by simp, Rat.zero_mul]
      exact pow2_pos 128

theorem representable32_finite {x : ℚ} (h : representable32 x = true) : FiniteValue32 x := by
  unfold representable32 at h
  cases hr : rne32 x with
  | none => simp [hr] at h
  | some w =>
    simp only [hr, Option.bind_some, beq_iff_eq] at h
    exact value32_finiteValue h

/-! ## The last bit of an FP32 value -/

theorem ulpExp32_ge (d : ℚ) : -149 ≤ ulpExp32 d := by
  unfold ulpExp32 normExp; split <;> omega

theorem normExp_pow2 {a : ℤ} (ha : -126 ≤ a) : normExp (pow2 a) = a := by
  unfold normExp
  rw [log2Floor_eq (Rat.le_refl) (pow2_lt_of_lt (by omega))]
  omega

theorem normExp_decode32 {w : F32} {u : Unpacked} (h : fp32.decode w = .finite u) (hm : u.m ≠ 0) :
    normExp (absQ u.value) = u.e := by
  obtain ⟨ht, hm24, he1, _, hn⟩ := decode32_finite_fields h
  have hv : absQ u.value = (u.m : ℚ) * pow2 (u.e - 23) := by rw [Unpacked.absQ_value, ht]; rfl
  have hq := pow2_pos (u.e - 23)
  have e1 : pow2 (u.e + 1) = ((16777216 : ℕ) : ℚ) * pow2 (u.e - 23) := by
    rw [pow2_split _ 24, show u.e + 1 - ((24 : ℕ) : ℤ) = u.e - 23 by omega]
  have e2 : pow2 u.e = ((8388608 : ℕ) : ℚ) * pow2 (u.e - 23) := by
    rw [pow2_split _ 23, show u.e - ((23 : ℕ) : ℤ) = u.e - 23 by omega]
  have hup : absQ u.value < pow2 (u.e + 1) := by
    rw [hv, e1]
    exact Rat.mul_lt_mul_of_pos_right (by exact_mod_cast hm24) hq
  by_cases hbig : 8388608 ≤ u.m
  · have hlo : pow2 u.e ≤ absQ u.value := by
      rw [hv, e2]
      exact Rat.mul_le_mul_of_nonneg_right (by exact_mod_cast hbig) (Rat.le_of_lt hq)
    unfold normExp
    rw [log2Floor_eq hlo hup]
    omega
  · have he : u.e = -126 := by omega
    have hpos : 0 < absQ u.value := absQ_pos (fun h0 => hm ((Unpacked.value_eq_zero_iff u).mp h0))
    have hsmall : absQ u.value < pow2 u.e := by
      rw [hv, e2]
      exact Rat.mul_lt_mul_of_pos_right (by exact_mod_cast (show u.m < 8388608 by omega)) hq
    obtain ⟨hl, _⟩ := log2Floor_spec hpos
    have : log2Floor (absQ u.value) < u.e := pow2_lt_iff.mp (Std.lt_of_le_of_lt hl hsmall)
    unfold normExp
    omega

theorem value32_onGrid_ulpExp {w : F32} {d : ℚ} (h : value32 w = some d) :
    OnGrid d (ulpExp32 d) := by
  unfold value32 at h
  cases hd : fp32.decode w with
  | finite u =>
    rw [hd] at h
    simp only [Datum.toFinite, Option.map_some, Option.some.injEq] at h
    subst h
    unfold ulpExp32
    split
    · rename_i h0; rw [h0]; exact OnGrid.zero _
    · rename_i h0
      have hm : u.m ≠ 0 := fun hm => h0 ((Unpacked.value_eq_zero_iff u).mpr hm)
      rw [normExp_decode32 hd hm]
      have := Unpacked.value_onGrid u
      rwa [(decode32_finite_fields hd).1] at this
  | infinity _ => rw [hd] at h; simp [Datum.toFinite] at h
  | nan => rw [hd] at h; simp [Datum.toFinite] at h

theorem absQ_rneValue (x : ℚ) : absQ (rneValue x) = rneMagnitude (absQ x) := by
  unfold rneValue
  have h := rneMagnitude_nonneg (absQ_nonneg x)
  split
  · rw [absQ_neg, absQ_of_nonneg h]
  · rw [absQ_of_nonneg h]

theorem rneValue_error_ulp (x : ℚ) : absQ (x - rneValue x) ≤ pow2 (ulpExp32 (rneValue x) - 1) := by
  by_cases hx : x = 0
  · subst hx
    rw [rneValue_zero, show absQ ((0 : ℚ) - 0) = 0 by decide +kernel]
    exact Rat.le_of_lt (pow2_pos _)
  have h1 := rneValue_error x
  unfold halfUlp32 at h1
  rw [if_neg hx] at h1
  refine Rat.le_trans h1 (pow2_le_of_le ?_)
  have ha := absQ_pos hx
  obtain ⟨_, _, hge⟩ := normExp_bounds ha
  unfold ulpExp32
  split
  · rename_i h0
    by_cases hn : normExp (absQ x) = -126
    · omega
    · exfalso
      have := (rneMagnitude_bounds ha).2 hn
      rw [← absQ_rneValue, h0, show absQ (0 : ℚ) = 0 from rfl] at this
      exact Rat.not_le.mpr (pow2_pos _) this
  · rename_i h0
    by_cases hn : normExp (absQ x) = -126
    · have := (normExp_bounds (absQ_pos h0)).2.2; omega
    · have hb := (rneMagnitude_bounds ha).2 hn
      rw [← absQ_rneValue] at hb
      have := normExp_mono (pow2_pos _) hb
      rw [normExp_pow2 hge] at this
      omega

theorem rneValue_eq_of_onGrid {x : ℚ} {w : F32} (hw : rne32 x = some w)
    (hg : OnGrid x (ulpExp32 (rneValue x))) : rneValue x = x := by
  have hd := value32_onGrid_ulpExp (rne32_value hw)
  have h0 := onGrid_eq_zero (hg.sub hd)
    (Std.lt_of_le_of_lt (rneValue_error_ulp x) (pow2_lt_of_lt (by omega)))
  grind

end MatrixCore
