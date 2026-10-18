import TensorCore.Numerics.RoundOp

/-! Arithmetic characterization of finite FP32 encodings, and correctness of `encode32`. -/

namespace TensorCore

theorem classifyNat_fp32 (n : ℕ) : classifyNat fp32 n =
    if n / 8388608 % 256 = 255 then
      (if n % 8388608 = 0 then .infinity (n / 2147483648 != 0) else .nan)
    else if n / 8388608 % 256 = 0 then
      (if n % 8388608 = 0 then .zero (n / 2147483648 != 0)
       else .subnormal ⟨if (n / 2147483648 != 0) then -((n % 8388608 : ℕ) : ℤ)
         else ((n % 8388608 : ℕ) : ℤ), -126, 23⟩)
    else .normal ⟨if (n / 2147483648 != 0) then -((8388608 + n % 8388608 : ℕ) : ℤ)
      else ((8388608 + n % 8388608 : ℕ) : ℤ), ((n / 8388608 % 256 : ℕ) : ℤ) - 127, 23⟩ :=
  rfl

theorem classifyNat32_finite (n : ℕ) (d : Decoded)
    (h : (classifyNat fp32 n).finite = some d) : FiniteValue32 d.value := by
  rw [classifyNat_fp32] at h
  by_cases h1 : n / 8388608 % 256 = 255
  · by_cases h3 : n % 8388608 = 0 <;> simp [h1, h3, Classification.finite] at h
  · by_cases h2 : n / 8388608 % 256 = 0
    · by_cases h3 : n % 8388608 = 0
      · simp [h2, h3, Classification.finite] at h
        subst h
        exact ⟨0, -126, by decide, by decide, by decide, by simp [Decoded.value]⟩
      · simp [h2, h3, Classification.finite] at h
        subst h
        refine ⟨if (n / 2147483648 != 0) then -((n % 8388608 : ℕ) : ℤ)
          else ((n % 8388608 : ℕ) : ℤ), -126, by decide, by decide, ?_, ?_⟩
        · split <;> simp <;> omega
        · simp [Decoded.value]
    · simp [h1, h2, Classification.finite] at h
      subst h
      refine ⟨if (n / 2147483648 != 0) then -((8388608 + n % 8388608 : ℕ) : ℤ)
        else ((8388608 + n % 8388608 : ℕ) : ℤ),
        ((n / 8388608 % 256 : ℕ) : ℤ) - 127, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · split <;> simp <;> omega
      · simp [Decoded.value]

theorem decode32_finite (b : F32) (d : Decoded) (h : decode32 b = some d) :
    FiniteValue32 d.value := by
  rw [decode32_eq] at h
  exact classifyNat32_finite b.toNat d h

/-- Every value of a finite encoding has the arithmetic form. -/
theorem value32_finite (b : F32) (z : ℚ) (h : value32 b = some z) : FiniteValue32 z := by
  unfold value32 at h
  cases hd : decode32 b with
  | none => simp [hd] at h
  | some d =>
    simp [hd] at h
    subst h
    exact decode32_finite b d hd

theorem encode32_toNat (negative : Bool) (e k : ℤ) (hk0 : 0 ≤ k) (hk1 : k < 2 ^ 24)
    (he1 : -126 ≤ e) (he2 : e ≤ 127) :
    (encode32 negative e k).toNat = (if negative then 2 ^ 31 else 0) +
      (if k < 2 ^ 23 then k.toNat else (e + 127).toNat * 2 ^ 23 + (k - 2 ^ 23).toNat) := by
  unfold encode32
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  simp only [Nat.reducePow]
  split <;> split <;> omega

/-- `encode32` decodes to the intended value, and its low bit is the coefficient's parity. -/
theorem encode32_value (negative : Bool) (e k : ℤ)
    (he1 : -126 ≤ e) (he2 : e ≤ 127) (hk0 : 0 ≤ k) (hk1 : k < 2 ^ 24)
    (hsub : 2 ^ 23 ≤ k ∨ e = -126) :
    value32 (encode32 negative e k) =
      some ((if negative then -(k : ℚ) else (k : ℚ)) * pow2 (e - 23)) ∧
    (encode32 negative e k).toNat % 2 = k.toNat % 2 := by
  have htoNat := encode32_toNat negative e k hk0 hk1 he1 he2
  unfold value32
  rw [decode32_eq, htoNat, classifyNat_fp32]
  simp only [Nat.reducePow, Int.reducePow] at *
  generalize hpay : (if k < 8388608 then k.toNat
    else (e + 127).toNat * 8388608 + (k - 8388608).toNat) = pay
  generalize hsgn : (if negative then 2147483648 else 0) = sgn
  have hsgn' : sgn = 0 ∨ sgn = 2147483648 := by
    rw [← hsgn]; cases negative <;> simp
  have hpay' : pay < 2147483648 := by
    rw [← hpay]; split <;> omega
  by_cases hk : k < 8388608
  · have hpk : pay = k.toNat := by rw [← hpay]; simp [hk]
    have hsubn : e = -126 := by rcases hsub with h | h <;> omega
    subst hsubn
    have hexp : (sgn + pay) / 8388608 % 256 = 0 := by
      rcases hsgn' with h | h <;> subst h <;> omega
    have hmant : (sgn + pay) % 8388608 = pay := by
      rcases hsgn' with h | h <;> subst h <;> omega
    have hneg : ((sgn + pay) / 2147483648 != 0) = negative := by
      cases negative <;> simp at hsgn <;> subst hsgn <;> simp <;> omega
    simp only [hexp, hmant, hneg]
    by_cases hz : pay = 0
    · have hk0' : k = 0 := by omega
      subst hk0'
      simp [hz, Decoded.value, Classification.finite]
      rcases hsgn' with h | h <;> subst h <;> simp
    · simp only [hz, if_false, Nat.reduceEqDiff]
      simp [Decoded.value, hpk, Classification.finite]
      constructor
      · cases negative <;> simp [Int.max_eq_left hk0]
      · rcases hsgn' with h | h <;> subst h <;> omega
  · have hk' : 8388608 ≤ k := by omega
    have hpk : pay = (e + 127).toNat * 8388608 + (k - 8388608).toNat := by
      rw [← hpay]; simp [hk]
    have hexp : (sgn + pay) / 8388608 % 256 = (e + 127).toNat := by
      rcases hsgn' with h | h <;> subst h <;> omega
    have hexp1 : (e + 127).toNat ≠ 255 := by omega
    have hexp0 : (e + 127).toNat ≠ 0 := by omega
    have hmant : (sgn + pay) % 8388608 = (k - 8388608).toNat := by
      rcases hsgn' with h | h <;> subst h <;> omega
    have hneg : ((sgn + pay) / 2147483648 != 0) = negative := by
      cases negative <;> simp at hsgn <;> subst hsgn <;> simp <;> omega
    simp only [hexp, hmant, hneg, hexp1, hexp0, if_false]
    simp [Decoded.value, Classification.finite]
    constructor
    · have he0 : 0 ≤ e + 127 := by omega
      have hk0' : 0 ≤ k - 8388608 := by omega
      have hk' : 8388608 + (k - 8388608) = k := by omega
      cases negative <;> simp [Int.max_eq_left he0, Int.max_eq_left hk0', hk']
    · rcases hsgn' with h | h <;> subst h <;> omega

theorem encode32_ulpExponent (negative : Bool) (e k : ℤ)
    (he1 : -126 ≤ e) (he2 : e ≤ 127) (hk0 : 0 ≤ k) (hk1 : k < 2 ^ 24)
    (hsub : 2 ^ 23 ≤ k ∨ e = -126) :
    outputUlpExponent (encode32 negative e k) = e - 23 := by
  unfold outputUlpExponent
  rw [encode32_toNat negative e k hk0 hk1 he1 he2]
  simp only [Nat.reducePow, Int.reducePow, emin32] at *
  cases negative <;> by_cases hk : k < 8388608 <;>
    simp only [hk, Bool.false_eq_true, ↓reduceIte] <;> omega

end TensorCore
