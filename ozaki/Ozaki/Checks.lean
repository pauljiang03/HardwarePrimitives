import Ozaki.Parameters

/-! # Runtime checks of the Z3 models as theorems

Small facts that the Z3 models check at runtime on their test matrices, stated for every input:

* `slice_product_bound` (Ozaki-I `[S2.2]`): a slice product is at most `k 2^(2b)`, which is
  `2^24` in the Z3 configuration;
* `scaleShift_spec` (Ozaki-II `[S1.1]`): the scaled row maximum lies in `(2^(P−1), 2^P]`;
* `natAbs_truncProduct_le` (Ozaki-II `[S1.6]`): `|a · c| ≤ k 2^(2P)`;
* `natAbs_residueProduct_le` (Ozaki-II `[S3.2]`): a residue product is at most `k ⌊m/2⌋²`;
* `z3_residue_exactnessBound` (Ozaki-II `[S0.5]`): `k ⌊m/2⌋² ≤ 2^24` for the Z3 moduli;
* `crt_dvd_sub` (Ozaki-II `[S4.2]`): the reconstruction is congruent to every residue. -/

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

namespace Ozaki

/-- **Slice products are small** (Ozaki-I `[S2.2]`). The product of slice `t` of `x` and slice `u`
of `y` is at most `k 2^(2b)` in magnitude. -/
theorem slice_product_bound (b s : ℕ) (x y : List ℚ) {t u : ℕ}
    (ht : t < s) (hu : u < s) :
    (dotZ ((split b s x).1.getD t default).coeffs ((split b s y).1.getD u default).coeffs).natAbs ≤
      x.length * (2 ^ b * 2 ^ b) := by
  obtain ⟨hlx, hcx, _⟩ := split_length b s x
  obtain ⟨hly, _, _⟩ := split_length b s y
  have hmx := getD_mem (l := (split b s x).1) (t := t) (by omega)
  have hmy := getD_mem (l := (split b s y).1) (t := u) (by omega)
  refine Nat.le_trans (natAbs_dotZ_le _ _) ?_
  have := dotAbs_le _ _ _ _ (split_coeff_bound b s x _ hmx) (split_coeff_bound b s y _ hmy)
  rwa [hcx _ hmx] at this

/-- In the Z3 configuration a slice product is at most `4 · 2^22 = 2^24`. -/
theorem z3_slice_product_bound {x y : List ℚ} (hk : x.length = z3K)
    {t u : ℕ} (ht : t < z3Slices) (hu : u < z3Slices) :
    (dotZ ((split z3SliceBits z3Slices x).1.getD t default).coeffs
      ((split z3SliceBits z3Slices y).1.getD u default).coeffs).natAbs ≤ 2 ^ 24 := by
  have := slice_product_bound z3SliceBits z3Slices x y ht hu
  rw [hk, z3_slice_exactnessBound] at this
  exact this

/-- **The scaled row maximum** (Ozaki-II `[S1.1]`): `2^(P−1) < max|x| · 2^sₓ ≤ 2^P`. -/
theorem scaleShift_spec (P : ℕ) {x : List ℚ} (hx : maxAbs x ≠ 0) :
    2 ^ ((P : ℤ) - 1) < maxAbs x * 2 ^ scaleShift P x ∧ maxAbs x * 2 ^ scaleShift P x ≤ 2 ^ (P : ℤ) := by
  have hpos : 0 < maxAbs x := by have := maxAbs_nonneg x; grind
  obtain ⟨h1, h2⟩ := ceilLog2_spec hpos
  have hs : scaleShift P x = (P : ℤ) - ceilLog2 (maxAbs x) := by unfold scaleShift; rw [if_neg hx]
  rw [hs]
  have hp := two_pow_pos ((P : ℤ) - ceilLog2 (maxAbs x))
  constructor
  · have := Rat.mul_lt_mul_of_pos_right h1 hp
    rwa [← two_pow_add, show ceilLog2 (maxAbs x) - 1 + ((P : ℤ) - ceilLog2 (maxAbs x)) = (P : ℤ) - 1
      by omega] at this
  · have := Rat.mul_le_mul_of_nonneg_right h2 (Rat.le_of_lt hp)
    rwa [← two_pow_add, show ceilLog2 (maxAbs x) + ((P : ℤ) - ceilLog2 (maxAbs x)) = (P : ℤ)
      by omega] at this

/-- **The integer product is small** (Ozaki-II `[S1.6]`): `|a · c| ≤ k 2^(2P)`. -/
theorem natAbs_truncProduct_le (P : ℕ) (x y : List ℚ) :
    (dotZ (scaleTrunc (scaleShift P x) x) (scaleTrunc (scaleShift P y) y)).natAbs ≤
      x.length * (2 ^ P * 2 ^ P) := by
  refine Nat.le_trans (natAbs_dotZ_le _ _) ?_
  have := dotAbs_le _ _ _ _ (scaleTrunc_bound P x) (scaleTrunc_bound P y)
  rwa [scaleTrunc_length] at this

/-- **A residue product is small** (Ozaki-II `[S3.2]`): `|Σ (aᵢ mod m)(cᵢ mod m)| ≤ k ⌊m/2⌋²`. -/
theorem natAbs_residueProduct_le {m : ℕ} (hm : 0 < m) (a c : List ℤ) :
    (dotZ (a.map fun z => symMod z m) (c.map fun z => symMod z m)).natAbs ≤
      a.length * (m / 2 * (m / 2)) := by
  have hres : ∀ l : List ℤ, ∀ z ∈ l.map fun z => symMod z m, z.natAbs ≤ m / 2 := by
    intro l z hz
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp hz
    have := natAbs_symMod_le w hm
    omega
  refine Nat.le_trans (natAbs_dotZ_le _ _) ?_
  have := dotAbs_le _ _ _ _ (hres a) (hres c)
  rwa [List.length_map] at this

/-- **The Z3 residue products fit binary32** (Ozaki-II `[S0.5]`): `k ⌊m/2⌋² ≤ 2^24` for every
modulus of `{4096, 4095, 4093, 4091}`. -/
theorem z3_residue_exactnessBound : ∀ m ∈ z3Moduli, z3K * (m / 2 * (m / 2)) ≤ 2 ^ 24 := by decide

theorem dvd_prod_of_mem {m : ℕ} : ∀ {ms : List ℕ}, m ∈ ms → m ∣ ms.prod
  | _ :: ms, h => by
    rw [List.prod_cons]
    rcases List.mem_cons.mp h with h | h
    · subst h; exact Nat.dvd_mul_right _ _
    · exact Nat.dvd_trans (dvd_prod_of_mem h) (Nat.dvd_mul_left _ _)

/-- **Reconstruction matches every residue** (Ozaki-II `[S4.2]`): with a valid basis, the
reconstructed integer is congruent to `rⱼ` modulo `mⱼ`, for every `j`. -/
theorem crt_dvd_sub {B : CRTBasis} (hB : B.Valid) {rs : List ℤ} (hlen : rs.length = B.moduli.length)
    (j : Fin B.moduli.length) : (B.moduli[j] : ℤ) ∣ crt B rs - rs.getD j 0 := by
  obtain ⟨hwl, _, _, hw⟩ := hB
  have hsel := dvd_dotZ_sub (B.moduli[j] : ℤ) B.weights rs j (by rw [hwl, hlen])
    (by rw [hwl]; exact j.2)
    (fun l hl => hw ⟨l, by rw [← hwl]; exact hl⟩ j |> fun h => by simpa [Fin.ext_iff] using h)
  have hM : (B.moduli[j] : ℤ) ∣ (B.modulus : ℤ) :=
    Int.natCast_dvd_natCast.mpr (dvd_prod_of_mem (List.getElem_mem j.2))
  have hsym := symMod_dvd (dotZ B.weights rs) B.modulus
  unfold crt
  have : symMod (dotZ B.weights rs) B.modulus - rs.getD j 0 =
      (dotZ B.weights rs - rs.getD j 0) - (dotZ B.weights rs - symMod (dotZ B.weights rs) B.modulus) := by
    omega
  rw [this]
  exact Int.dvd_sub hsel (Int.dvd_trans hM hsym)

end Ozaki
