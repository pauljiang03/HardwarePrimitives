import Ozaki.Ozaki2

/-! # The moduli rule of Ozaki-II, for any matrix multiplier

Ozaki-II on a matrix multiplier exact on `b`-bit vectors takes moduli at most `2^(b+1)`, so that
symmetric residues are `b`-bit integers (`natAbs_symMod_le`). Two hardware-independent pieces of the
per-variant choice of `b`, the moduli and the matrix multiplier configuration
(`OzakiTC.Ozaki2Choice`, `OzakiMC.Ozaki2Choice`):

* **the moduli** `moduliList top n`: the first `n` pairwise coprime integers at most `top`,
  largest first, chosen greedily (`moduliList_le`, `moduliList_pairwise`);
* **the moduli rule** `moduliFor b t k`: the fewest of them, with `top = 2^(b+1)`, whose product
  exceeds `2 k 2^(2P)` for `P = t + 2`. With `P = t + 2` the truncation term of Ozaki-II's error
  bound, at most `4 k max|x| max|y| 2^(−P)` (`truncProduct_error_normwise4`), is at most
  `2^-t · k · max|x| · max|y|`, the same target as Ozaki-I's slice rule (`slicesFor`); and
  `2 k 2^(2P) < M` is the reconstruction condition of `crt_eq` (`moduliFor_spec`).

Ozaki-II then makes one dot product on the matrix multiplier per modulus, against `s(s+1)/2` slice
products for Ozaki-I. -/

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

namespace Ozaki

/-- The greedy scan: from `m` downward, keep each integer coprime to every kept one, until `n` are
kept or `m < 2`. -/
def moduliAux : ℕ → ℕ → ℕ → List ℕ → List ℕ
  | 0, _, _, acc => acc.reverse
  | fuel + 1, n, m, acc =>
    if n ≤ acc.length ∨ m < 2 then acc.reverse
    else if acc.all (fun a => Nat.gcd a m == 1) then moduliAux fuel n (m - 1) (m :: acc)
    else moduliAux fuel n (m - 1) acc

/-- **The first `n` pairwise coprime integers at most `top`**, largest first. -/
def moduliList (top n : ℕ) : List ℕ := moduliAux top n top []

theorem moduliAux_le : ∀ (fuel n m : ℕ) (acc : List ℕ) (top : ℕ), m ≤ top → (∀ a ∈ acc, a ≤ top) →
    ∀ a ∈ moduliAux fuel n m acc, a ≤ top
  | 0, _, _, acc, _, _, hacc => by simpa [moduliAux] using hacc
  | fuel + 1, n, m, acc, top, hm, hacc => by
    unfold moduliAux
    split
    · simpa using hacc
    · split
      · refine moduliAux_le fuel n (m - 1) (m :: acc) top (by omega) ?_
        intro a ha; rcases List.mem_cons.mp ha with rfl | ha
        · exact hm
        · exact hacc a ha
      · exact moduliAux_le fuel n (m - 1) acc top (by omega) hacc

theorem moduliAux_pos : ∀ (fuel n m : ℕ) (acc : List ℕ), (∀ a ∈ acc, 2 ≤ a) →
    ∀ a ∈ moduliAux fuel n m acc, 2 ≤ a
  | 0, _, _, acc, hacc => by simpa [moduliAux] using hacc
  | fuel + 1, n, m, acc, hacc => by
    unfold moduliAux
    split
    · simpa using hacc
    · rename_i hstop
      split
      · refine moduliAux_pos fuel n (m - 1) (m :: acc) ?_
        intro a ha; rcases List.mem_cons.mp ha with rfl | ha
        · omega
        · exact hacc a ha
      · exact moduliAux_pos fuel n (m - 1) acc hacc

theorem moduliAux_pairwise : ∀ (fuel n m : ℕ) (acc : List ℕ), acc.Pairwise Nat.Coprime →
    (moduliAux fuel n m acc).Pairwise Nat.Coprime
  | 0, _, _, acc, hacc => by simpa [moduliAux, List.pairwise_reverse] using hacc.imp Nat.Coprime.symm
  | fuel + 1, n, m, acc, hacc => by
    unfold moduliAux
    split
    · simpa [List.pairwise_reverse] using hacc.imp Nat.Coprime.symm
    · split
      · rename_i hall
        refine moduliAux_pairwise fuel n (m - 1) (m :: acc) ?_
        refine List.pairwise_cons.mpr ⟨fun a ha => ?_, hacc⟩
        have := List.all_eq_true.mp hall a ha
        simp only [beq_iff_eq] at this
        exact Nat.Coprime.symm this
      · exact moduliAux_pairwise fuel n (m - 1) acc hacc

/-- Every greedy modulus is at most `top`. -/
theorem moduliList_le (top n : ℕ) : ∀ m ∈ moduliList top n, m ≤ top :=
  moduliAux_le top n top [] top (Nat.le_refl _) (by simp)

/-- The greedy moduli are at least `2` and pairwise coprime. -/
theorem moduliList_pairwise (top n : ℕ) :
    (∀ m ∈ moduliList top n, 2 ≤ m) ∧ (moduliList top n).Pairwise Nat.Coprime :=
  ⟨moduliAux_pos top n top [] (by simp), moduliAux_pairwise top n top [] List.Pairwise.nil⟩

/-- The basis of the first `n` greedy moduli at most `2^(b+1)`. -/
def moduliBasis (b n : ℕ) : CRTBasis := crtBasis (moduliList (2 ^ (b + 1)) n)

/-- **The moduli rule**: the fewest greedy moduli at most `2^(b+1)` (up to `64`) whose product
exceeds `2 k 2^(2(t+2))`; `0` if there is none. -/
def moduliFor (b t k : ℕ) : ℕ :=
  ((List.range' 1 64).find? fun n =>
    decide (2 * k * (2 ^ (t + 2) * 2 ^ (t + 2)) < (moduliBasis b n).modulus)).getD 0

/-- **The moduli rule meets the reconstruction condition**: with `n = moduliFor b t k > 0` moduli and
`P = t + 2`, every vector of at most `k` entries has `2 · length · 2^(2P) < M`. -/
theorem moduliFor_spec {b t k : ℕ} (hn : 0 < moduliFor b t k) {L : ℕ} (hL : L ≤ k) :
    2 * L * (2 ^ (t + 2) * 2 ^ (t + 2)) < (moduliBasis b (moduliFor b t k)).modulus := by
  unfold moduliFor at hn ⊢
  cases h : (List.range' 1 64).find? fun n =>
      decide (2 * k * (2 ^ (t + 2) * 2 ^ (t + 2)) < (moduliBasis b n).modulus) with
  | none => rw [h] at hn; simp at hn
  | some n =>
    simp only [Option.getD_some]
    have h' := List.find?_some (p := fun n =>
      decide (2 * k * (2 ^ (t + 2) * 2 ^ (t + 2)) < (moduliBasis b n).modulus)) h
    have := of_decide_eq_true h'
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hL)) this

/-- Every modulus of the rule is at most `2^(b+1)`. -/
theorem moduliBasis_le (b n : ℕ) : ∀ m ∈ (moduliBasis b n).moduli, m ≤ 2 ^ (b + 1) :=
  moduliList_le _ _

end Ozaki
