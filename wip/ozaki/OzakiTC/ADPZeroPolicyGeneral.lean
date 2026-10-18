import OzakiTC.ADPZeroPolicy
import OzakiTC.IEEE
import Ozaki.SharpBounds
import Ozaki.Bounded

/-! # ADP's unsafe zero policies, in general

`OzakiTC/ADPZeroPolicy.lean` runs the routine with the Z3 model's unsafe zero policies on
recorded inputs. Here the failures are proven for whole families of inputs:

* **Skipping zeros is unsafe for every block size `n ≥ 2` and every inner dimension `k ≥ 2`**
  (`adpPolicy_skip_wrong`), and safe for `n = 1`, where it is the exact estimate
  (`coarseEstSkip_one`, `escCoarsePolicy_skip_one`).
* **Giving zeros the exponent `−1022` is unsafe for every block size `n ≥ 1` and every `k ≥ 2`**
  (`adpPolicy_field0_wrong`).

The family is `x = (2^a, 1, 0, …, 0)` against `y = (0, 2^d, 0, …, 0)`: the only nonzero product is
`2^d`, so the exact ESC is `a` (`escExact_zp`). Skipping zeros pairs `x₁ = 2^a` with the block
minimum of the nonzero `y`'s, `d`, so the estimate is at least `a + d` and the computed ESC at
most `0`; giving zeros `−1022` pairs it with `−1022`, so the computed ESC is at most `d + 1022`.
Either way the fixed point has at most `78` bits, `x₂ = 1` is shifted below the point and lost,
and the routine emulates and returns `0` for the nonzero product `2^d`, breaking Grade A
(`gradeAEntry_zp_zero`). The binary64 words exist for every member of the family
(`exists_decode_zp`). The paper's policy, zeros as `−∞`, never underestimates the ESC
(`Ozaki.ADP.escCoarse_ge`), and `adp` meets Grade A on every input of normal entries
(`adp_accuracy`). -/

open TensorCore

namespace Ozaki.TC

open ADP

/-! ## Exponent lists -/

theorem maxE_replicate_none : ∀ m : ℕ, maxE (List.replicate m (none : Exp)) = none
  | 0 => rfl
  | m + 1 => by
    simp only [List.replicate_succ, maxE, List.foldr_cons]
    have := maxE_replicate_none m
    simp only [maxE] at this
    rw [this]; rfl

theorem zipWith_eAdd_replicate_none : ∀ m : ℕ,
    List.zipWith eAdd (List.replicate m (none : Exp)) (List.replicate m none) = List.replicate m none
  | 0 => rfl
  | m + 1 => by
    simp only [List.replicate_succ, List.zipWith_cons_cons]
    rw [zipWith_eAdd_replicate_none m]; rfl

/-- `some c` is below the minimum of a nonempty list of values all above `some c`. -/
theorem eLe_minE {c : ℤ} : ∀ {l : List Exp}, l ≠ [] → (∀ e ∈ l, eLe (some c) e) →
    eLe (some c) (minE l)
  | [], h, _ => absurd rfl h
  | [e], _, h => by simpa only [minE] using h e List.mem_cons_self
  | e :: e' :: l, _, h => by
    have h1 := h e List.mem_cons_self
    have h2 := eLe_minE (l := e' :: l) (by simp) (fun x hx => h x (List.mem_cons_of_mem _ hx))
    show eLe (some c) (eMin e (minE (e' :: l)))
    cases e with
    | none => simp [eLe] at h1
    | some a =>
      cases hm : minE (e' :: l) with
      | none => rw [hm] at h2; simp [eLe] at h2
      | some b =>
        rw [hm] at h2
        simp only [eMin, eLe] at h1 h2 ⊢
        omega

/-- The coarsened estimate is at least the contribution of the first pair of blocks. -/
theorem coarseEstWith_ge_head (rep : List Exp → Exp × Exp) (n : ℕ) {ex ey : List Exp}
    (hx : ex ≠ []) (hy : ey ≠ []) :
    eLe (eAdd (rep (ex.take n)).1 (rep (ey.take n)).2) (coarseEstWith rep n ex ey) := by
  unfold coarseEstWith
  obtain ⟨Lx, hLx⟩ : ∃ L, ex.length = L + 1 := ⟨ex.length - 1, by
    have := List.length_pos_iff.mpr hx; omega⟩
  obtain ⟨Ly, hLy⟩ : ∃ L, ey.length = L + 1 := ⟨ey.length - 1, by
    have := List.length_pos_iff.mpr hy; omega⟩
  rw [hLx, hLy]
  simp only [blocksOf, if_neg hx, if_neg hy, List.zipWith_cons_cons]
  refine eLe_trans (eLe_eMax_left _ _) (le_maxE List.mem_cons_self)

/-! ## The family -/

/-- `x = (2^a, 1, 0, …, 0)` of length `k`. -/
def zpX (a : ℤ) (k : ℕ) : List ℚ := 2 ^ a :: 1 :: List.replicate (k - 2) 0

/-- `y = (0, 2^d, 0, …, 0)` of length `k`. -/
def zpY (d : ℤ) (k : ℕ) : List ℚ := 0 :: 2 ^ d :: List.replicate (k - 2) 0

theorem zpX_length (a : ℤ) {k : ℕ} (hk : 2 ≤ k) : (zpX a k).length = k := by
  simp [zpX]; omega

theorem zpY_length (d : ℤ) {k : ℕ} (hk : 2 ≤ k) : (zpY d k).length = k := by
  simp [zpY]; omega

theorem expOf_two_pow {a : ℤ} (ha : -1022 ≤ a) : expOf ((2 : ℚ) ^ a) = some a := by
  unfold expOf exp64
  rw [if_neg (two_pow_ne_zero a), abs_two_pow,
    floorLog2_eq (Rat.le_refl) (two_pow_lt (by omega))]
  congr 1; omega

theorem expOf_zero : expOf (0 : ℚ) = none := by simp [expOf]

theorem expOf_one : expOf (1 : ℚ) = some 0 := by
  rw [show (1 : ℚ) = 2 ^ (0 : ℤ) from rfl]; exact expOf_two_pow (by decide)

theorem expsOf_zpX {a : ℤ} (ha : -1022 ≤ a) (k : ℕ) :
    expsOf (zpX a k) = some a :: some 0 :: List.replicate (k - 2) none := by
  simp only [expsOf, zpX, List.map_cons, List.map_replicate, expOf_two_pow ha, expOf_one,
    expOf_zero]

theorem expsOf_zpY {d : ℤ} (hd : -1022 ≤ d) (k : ℕ) :
    expsOf (zpY d k) = none :: some d :: List.replicate (k - 2) none := by
  simp only [expsOf, zpY, List.map_cons, List.map_replicate, expOf_two_pow hd, expOf_zero]

theorem maxE_expsOf_zpX {a : ℤ} (ha : 0 ≤ a) (k : ℕ) : maxE (expsOf (zpX a k)) = some a := by
  rw [expsOf_zpX (by omega)]
  have := maxE_replicate_none (k - 2)
  simp only [maxE, List.foldr_cons] at this ⊢
  rw [this]
  simp only [eMax]
  congr 1; omega

theorem maxE_expsOf_zpY {d : ℤ} (hd : -1022 ≤ d) (k : ℕ) : maxE (expsOf (zpY d k)) = some d := by
  rw [expsOf_zpY hd]
  have := maxE_replicate_none (k - 2)
  simp only [maxE, List.foldr_cons] at this ⊢
  rw [this]; rfl

theorem fExact_zp {a d : ℤ} (ha : -1022 ≤ a) (hd : -1022 ≤ d) (k : ℕ) :
    fExact (expsOf (zpX a k)) (expsOf (zpY d k)) = some d := by
  unfold fExact
  rw [expsOf_zpX ha, expsOf_zpY hd]
  simp only [List.zipWith_cons_cons, zipWith_eAdd_replicate_none]
  have := maxE_replicate_none (k - 2)
  simp only [maxE, List.foldr_cons] at this ⊢
  rw [this]
  simp only [eAdd, eMax]
  congr 1; omega

/-- **The exact ESC of the family is `a`**: the largest possible product is `2^(a+d)`, the
largest actual one `2^d`. -/
theorem escExact_zp {a d : ℤ} (ha : 0 ≤ a) (hd : -1022 ≤ d) (k : ℕ) :
    escExact (zpX a k) (zpY d k) = a := by
  unfold escExact
  rw [maxE_expsOf_zpX ha, maxE_expsOf_zpY hd, fExact_zp (by omega) hd]
  simp only; omega

theorem dot_replicate_zero : ∀ (m : ℕ) (y : List ℚ), dot (List.replicate m 0) y = 0
  | 0, _ => rfl
  | m + 1, [] => rfl
  | m + 1, b :: y => by
    rw [List.replicate_succ, dot_cons, dot_replicate_zero m y]; grind

/-- The only nonzero product is `2^d`. -/
theorem dot_zp (a d : ℤ) (k : ℕ) : dot (zpX a k) (zpY d k) = 2 ^ d := by
  unfold zpX zpY
  rw [dot_cons, dot_cons, dot_replicate_zero]
  grind

/-! ## The estimates -/

/-- **Skipping zeros**: for block size `n ≥ 2` the estimate is at least `a + d`, so the computed
ESC is at most `0`. -/
theorem escCoarsePolicy_skip_zp {n : ℕ} (hn : 2 ≤ n) {a d : ℤ} (ha : 0 ≤ a) (hd : -1022 ≤ d)
    (k : ℕ) : ∃ esc, escCoarsePolicy .skip n (zpX a k) (zpY d k) = some esc ∧ esc ≤ 0 := by
  have hhead := coarseEstWith_ge_head (fun bs => (maxE bs, minE (bs.filter Option.isSome))) n
    (ex := expsOf (zpX a k)) (ey := expsOf (zpY d k))
    (by rw [expsOf_zpX (by omega)]; simp) (by rw [expsOf_zpY hd]; simp)
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
  have hmax : eLe (some a) (maxE ((expsOf (zpX a k)).take (n' + 2))) := by
    rw [expsOf_zpX (by omega)]
    exact le_maxE (by simp)
  have hmin : eLe (some d) (minE (((expsOf (zpY d k)).take (n' + 2)).filter Option.isSome)) := by
    apply eLe_minE
    · rw [expsOf_zpY hd]; simp
    · intro e he
      have he' := (List.mem_filter.mp he).1
      have hs := (List.mem_filter.mp he).2
      rw [expsOf_zpY hd] at he'
      have := List.mem_of_mem_take he'
      simp only [List.mem_cons, List.mem_replicate] at this
      rcases this with rfl | rfl | ⟨_, rfl⟩
      · simp at hs
      · simp [eLe]
      · simp at hs
  have hle := eLe_trans (eAdd_mono hmax hmin) hhead
  unfold escCoarsePolicy coarseEstPolicy coarseEstSkip
  rw [maxE_expsOf_zpX ha, maxE_expsOf_zpY hd]
  simp only
  cases he : coarseEstWith (fun bs => (maxE bs, minE (bs.filter Option.isSome))) (n' + 2)
      (expsOf (zpX a k)) (expsOf (zpY d k)) with
  | none => rw [he] at hle; simp [eAdd, eLe] at hle
  | some est =>
    rw [he] at hle
    simp only [eAdd, eLe] at hle
    exact ⟨a + d - est, rfl, by omega⟩

/-- **Zeros at `−1022`**: for every block size `n ≥ 1` the estimate is at least `a − 1022`, so the
computed ESC is at most `d + 1022`. -/
theorem escCoarsePolicy_field0_zp {n : ℕ} (hn : 1 ≤ n) {a d : ℤ} (ha : 0 ≤ a) (hd : -1022 ≤ d)
    (k : ℕ) :
    ∃ esc, escCoarsePolicy .field0 n (zpX a k) (zpY d k) = some esc ∧ esc ≤ d + 1022 := by
  have hhead := coarseEstWith_ge_head (fun bs => blockRep (bs.map fun e => some (e.getD (-1022))))
    n (ex := expsOf (zpX a k)) (ey := expsOf (zpY d k))
    (by rw [expsOf_zpX (by omega)]; simp) (by rw [expsOf_zpY hd]; simp)
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hmax : eLe (some a)
      (maxE (((expsOf (zpX a k)).take (n' + 1)).map fun e => some (e.getD (-1022)))) := by
    rw [expsOf_zpX (by omega)]
    exact le_maxE (by simp)
  have hmin : eLe (some (-1022))
      (minE (((expsOf (zpY d k)).take (n' + 1)).map fun e => some (e.getD (-1022)))) := by
    apply eLe_minE
    · rw [expsOf_zpY hd]; simp
    · intro e he
      obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
      rw [expsOf_zpY hd] at he'
      have := List.mem_of_mem_take he'
      simp only [List.mem_cons, List.mem_replicate] at this
      rcases this with rfl | rfl | ⟨_, rfl⟩ <;> simp [eLe] <;> omega
  have hle := eLe_trans (eAdd_mono hmax hmin) hhead
  unfold escCoarsePolicy coarseEstPolicy coarseEstField0
  rw [maxE_expsOf_zpX ha, maxE_expsOf_zpY hd]
  simp only
  cases he : coarseEstWith (fun bs => blockRep (bs.map fun e => some (e.getD (-1022)))) (n' + 1)
      (expsOf (zpX a k)) (expsOf (zpY d k)) with
  | none => rw [he] at hle; simp [eAdd, eLe] at hle
  | some est =>
    rw [he] at hle
    simp only [eAdd, eLe] at hle
    exact ⟨a + d - est, rfl, by omega⟩

/-- **Skipping zeros is safe for block size `1`**: it is then the exact estimate. -/
theorem coarseEstSkip_one {ex ey : List Exp} (hlen : ex.length = ey.length) :
    coarseEstSkip 1 ex ey = fExact ex ey := by
  have key : ∀ (ex ey : List Exp),
      List.zipWith (fun bx by_ => eMax (eAdd (maxE bx, minE (bx.filter Option.isSome)).1
          (maxE by_, minE (by_.filter Option.isSome)).2)
        (eAdd (maxE bx, minE (bx.filter Option.isSome)).2 (maxE by_, minE (by_.filter Option.isSome)).1))
        (ex.map fun e => [e]) (ey.map fun e => [e]) =
      List.zipWith (fun bx by_ => eMax (eAdd (blockRep bx).1 (blockRep by_).2)
        (eAdd (blockRep bx).2 (blockRep by_).1)) (ex.map fun e => [e]) (ey.map fun e => [e]) := by
    intro ex ey
    induction ex generalizing ey with
    | nil => simp
    | cons a ex ih =>
      cases ey with
      | nil => simp
      | cons b ey =>
        simp only [List.map_cons, List.zipWith_cons_cons]
        rw [ih ey]
        congr 1
        cases a <;> cases b <;> rfl
  rw [← coarseEst_one hlen]
  unfold coarseEstSkip coarseEst coarseEstWith
  rw [blocksOf_one, blocksOf_one, key]

theorem escCoarsePolicy_skip_one {x y : List ℚ} (hlen : x.length = y.length) :
    escCoarsePolicy .skip 1 x y = escCoarse 1 x y := by
  have hl : (expsOf x).length = (expsOf y).length := by simp [expsOf, hlen]
  have h := coarseEstSkip_one hl
  have h' := coarseEst_one hl
  unfold escCoarsePolicy escCoarse
  simp only [coarseEstPolicy, h, h']
  cases maxE (expsOf x) <;> cases maxE (expsOf y) <;> rfl

/-! ## The routine -/

theorem transpose_singletons : ∀ ys : List ℚ, ys ≠ [] → transpose (ys.map fun v => [v]) = [ys]
  | [], h => absurd rfl h
  | [y], _ => rfl
  | y :: y' :: ys, _ => by
    have ih := transpose_singletons (y' :: ys) (by simp)
    show transpose ([y] :: ((y' :: ys).map fun v => [v])) = [y :: y' :: ys]
    rw [show (y' :: ys).map (fun v => [v]) = [y'] :: ys.map (fun v => [v]) from rfl] at ih ⊢
    show List.zipWith List.cons [y] (transpose ([y'] :: ys.map fun v => [v])) = _
    rw [ih]; rfl

/-- The fixed-point product of the family is `0` once the width is at most `a`: `x₂ = 1` falls
below the point and `y₁ = 0`. -/
theorem fixedProduct_zp {W : ℕ} {a d : ℤ} (ha : 0 ≤ a) (hd : -1022 ≤ d) (hW : (W : ℤ) ≤ a)
    (k : ℕ) : fixedProduct W (zpX a k) (zpY d k) = 0 := by
  unfold fixedProduct shiftOf
  rw [maxE_expsOf_zpX ha, maxE_expsOf_zpY hd]
  simp only
  have hlost : ((1 : ℚ) * 2 ^ ((W : ℤ) - 1 - a)).floor = 0 := by
    apply floor_eq_of
    · rw [Rat.one_mul]; exact Rat.le_of_lt (two_pow_pos _)
    · rw [Rat.one_mul]
      have := two_pow_lt (show (W : ℤ) - 1 - a < 0 by omega)
      have h1 : (2 : ℚ) ^ (0 : ℤ) = 1 := rfl
      have h2 : ((0 : ℤ) : ℚ) = 0 := rfl
      grind
  unfold fixedVec zpX zpY
  simp only [List.map_cons, List.map_replicate, Rat.zero_mul, floor_zero, hlost]
  rw [dotZ_cons, dotZ_cons, dotZ_zero_left (List.replicate (k - 2) 0) _
    (fun z hz => List.eq_of_mem_replicate hz)]
  simp

/-- One emulated entry of the family is `0`. -/
theorem emulEntry_zp {W s : ℕ} (hs : 0 < s) (hfit : ADP.remapFits W s = true) {a d : ℤ}
    (ha : 0 ≤ a) (hd : -1022 ≤ d) (hW : (W : ℤ) ≤ a) {k : ℕ} (hk1 : 2 ≤ k)
    (hk2 : k * (128 * 128) < 2 ^ 31) : emulEntry W s (zpX a k) (zpY d k) = some 0 := by
  rw [emulEntry_eq hs hfit (by rw [zpX_length a hk1]; exact hk2), fixedProduct_zp ha hd hW]
  show rne64 0 = some 0
  decide +kernel

/-- Widths up to `78` need at most `10` slices. -/
theorem slicesNeeded_le_ten : ∀ m : Fin 25, slicesNeeded (54 + m) ≤ 10 := by decide +kernel

/-- **The routine on the family.** If a zero policy's ESC for the family is at most `24` and
`a ≥ 78`, ADP emulates with at most `78` bits and returns `0` for the nonzero product `2^d`. -/
theorem adpPolicy_zp (cfg : ADPConfig) (hratio : 100 ≤ cfg.speedRatio) (pol : ZeroPolicy)
    {a d : ℤ} (ha : 78 ≤ a) (hd : -1022 ≤ d) {k : ℕ} (hk1 : 2 ≤ k)
    (hk2 : k * (128 * 128) < 2 ^ 31) {esc : ℤ}
    (hesc : escCoarsePolicy pol cfg.block (zpX a k) (zpY d k) = some esc) (h24 : esc ≤ 24)
    {A B : List (List (BitVec 64))} (hA : decodeMatrix64 A = some [zpX a k])
    (hB : decodeMatrix64 B = some ((zpY d k).map fun v => [v])) :
    adpPolicy cfg pol A B = (.emulated, some [[0]]) := by
  unfold adpPolicy
  rw [hA, hB]
  simp only
  rw [transpose_singletons _ (by simp [zpY])]
  have hm : matrixEscPolicy pol cfg.block [zpX a k] [zpY d k] = some (max 0 esc) := by
    unfold matrixEscPolicy
    simp only [List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil,
      List.append_nil, List.foldl_cons, List.foldl_nil, hesc, maxOpt, Option.bind_some,
      Option.map_some]
  rw [hm]
  simp only
  obtain ⟨m, hm0, hmle, hmeq⟩ : ∃ m : ℕ, 0 ≤ m ∧ m ≤ 24 ∧ (m : ℤ) = max 0 esc :=
    ⟨(max 0 esc).toNat, by omega, by omega, by omega⟩
  have hW : adpWidth (max 0 esc) = 54 + m := by
    unfold adpWidth; omega
  rw [hW]
  have hsl := slicesNeeded_le_ten ⟨m, by omega⟩
  obtain ⟨hs1, hfit, _⟩ := slicesNeeded_spec (54 + m)
  have hsq : slicesNeeded (54 + m) * slicesNeeded (54 + m) ≤ cfg.speedRatio := by
    have := Nat.mul_le_mul hsl hsl
    simp only at this
    omega
  rw [if_pos hsq]
  have he := emulEntry_zp (W := 54 + m) (s := slicesNeeded (54 + m)) (a := a) (d := d) (k := k)
    hs1 hfit (by omega) hd (by omega) hk1 hk2
  simp only [List.mapM_cons, List.mapM_nil, he]
  rfl

/-! ## Grade A fails -/

theorem two_pow_mul_le {k : ℕ} (hk : k * (128 * 128) < 2 ^ 31) :
    ((4 * k + 1 : ℕ) : ℚ) ≤ 2 ^ (19 : ℤ) := by
  have : 4 * k + 1 ≤ 2 ^ 19 := by omega
  rw [show (2 : ℚ) ^ (19 : ℤ) = ((2 ^ 19 : ℕ) : ℚ) from two_pow_natCast 19]
  exact_mod_cast this

/-- **Grade A fails** for the family's computed `0`: `|0 − 2^d| = 2^d` exceeds
`(4k + 1) 2^-53 · 2^d + 2^-1075`. -/
theorem gradeAEntry_zp_zero {a d : ℤ} (hd : -1022 ≤ d) {k : ℕ} (hk1 : 2 ≤ k)
    (hk2 : k * (128 * 128) < 2 ^ 31) : gradeAEntry (zpX a k) (zpY d k) 0 = false := by
  unfold gradeAEntry
  rw [dot_zp, zpX_length a hk1]
  have hsum : ((List.zipWith (· * ·) (zpX a k) (zpY d k)).map Rat.abs).sum = 2 ^ d := by
    unfold zpX zpY
    simp only [List.zipWith_cons_cons, List.map_cons, List.sum_cons]
    have hz : ((List.zipWith (· * ·) (List.replicate (k - 2) (0 : ℚ))
        (List.replicate (k - 2) 0)).map Rat.abs).sum = 0 := by
      rw [List.zipWith_replicate, List.map_replicate, Nat.min_self]
      generalize k - 2 = m
      induction m with
      | zero => rfl
      | succ m ih => rw [List.replicate_succ, List.sum_cons, ih]; simp; grind
    rw [hz]
    simp only [Rat.mul_zero, Rat.one_mul, abs_zero, abs_two_pow]
    grind
  rw [hsum]
  simp only [decide_eq_false_iff_not, Rat.not_le]
  rw [show (0 : ℚ) - 2 ^ d = -(2 ^ d) by grind, abs_neg, abs_two_pow]
  have h1 := two_pow_mul_le hk2
  have h4k : ((4 * k + 1 : ℕ) : ℚ) = 4 * (k : ℚ) + 1 := by
    rw [Rat.natCast_add, Rat.natCast_mul]; rfl
  rw [h4k] at h1
  have hp := two_pow_pos d
  have hA : (4 * (k : ℚ) + 1) * 2 ^ (-53 : ℤ) * 2 ^ d ≤ 2 ^ (d - 34) := by
    have := Rat.mul_le_mul_of_nonneg_right h1 (Rat.le_of_lt (two_pow_pos (-53 : ℤ)))
    have := Rat.mul_le_mul_of_nonneg_right this (Rat.le_of_lt hp)
    have e : (2 : ℚ) ^ (19 : ℤ) * 2 ^ (-53 : ℤ) * 2 ^ d = 2 ^ (d - 34) := by
      rw [← two_pow_add, ← two_pow_add]; congr 1; omega
    rw [e] at this; exact this
  have hB : (2 : ℚ) ^ (-1075 : ℤ) ≤ 2 ^ (d - 34) := two_pow_le (by omega)
  have hC : (2 : ℚ) ^ (d - 34) + 2 ^ (d - 34) < 2 ^ d := by
    rw [show (2 : ℚ) ^ (d - 34) + 2 ^ (d - 34) = 2 ^ (d - 33) by
      rw [show d - 33 = (d - 34) + 1 by omega, two_pow_succ]; grind]
    exact two_pow_lt (by omega)
  grind

/-! ## Binary64 words -/

theorem exists_word64 {v : ℚ} (hv : Binary64Value v) : ∃ w, value64 w = some v := by
  have hfin : absQ v ≤ fp64.maxFinite := by
    rw [absQ_eq, fp64_maxFinite_eq_maxFormat]; exact formatValue_abs_le hv
  have h := fp64RoundTC_eq hfin
  rw [show fp64Round v = some v from rne64_of_value hv] at h
  unfold fp64RoundTC at h
  cases hb : roundBinary fp64 .nearestEven v with
  | none => rw [hb] at h; simp at h
  | some w => rw [hb, Option.bind_some] at h; exact ⟨w, h⟩

theorem exists_words64 : ∀ (x : List ℚ), (∀ a ∈ x, Binary64Value a) →
    ∃ ws : List (BitVec 64), ws.mapM value64 = some x
  | [], _ => ⟨[], rfl⟩
  | a :: x, h => by
    obtain ⟨w, hw⟩ := exists_word64 (h a List.mem_cons_self)
    obtain ⟨ws, hws⟩ := exists_words64 x (fun b hb => h b (List.mem_cons_of_mem _ hb))
    exact ⟨w :: ws, by rw [List.mapM_cons, hw, hws]; rfl⟩

theorem exists_columns64 : ∀ (y : List ℚ), (∀ a ∈ y, Binary64Value a) →
    ∃ B : List (List (BitVec 64)), decodeMatrix64 B = some (y.map fun v => [v])
  | [], _ => ⟨[], rfl⟩
  | a :: y, h => by
    obtain ⟨w, hw⟩ := exists_word64 (h a List.mem_cons_self)
    obtain ⟨B, hB⟩ := exists_columns64 y (fun b hb => h b (List.mem_cons_of_mem _ hb))
    refine ⟨[w] :: B, ?_⟩
    unfold decodeMatrix64 at hB ⊢
    rw [List.mapM_cons, hB]
    simp [hw]

theorem binary64Value_zero : Binary64Value 0 := ⟨0, 0, by decide, by decide, by decide, by simp⟩

theorem binary64Value_two_pow {e : ℤ} (h1 : -1022 ≤ e) (h2 : e ≤ 1023) :
    Binary64Value ((2 : ℚ) ^ e) :=
  formatValue_two_pow (by decide) h1 h2

/-- **The family's binary64 words exist**: `A = [x]` as one row, `B` as the column `y`. -/
theorem exists_decode_zp {a d : ℤ} (ha1 : -1022 ≤ a) (ha2 : a ≤ 1023) (hd1 : -1022 ≤ d)
    (hd2 : d ≤ 1023) (k : ℕ) :
    ∃ A B : List (List (BitVec 64)), decodeMatrix64 A = some [zpX a k] ∧
      decodeMatrix64 B = some ((zpY d k).map fun v => [v]) := by
  obtain ⟨ws, hws⟩ := exists_words64 (zpX a k) (by
    intro v hv
    simp only [zpX, List.mem_cons, List.mem_replicate] at hv
    rcases hv with rfl | rfl | ⟨_, rfl⟩
    · exact binary64Value_two_pow ha1 ha2
    · exact binary64Value_two_pow (e := 0) (by decide) (by decide)
    · exact binary64Value_zero)
  obtain ⟨B, hB⟩ := exists_columns64 (zpY d k) (by
    intro v hv
    simp only [zpY, List.mem_cons, List.mem_replicate] at hv
    rcases hv with rfl | rfl | ⟨_, rfl⟩
    · exact binary64Value_zero
    · exact binary64Value_two_pow hd1 hd2
    · exact binary64Value_zero)
  refine ⟨[ws], B, ?_, hB⟩
  unfold decodeMatrix64
  rw [List.mapM_cons, hws]
  rfl

/-! ## The general statements -/

/-- **Skipping zeros is unsafe for every block size `n ≥ 2` and every inner dimension
`2 ≤ k < 2^17`**: for `x = (2^a, 1, 0, …)` and `y = (0, 2^d, 0, …)` with `78 ≤ a ≤ 1023`, the
computed ESC is at most `0` while the exact one is `a` (`[X.4]` fails), and ADP emulates and returns
`0` for the product `2^d`, breaking Grade A. -/
theorem adpPolicy_skip_wrong (cfg : ADPConfig) (hblock : 2 ≤ cfg.block)
    (hratio : 100 ≤ cfg.speedRatio) {a d : ℤ} (ha1 : 78 ≤ a) (ha2 : a ≤ 1023) (hd1 : -1022 ≤ d)
    (hd2 : d ≤ 1023) {k : ℕ} (hk1 : 2 ≤ k) (hk2 : k * (128 * 128) < 2 ^ 31) :
    (∃ esc, escCoarsePolicy .skip cfg.block (zpX a k) (zpY d k) = some esc ∧
      esc < escExact (zpX a k) (zpY d k)) ∧
    ∃ A B : List (List (BitVec 64)), decodeMatrix64 A = some [zpX a k] ∧
      decodeMatrix64 B = some ((zpY d k).map fun v => [v]) ∧
      dot (zpX a k) (zpY d k) = 2 ^ d ∧
      adpPolicy cfg .skip A B = (.emulated, some [[0]]) ∧
      gradeAEntry (zpX a k) (zpY d k) 0 = false := by
  obtain ⟨esc, hesc, hle⟩ := escCoarsePolicy_skip_zp hblock (show 0 ≤ a by omega) hd1 k
  refine ⟨⟨esc, hesc, by rw [escExact_zp (by omega) hd1]; omega⟩, ?_⟩
  obtain ⟨A, B, hA, hB⟩ := exists_decode_zp (by omega) ha2 hd1 hd2 k
  exact ⟨A, B, hA, hB, dot_zp a d k,
    adpPolicy_zp cfg hratio .skip ha1 hd1 hk1 hk2 hesc (by omega) hA hB,
    gradeAEntry_zp_zero hd1 hk1 hk2⟩

/-- **Zeros at `−1022` are unsafe for every block size `n ≥ 1` and every inner dimension
`2 ≤ k < 2^17`**: for `x = (2^a, 1, 0, …)` and `y = (0, 2^d, 0, …)` with `78 ≤ a ≤ 1023` and
`−1022 ≤ d ≤ −998`, the computed ESC is at most `d + 1022 ≤ 24` while the exact one is `a`, and
ADP emulates and returns `0` for the product `2^d`, breaking Grade A. -/
theorem adpPolicy_field0_wrong (cfg : ADPConfig) (hblock : 1 ≤ cfg.block)
    (hratio : 100 ≤ cfg.speedRatio) {a d : ℤ} (ha1 : 78 ≤ a) (ha2 : a ≤ 1023) (hd1 : -1022 ≤ d)
    (hd2 : d ≤ -998) {k : ℕ} (hk1 : 2 ≤ k) (hk2 : k * (128 * 128) < 2 ^ 31) :
    (∃ esc, escCoarsePolicy .field0 cfg.block (zpX a k) (zpY d k) = some esc ∧
      esc < escExact (zpX a k) (zpY d k)) ∧
    ∃ A B : List (List (BitVec 64)), decodeMatrix64 A = some [zpX a k] ∧
      decodeMatrix64 B = some ((zpY d k).map fun v => [v]) ∧
      dot (zpX a k) (zpY d k) = 2 ^ d ∧
      adpPolicy cfg .field0 A B = (.emulated, some [[0]]) ∧
      gradeAEntry (zpX a k) (zpY d k) 0 = false := by
  obtain ⟨esc, hesc, hle⟩ := escCoarsePolicy_field0_zp hblock (show 0 ≤ a by omega) hd1 k
  refine ⟨⟨esc, hesc, by rw [escExact_zp (by omega) hd1]; omega⟩, ?_⟩
  obtain ⟨A, B, hA, hB⟩ := exists_decode_zp (by omega) ha2 hd1 (by omega) k
  exact ⟨A, B, hA, hB, dot_zp a d k,
    adpPolicy_zp cfg hratio .field0 ha1 hd1 hk1 hk2 hesc (by omega) hA hB,
    gradeAEntry_zp_zero hd1 hk1 hk2⟩

end Ozaki.TC
