import Ozaki.Basic

/-! # ADP and ESC: Ozaki-I on INT8 matrix multipliers

NVIDIA's guaranteed-accuracy DGEMM (Schwarz et al., *Guaranteed DGEMM Accuracy While Using Reduced
Precision Tensor Cores Through Extensions of the Ozaki Scheme*, arXiv:2511.13778, modeled in Z3 in
`ozaki-NVIDIA/` of the Z3 repository) emulates binary64 GEMM on INT8 matrix multipliers. Each row of
`A` (column of `B`) is converted to a `W`-bit fixed-point integer, cut into `s` signed 8-bit slices,
and all `s²` slice products are accumulated exactly. This file formalizes the parts that do not
depend on the matrix multiplier:

* **Unsigned slice encoding (§3).** `remap s N` cuts `N` into `s` base-256 digits, lowest first,
  turning an unsigned digit `u ∈ [128, 255]` into `u − 256` with a carry. The digits always
  reconstruct `N` (`remap_value`); all are signed bytes exactly on
  `[−128 (256^s − 1)/255, 127 (256^s − 1)/255]` (`remap_s8`, `[Z.3]`); a remapped digit has the
  bit pattern of the unsigned one (`remap_bit_pattern`, `[Z.5]`); and the range is slightly smaller
  than the unsigned prototype's `[−2^(8s−1), 2^(8s−1))` (`remap_range_smaller`, `[Z.4]`).
* **Slice counts.** `53`-bit integers need `8` naive signed slices but `7` remapped ones
  (`slices_53`).
* **Exponent span capacity (§4).** The coarsened estimate of the largest product exponent never
  exceeds the exact one when zeros have exponent `−∞` (`coarseEst_le`, the paper's coarsening
  theorem, `[Z.6]`); skipping zeros or giving them exponent `−1022` is unsafe
  (`skipZeros_unsafe`, `field0_unsafe`, `[Z.7]`, `[Z.8]`).
* **Fidelity and funnel.** With `W = 53 + ESC + 1` the dominant products keep every bit
  (`full_fidelity`, `[Z.9]`, which also holds without the `+1`, `[Z.9b]`); each product's
  conversion error is at most `δa|b| + |ã|δb` (`term_error`, `[Z.10]`), and with the `+1` each half
  is at most `2^(F−52)` (`funnel`, `[Z.11]`), which fails without it (`funnel_needs_plus_one`,
  `[Z.12]`).
* **Recombination.** The `s²` slice products, weighted by `256^(t+u)`, add up to the product of
  the fixed-point integers (`slice_recombination`, `[R.1]`). -/

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

namespace Ozaki.ADP

/-! ## Slice encodings -/

/-- Value of base-256 digits, lowest first. -/
def digitValue : List ℤ → ℤ
  | [] => 0
  | d :: ds => d + 256 * digitValue ds

/-- The paper's remap from `carry`: a low digit `x = N mod 256 + carry` becomes `x − 256` with a
carry of `1` when `x ≥ 128`; the last digit takes `⌊N / 256^(s−1)⌋` plus the carry. -/
def remapFrom (carry : ℤ) : ℕ → ℤ → List ℤ
  | 0, _ => []
  | 1, N => [N + carry]
  | s + 2, N =>
    if 128 ≤ N % 256 + carry then (N % 256 + carry - 256) :: remapFrom 1 (s + 1) (N / 256)
    else (N % 256 + carry) :: remapFrom 0 (s + 1) (N / 256)

/-- Unsigned slice encoding of `N` into `s` signed bytes, lowest first. -/
def remap (s : ℕ) (N : ℤ) : List ℤ := remapFrom 0 s N

/-- Floor digits of the prototype: `s − 1` unsigned bytes and a signed lead digit. -/
def floorDigits : ℕ → ℤ → List ℤ
  | 0, _ => []
  | 1, N => [N]
  | s + 2, N => (N % 256) :: floorDigits (s + 1) (N / 256)

/-- `127 (256^s − 1) / 255` and `−128 (256^s − 1) / 255`: the remap range. -/
def remapHi (s : ℕ) : ℤ := 127 * ((256 ^ s - 1 : ℕ) / 255 : ℕ)
def remapLo (s : ℕ) : ℤ := -128 * ((256 ^ s - 1 : ℕ) / 255 : ℕ)

theorem dvd_pow256_sub_one : ∀ n : ℕ, 255 ∣ 256 ^ n - 1
  | 0 => by simp
  | n + 1 => by
    have ih := dvd_pow256_sub_one n
    have hk : 1 ≤ 256 ^ n := Nat.one_le_pow n 256 (by decide)
    rw [Nat.pow_succ]
    generalize 256 ^ n = k at ih hk
    have : k * 256 - 1 = 255 * k + (k - 1) := by omega
    rw [this]
    exact Nat.dvd_add (Nat.dvd_mul_right 255 k) ih

theorem remapQ_succ (n : ℕ) :
    (256 ^ (n + 1) - 1 : ℕ) / 255 = 256 * ((256 ^ n - 1 : ℕ) / 255) + 1 := by
  obtain ⟨q, hq⟩ := dvd_pow256_sub_one n
  have hk : 1 ≤ 256 ^ n := Nat.one_le_pow n 256 (by decide)
  rw [hq, Nat.mul_div_cancel_left _ (by decide), Nat.pow_succ]
  generalize 256 ^ n = k at hq hk
  have : k * 256 - 1 = 255 * (256 * q + 1) := by omega
  rw [this, Nat.mul_div_cancel_left _ (by decide)]

theorem remapFrom_length (c : ℤ) : ∀ s N, (remapFrom c s N).length = s
  | 0, _ => rfl
  | 1, _ => rfl
  | s + 2, N => by
    unfold remapFrom
    split <;> simp [remapFrom_length _ (s + 1)]

/-- The digits reconstruct `N + carry`. -/
theorem digitValue_remapFrom : ∀ (c : ℤ) (s : ℕ) (N : ℤ), 0 < s →
    digitValue (remapFrom c s N) = N + c
  | _, 0, _, h => absurd h (by decide)
  | c, 1, N, _ => by simp [remapFrom, digitValue]
  | c, s + 2, N, _ => by
    have hd := Int.emod_def N 256
    unfold remapFrom
    split
    · simp only [digitValue]
      rw [digitValue_remapFrom 1 (s + 1) (N / 256) (by omega)]; omega
    · simp only [digitValue]
      rw [digitValue_remapFrom 0 (s + 1) (N / 256) (by omega)]; omega

/-- **The remap is exact** (`[U.5]`). -/
theorem remap_value {s : ℕ} (hs : 0 < s) (N : ℤ) : digitValue (remap s N) = N := by
  have := digitValue_remapFrom 0 s N hs
  unfold remap; rw [this]; omega

/-- The value of `s` digits in `[−128, 127]` lies in the remap range. -/
theorem digitValue_range : ∀ (ds : List ℤ), (∀ d ∈ ds, -128 ≤ d ∧ d ≤ 127) →
    remapLo ds.length ≤ digitValue ds ∧ digitValue ds ≤ remapHi ds.length
  | [], _ => by simp [digitValue, remapLo, remapHi]
  | d :: ds, h => by
    have ⟨h1, h2⟩ := h d (by simp)
    have ih := digitValue_range ds (fun e he => h e (by simp [he]))
    simp only [remapLo, remapHi, List.length_cons, digitValue] at ih ⊢
    rw [remapQ_succ]
    generalize (256 ^ ds.length - 1 : ℕ) / 255 = q at ih ⊢
    omega

/-- The digits from a carry `c ∈ {0, 1}` are signed bytes when `N + c` lies in the remap range. -/
theorem remapFrom_s8 : ∀ (c : ℤ) (s : ℕ) (N : ℤ), 0 < s → (c = 0 ∨ c = 1) →
    remapLo s ≤ N + c → N + c ≤ remapHi s → ∀ d ∈ remapFrom c s N, -128 ≤ d ∧ d ≤ 127
  | _, 0, _, h, _, _, _ => absurd h (by decide)
  | c, 1, N, _, _, hlo, hhi => by
    simp only [remapLo, remapHi] at hlo hhi
    simp only [remapFrom, List.mem_singleton]
    rintro d rfl
    have : (256 ^ 1 - 1 : ℕ) / 255 = 1 := by decide
    rw [this] at hlo hhi; omega
  | c, s + 2, N, _, hc, hlo, hhi => by
    have hd := Int.emod_def N 256
    have hm1 := Int.emod_nonneg N (show (256 : ℤ) ≠ 0 by decide)
    have hm2 := Int.emod_lt_of_pos N (show (0 : ℤ) < 256 by decide)
    simp only [remapLo, remapHi] at hlo hhi
    rw [remapQ_succ (s + 1)] at hlo hhi
    generalize hQ : (256 ^ (s + 1) - 1 : ℕ) / 255 = Q at hlo hhi
    unfold remapFrom
    split
    · intro d hdm
      rcases List.mem_cons.mp hdm with rfl | hdm
      · omega
      · exact remapFrom_s8 1 (s + 1) (N / 256) (by omega) (Or.inr rfl)
          (by simp only [remapLo]; rw [hQ]; omega) (by simp only [remapHi]; rw [hQ]; omega) d hdm
    · intro d hdm
      rcases List.mem_cons.mp hdm with rfl | hdm
      · omega
      · exact remapFrom_s8 0 (s + 1) (N / 256) (by omega) (Or.inl rfl)
          (by simp only [remapLo]; rw [hQ]; omega) (by simp only [remapHi]; rw [hQ]; omega) d hdm

/-- **Remapped slices are signed bytes** exactly on the remap range (`[Z.3]`). -/
theorem remap_s8 {s : ℕ} (hs : 0 < s) (N : ℤ) :
    (∀ d ∈ remap s N, -128 ≤ d ∧ d ≤ 127) ↔ remapLo s ≤ N ∧ N ≤ remapHi s := by
  constructor
  · intro h
    have := digitValue_range (remap s N) h
    rw [remap_value hs, remap, remapFrom_length] at this
    exact this
  · rintro ⟨h1, h2⟩
    exact remapFrom_s8 0 s N hs (Or.inl rfl) (by simpa using h1) (by simpa using h2)

/-- A remapped digit has the bit pattern of the unsigned digit (`[Z.5]`). -/
theorem remap_bit_pattern (u : ℤ) (h1 : 128 ≤ u) (h2 : u ≤ 255) : (u - 256) % 256 = u := by omega

/-- **The remap range is smaller than the prototype's** (`[Z.4]`): `2^23 − 129` fits three
floor/u8 slices but not three signed bytes. -/
theorem remap_range_smaller :
    (∀ d ∈ (floorDigits 3 8388479).take 2, 0 ≤ d ∧ d ≤ 255) ∧
      (∀ d ∈ (floorDigits 3 8388479).drop 2, -128 ≤ d ∧ d ≤ 127) ∧
      digitValue (floorDigits 3 8388479) = 8388479 ∧
      ¬ ∀ d ∈ remap 3 8388479, -128 ≤ d ∧ d ≤ 127 := by decide

/-- Smallest slice count of a capacity predicate, searched up to `fuel`. -/
def slicesNeeded (fits : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | fuel + 1 => if fits (fuel + 1 - fuel) then 1 else 1 + slicesNeeded (fun s => fits (s + 1)) fuel

/-- Capacity of `s` naive signed slices (seven magnitude bits each) for `W`-bit integers. -/
def naiveFits (W s : ℕ) : Bool := 2 ^ W ≤ 128 ^ s - 1

/-- Capacity of `s` remapped slices for `W`-bit integers `[−2^W, 2^W)`. -/
def remapFits (W s : ℕ) : Bool := decide (remapLo s ≤ -(2 ^ W : ℤ) ∧ (2 ^ W - 1 : ℤ) ≤ remapHi s)

/-- `53` bits: naive signed slices need `8`, remapped slices `7` (`49` slice products instead of
`64`). -/
theorem slices_53 : naiveFits 53 8 ∧ !naiveFits 53 7 ∧ remapFits 53 7 ∧ !remapFits 53 6 := by
  decide

/-! ## Exponent span capacity -/

/-- An exponent, `none` standing for `−∞` (a zero). -/
abbrev Exp := Option ℤ

def eAdd : Exp → Exp → Exp
  | some a, some b => some (a + b)
  | _, _ => none

def eMax : Exp → Exp → Exp
  | none, e => e
  | e, none => e
  | some a, some b => some (max a b)

def eMin : Exp → Exp → Exp
  | some a, some b => some (min a b)
  | _, _ => none

/-- `a ≤ b` with `none = −∞`. -/
def eLe : Exp → Exp → Prop
  | none, _ => True
  | some _, none => False
  | some a, some b => a ≤ b

instance : DecidableRel eLe := fun a b => by
  cases a <;> cases b <;> unfold eLe <;> infer_instance

/-- Largest exponent of a list, `−∞` for no nonzero entry. -/
def maxE (l : List Exp) : Exp := l.foldr eMax none

/-- Smallest exponent of a nonempty list (zeros as `−∞`). -/
def minE : List Exp → Exp
  | [] => none
  | [e] => e
  | e :: e' :: l => eMin e (minE (e' :: l))

/-- `exp(z_r)`: the largest exponent sum `exp(xₜ) + exp(yₜ)` over the products, `−∞` when every
product is zero. -/
def fExact (ex ey : List Exp) : Exp := maxE (List.zipWith eAdd ex ey)

/-- Consecutive blocks of `n` (the last may be shorter). -/
def blocksOf (n : ℕ) : ℕ → List α → List (List α)
  | 0, _ => []
  | fuel + 1, xs => if xs = [] then [] else xs.take n :: blocksOf n fuel (xs.drop n)

/-- The coarsened estimate with block representatives `rep = (Max, Min)`:
`max over blocks of max(Max(x) + Min(y), Min(x) + Max(y))`. -/
def coarseEstWith (rep : List Exp → Exp × Exp) (n : ℕ) (ex ey : List Exp) : Exp :=
  maxE (List.zipWith (fun bx by_ => eMax (eAdd (rep bx).1 (rep by_).2) (eAdd (rep bx).2 (rep by_).1))
    (blocksOf n ex.length ex) (blocksOf n ey.length ey))

/-- The paper's representatives, with zeros as `−∞`. -/
def blockRep (bs : List Exp) : Exp × Exp := (maxE bs, minE bs)

/-- The coarsened estimate the paper computes (§4, §5.2), with zeros as `−∞`. -/
def coarseEst (n : ℕ) (ex ey : List Exp) : Exp := coarseEstWith blockRep n ex ey

/-- Zeros left out of the block minimum (unsafe). -/
def coarseEstSkip (n : ℕ) (ex ey : List Exp) : Exp :=
  coarseEstWith (fun bs => (maxE bs, minE (bs.filter Option.isSome))) n ex ey

/-- Zeros given the subnormal exponent `−1022` (unsafe). -/
def coarseEstField0 (n : ℕ) (ex ey : List Exp) : Exp :=
  coarseEstWith (fun bs => blockRep (bs.map fun e => some (e.getD (-1022)))) n ex ey

theorem eLe_refl (a : Exp) : eLe a a := by cases a <;> simp [eLe]

theorem eLe_trans {a b c : Exp} (h1 : eLe a b) (h2 : eLe b c) : eLe a c := by
  cases a <;> cases b <;> cases c <;> simp_all [eLe] <;> omega

theorem eLe_eMax_iff (a b c : Exp) : eLe (eMax a b) c ↔ eLe a c ∧ eLe b c := by
  cases a <;> cases b <;> cases c <;> simp [eMax, eLe] <;> omega

theorem eLe_eMax_left (a b : Exp) : eLe a (eMax a b) := by
  cases a <;> cases b <;> simp [eMax, eLe] <;> omega

theorem eLe_eMax_right (a b : Exp) : eLe b (eMax a b) := by
  cases a <;> cases b <;> simp [eMax, eLe] <;> omega

theorem eLe_eMin_left (a b : Exp) : eLe (eMin a b) a := by
  cases a <;> cases b <;> simp [eMin, eLe] <;> omega

theorem eLe_eMin_right (a b : Exp) : eLe (eMin a b) b := by
  cases a <;> cases b <;> simp [eMin, eLe] <;> omega

theorem eAdd_mono {a b c d : Exp} (h1 : eLe a b) (h2 : eLe c d) : eLe (eAdd a c) (eAdd b d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all [eAdd, eLe] <;> omega

theorem eAdd_comm (a b : Exp) : eAdd a b = eAdd b a := by
  cases a <;> cases b <;> simp [eAdd]; omega

theorem maxE_le_iff (l : List Exp) (c : Exp) : eLe (maxE l) c ↔ ∀ e ∈ l, eLe e c := by
  induction l with
  | nil => simp [maxE, eLe]
  | cons a l ih =>
    show eLe (eMax a (maxE l)) c ↔ _
    rw [eLe_eMax_iff, ih, List.forall_mem_cons]

theorem le_maxE {l : List Exp} {e : Exp} (h : e ∈ l) : eLe e (maxE l) := by
  have := (maxE_le_iff l (maxE l)).mp (eLe_refl _)
  exact this e h

/-- In one block: `Max(x) + Min(y)` is at most the largest exponent sum of the block's products. -/
theorem block_le : ∀ (bx by_ : List Exp), bx.length = by_.length →
    eLe (eAdd (maxE bx) (minE by_)) (maxE (List.zipWith eAdd bx by_))
  | [], [], _ => by simp [maxE, minE, eAdd, eLe]
  | [a], [b], _ => by
    simp only [maxE, List.foldr_cons, List.foldr_nil, minE, List.zipWith_cons_cons,
      List.zipWith_nil_left]
    have : eMax a none = a := by cases a <;> rfl
    rw [this]
    have : eMax (eAdd a b) none = eAdd a b := by cases (eAdd a b) <;> rfl
    rw [this]; exact eLe_refl _
  | a :: a' :: as, b :: b' :: bs, h => by
    have ih := block_le (a' :: as) (b' :: bs) (by simpa using h)
    have hm : maxE (a :: a' :: as) = eMax a (maxE (a' :: as)) := rfl
    have hz : maxE (List.zipWith eAdd (a :: a' :: as) (b :: b' :: bs)) =
        eMax (eAdd a b) (maxE (List.zipWith eAdd (a' :: as) (b' :: bs))) := rfl
    have hn : minE (b :: b' :: bs) = eMin b (minE (b' :: bs)) := rfl
    rw [hm, hz, hn]
    -- either `a` or the rest attains the maximum
    have hsplit : eLe (eAdd (eMax a (maxE (a' :: as))) (eMin b (minE (b' :: bs))))
        (eMax (eAdd a (eMin b (minE (b' :: bs)))) (eAdd (maxE (a' :: as)) (eMin b (minE (b' :: bs))))) := by
      cases a <;> cases (maxE (a' :: as)) <;> cases (eMin b (minE (b' :: bs))) <;>
        simp [eMax, eAdd, eLe] <;> omega
    refine eLe_trans hsplit ((eLe_eMax_iff _ _ _).mpr ⟨?_, ?_⟩)
    · exact eLe_trans (eAdd_mono (eLe_refl a) (eLe_eMin_left b _)) (eLe_eMax_left _ _)
    · exact eLe_trans (eAdd_mono (eLe_refl _) (eLe_eMin_right b _))
        (eLe_trans ih (eLe_eMax_right _ _))
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | [_], _ :: _ :: _, h => by simp at h
  | _ :: _ :: _, [_], h => by simp at h

theorem mem_zipWith_exists {f : α → β → γ} :
    ∀ {l₁ : List α} {l₂ : List β} {e : γ}, e ∈ List.zipWith f l₁ l₂ →
      ∃ a b, (a, b) ∈ List.zip l₁ l₂ ∧ e = f a b
  | [], _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | a :: l₁, b :: l₂, e, h => by
    simp only [List.zipWith_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨a, b, by simp, rfl⟩
    · obtain ⟨a', b', hm, rfl⟩ := mem_zipWith_exists h
      exact ⟨a', b', by simp [hm], rfl⟩

/-- Blocks of aligned lists have equal lengths and pair up the original products. -/
theorem blocksOf_pairs (f : Exp → Exp → Exp) (n : ℕ) :
    ∀ (fuel : ℕ) (xs ys : List Exp), xs.length = ys.length →
      ∀ bx by_, (bx, by_) ∈ List.zip (blocksOf n fuel xs) (blocksOf n fuel ys) →
        bx.length = by_.length ∧ ∀ e ∈ List.zipWith f bx by_, e ∈ List.zipWith f xs ys
  | 0, xs, ys, _, bx, by_, hb => by simp [blocksOf] at hb
  | fuel + 1, xs, ys, hlen, bx, by_, hb => by
    by_cases hx : xs = []
    · subst hx; simp [blocksOf] at hb
    · have hy : ys ≠ [] := by
        intro h; subst h; exact hx (List.eq_nil_of_length_eq_zero (by simpa using hlen))
      simp only [blocksOf, hx, hy, if_false, List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at hb
      rcases hb with ⟨rfl, rfl⟩ | hb
      · refine ⟨by simp [hlen], fun e he => ?_⟩
        rw [← List.take_append_drop n xs, ← List.take_append_drop n ys,
          List.zipWith_append (by simp [hlen])]
        exact List.mem_append_left _ he
      · obtain ⟨h1, h2⟩ := blocksOf_pairs f n fuel (xs.drop n) (ys.drop n) (by simp [hlen]) bx by_ hb
        refine ⟨h1, fun e he => ?_⟩
        rw [← List.take_append_drop n xs, ← List.take_append_drop n ys,
          List.zipWith_append (by simp [hlen])]
        exact List.mem_append_right _ (h2 e he)

/-- **The coarsening theorem** (§4, `[Z.6]`). With zeros as `−∞`, the coarsened estimate never
exceeds the exact `exp(z_r)`, so the coarsened ESC is never smaller than the exact one. -/
theorem coarseEst_le (n : ℕ) {ex ey : List Exp} (hlen : ex.length = ey.length) :
    eLe (coarseEst n ex ey) (fExact ex ey) := by
  unfold coarseEst coarseEstWith fExact
  rw [maxE_le_iff]
  intro e he
  obtain ⟨bx, by_, hb, rfl⟩ := mem_zipWith_exists he
  rw [show ey.length = ex.length from hlen.symm] at hb
  obtain ⟨hl, hsub⟩ := blocksOf_pairs eAdd n ex.length ex ey hlen bx by_ hb
  have hsub' : ∀ e ∈ List.zipWith eAdd by_ bx, e ∈ List.zipWith eAdd ex ey := by
    intro e he
    rw [show List.zipWith eAdd by_ bx = List.zipWith eAdd bx by_ from
      List.zipWith_comm_of_comm eAdd_comm] at he
    exact hsub e he
  simp only [blockRep]
  rw [eLe_eMax_iff]
  constructor
  · refine eLe_trans (block_le bx by_ hl) ((maxE_le_iff _ _).mpr fun e he => le_maxE (hsub e he))
  · rw [eAdd_comm]
    refine eLe_trans (block_le by_ bx hl.symm) ((maxE_le_iff _ _).mpr fun e he => le_maxE (hsub' e he))

/-- Skipping zeros in the block minimum is unsafe (`[Z.7]`): `x = (1.5 · 2^10, 1.25, 0, 0)`,
`y = (0, 1.75, 0, 0)`, blocks of two. The only nonzero product has exponent `0`, but the
estimate is `10`. -/
theorem skipZeros_unsafe :
    coarseEstSkip 2 [some 10, some 0, none, none] [none, some 0, none, none] = some 10 ∧
      fExact [some 10, some 0, none, none] [none, some 0, none, none] = some 0 := by decide

/-- Giving zeros the exponent `−1022` is unsafe (`[Z.8]`): `x = (1.5 · 2^1000, 1.25 · 2^-1000)`,
`y = (0, 1.75 · 2^-20)`. The only nonzero product has exponent `−1020`, but the estimate is
`−22`. -/
theorem field0_unsafe :
    coarseEstField0 2 [some 1000, some (-1000)] [none, some (-20)] = some (-22) ∧
      fExact [some 1000, some (-1000)] [none, some (-20)] = some (-1020) := by decide

/-! ## Fidelity and the funnel -/

/-- **Full fidelity** (`[Z.9]`). With `W = 53 + ESC + 1`, the lowest bit `2^(e−52)` of every
entry that forms a dominant product lies on the fixed-point grid `2^(e_p + 1 − W)` of its row. -/
theorem full_fidelity (ep eq ex ey F ESC W : ℤ) (h1 : ex ≤ ep) (h2 : ey ≤ eq) (hF : F = ex + ey)
    (hE : ep + eq - F ≤ ESC) (hW : W = 53 + ESC + 1) :
    ep + 1 - W ≤ ex - 52 ∧ eq + 1 - W ≤ ey - 52 := by omega

/-- Full fidelity already holds with `W = 53 + ESC` (`[Z.9b]`). -/
theorem full_fidelity_without_plus_one (ep eq ex ey F ESC W : ℤ) (h1 : ex ≤ ep) (h2 : ey ≤ eq)
    (hF : F = ex + ey) (hE : ep + eq - F ≤ ESC) (hW : W = 53 + ESC) :
    ep + 1 - W ≤ ex - 52 ∧ eq + 1 - W ≤ ey - 52 := by omega

/-- **Term error** (`[Z.10]`): `|ab − ãb̃| ≤ δa |b| + |ã| δb`. -/
theorem term_error (a at_ b bt da db : ℚ) (ha : Rat.abs (a - at_) ≤ da) (hb : Rat.abs (b - bt) ≤ db) :
    Rat.abs (a * b - at_ * bt) ≤ da * Rat.abs b + Rat.abs at_ * db := by
  have e : a * b - at_ * bt = (a - at_) * b + at_ * (b - bt) := by grind
  rw [e]
  have h1 := abs_add_le ((a - at_) * b) (at_ * (b - bt))
  rw [abs_mul, abs_mul] at h1
  have h2 := Rat.mul_le_mul_of_nonneg_right ha (abs_nonneg b)
  have h3 := Rat.mul_le_mul_of_nonneg_left hb (abs_nonneg at_)
  grind

/-- **The funnel** (`[Z.11]`). With `W = 54 + ESC`, both halves of a term's error,
`δa |b| ≤ 2^(e_p+1−W) 2^(e_b+1)` and `|ã| δb ≤ 2^(e_a+1) 2^(e_q+1−W)`, are at most `2^(F − 52)` for
every term (the Z3 query also assumes `e_a + e_b ≤ F`, which is not needed). -/
theorem funnel (ep eq ea eb F ESC W : ℤ) (h1 : ea ≤ ep) (h2 : eb ≤ eq)
    (hE : ep + eq - F ≤ ESC) (hW : W = 54 + ESC) :
    (ep + 1 - W) + (eb + 1) ≤ F - 52 ∧ (ea + 1) + (eq + 1 - W) ≤ F - 52 := by omega

/-- Without the `+1` the funnel bound fails (`[Z.12]`): `e_a = e_p = 0`, `e_b = e_q = 0`, `F = 0`,
`ESC = 0`, `W = 53`. -/
theorem funnel_needs_plus_one :
    ¬ ((0 + 1 - (53 + 0 : ℤ)) + (0 + 1) ≤ 0 - 52) := by decide

/-! ## Recombination -/

/-- The `t`-th slice of a vector of remapped integers. -/
def sliceVec (s t : ℕ) (N : List ℤ) : List ℤ := N.map fun z => (remap s z).getD t 0

theorem sumZ_map_add (l : List α) (f g : α → ℤ) :
    (l.map fun a => f a + g a).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; omega

theorem sumZ_map_mul_left (l : List α) (c : ℤ) (f : α → ℤ) :
    (l.map fun a => c * f a).sum = c * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih, Int.mul_add]

theorem sumZ_map_mul_right (l : List α) (c : ℤ) (f : α → ℤ) :
    (l.map fun a => f a * c).sum = (l.map f).sum * c := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih, Int.add_mul]

theorem sumZ_map_zero (l : List α) : (l.map fun _ => (0 : ℤ)).sum = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem digitValue_eq_sum (ds : List ℤ) :
    digitValue ds = ((List.range ds.length).map fun t => ds.getD t 0 * 256 ^ t).sum := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    rw [List.length_cons, List.range_succ_eq_map]
    simp only [digitValue, List.map_cons, List.sum_cons, List.getD_cons_zero, List.map_map,
      Function.comp_def, List.getD_cons_succ, Int.pow_succ]
    rw [ih, show (256 : ℤ) ^ 0 = 1 from rfl, Int.mul_one, ← sumZ_map_mul_left]
    congr 2
    apply List.map_congr_left; intro t _; rw [Int.mul_comm (256 : ℤ), Int.mul_assoc]

/-- One entry: the weighted slice products of `a` and `b` add up to `a · b`. -/
theorem entry_recombination {s : ℕ} (hs : 0 < s) (a b : ℤ) :
    ((List.range s).map fun t => ((List.range s).map fun u =>
      256 ^ (t + u) * ((remap s a).getD t 0 * (remap s b).getD u 0)).sum).sum = a * b := by
  have ha := remap_value hs a
  have hb := remap_value hs b
  rw [digitValue_eq_sum, remap, remapFrom_length, ← remap] at ha hb
  conv => rhs; rw [← ha, ← hb]
  rw [← sumZ_map_mul_right]
  congr 1; apply List.map_congr_left; intro t _
  rw [← sumZ_map_mul_left]
  congr 1; apply List.map_congr_left; intro u _
  rw [Int.pow_add]; grind

/-- **Recombination** (`[R.1]`): the `s²` slice products, weighted by `256^(t+u)`, add up to the
product of the fixed-point integers. -/
theorem slice_recombination {s : ℕ} (hs : 0 < s) :
    ∀ (Na Nb : List ℤ), ((List.range s).map fun t => ((List.range s).map fun u =>
      256 ^ (t + u) * dotZ (sliceVec s t Na) (sliceVec s u Nb)).sum).sum = dotZ Na Nb
  | [], Nb => by simp [sliceVec, sumZ_map_zero]
  | _ :: _, [] => by simp [sliceVec, sumZ_map_zero]
  | a :: Na, b :: Nb => by
    have ih := slice_recombination hs Na Nb
    simp only [sliceVec, List.map_cons, dotZ_cons] at ih ⊢
    simp only [Int.mul_add]
    rw [← entry_recombination hs a b, ← ih]
    rw [← sumZ_map_add]; congr 1; apply List.map_congr_left; intro t _
    rw [← sumZ_map_add]

end Ozaki.ADP
