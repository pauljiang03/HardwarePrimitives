import Ozaki.BoundedChecked
import Ozaki.BoundedOzaki2J

/-! # One theorem bounding every integer of correctly rounded Ozaki-II

`ozaki2CRJ` (in `Ozaki.BoundedOzaki2J`) is correctly rounded Ozaki-II in integer operations. As
`Ozaki.BoundedChecked` does for Ozaki-I, this file gives each of its steps a *checked* twin in
`Ozaki.Checked`, in which every integer an arithmetic operation produces passes a guard (data below
`2^R`, exponent-like integers below `2^X`) and a failed guard returns `none`:

* the scaling exponents from bit lengths (`scaleShiftZC`), the shift amounts, the shifted and
  truncated significands (`truncShiftZC`) and the test for dropped bits (`dropsBitsC`);
* the symmetric residues (`symModC`), each output of the matrix multiplier read back and its residue
  (`residueProductC`), every product and partial sum of the CRT combination and the final symmetric
  residue (`crtC`);
* the sums of the integer bound `K` (`boundKC`), the enclosure's exponent, and the enclosure test
  (`roundEnclosureBC` of `Ozaki.BoundedChecked`);
* the exact fallback, by the checked jumping exact fallback of `Ozaki.BoundedChecked`
  (`ozaki1ExactFallbackIC`).

The CRT basis's constants are guarded as they are read: each modulus, the weights in use and their
product `M`. As there, comparisons, signs, absolute values, bit lengths and list lengths produce no
new magnitudes and are not guarded. The arithmetic of the matrix multiplier itself is guarded when
it runs through `Ozaki.CheckedMultipliers.chunkedC` (split-K with its chunk sums guarded); the block
FMA arithmetic of the matrix multiplier is that of the hardware model.

`ozaki2CRJC_eq` proves that on binary entries with an exact matrix multiplier, if `R` and `X` meet
explicit requirements (`ozaki2R`, `ozaki2X` for each configuration; `exactR`, `exactX` for the exact
fallback), the checked `ozaki2CRJC` returns exactly what `ozaki2CRJ` returns: no guard ever fails.
The requirements on the CRT are `crtSize B < 2^R` (the weights times the moduli, summed) and
`2M < 2^R`. Concrete widths:

* binary64 with the twelve moduli at most `4096` (`P = 69`), `11`-bit slices, `k ≤ 2^20` and at
  most `175` slices in the exact fallback: every data integer within `264` bits, every exponent and
  counter within `24` bits (`ozaki2CRJC_binary64`, `ozaki2CRJC_binary64_eq`);
* binary32 with six moduli at most `4096` (`P ≤ 34`), `k ≤ 2^20`, at most `24` slices: `161` and
  `17` bits (`ozaki2CRJC_binary32`, `ozaki2CRJC_binary32_eq`).

The widths are set by the exact fallback (Ozaki-I's), not by the CRT: the CRT's integers need about
`160` bits with twelve moduli. -/

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

namespace Ozaki

namespace Checked

variable (B : Widths)

/-- A sum with every partial sum guarded (added from the right). -/
def sumC : List ℤ → Option ℤ
  | [] => some 0
  | z :: zs => do
    let r ← sumC zs
    B.gv (z + r)

/-- A sum of natural numbers with every partial sum guarded. -/
def sumNC : List ℕ → Option ℕ
  | [] => some 0
  | n :: ns => do
    let r ← sumNC ns
    B.gn (n + r)

/-- A dot product with every product and every partial sum guarded. -/
def dotZC (a c : List ℤ) : Option ℤ := do
  let ps ← (List.zipWith (· * ·) a c).mapM B.gv
  sumC B ps

/-- `symMod`: the remainder, its double, and the shifted remainder. -/
def symModC (x : ℤ) (m : ℕ) : Option ℤ := do
  let r ← B.gv (x % (m : ℤ))
  let r2 ← B.gv (2 * r)
  if r2 > m then B.gv (r - m) else pure r

/-- `truncShiftZ`: the left-shifted significand or the right-shifted magnitude. -/
def truncShiftZC (m j : ℤ) : Option ℤ :=
  if m = 0 then some 0
  else if 0 ≤ j then B.gv (m * 2 ^ j.toNat)
  else if m.natAbs.log2 < (-j).toNat then some 0
  else do
    let q ← B.gn (m.natAbs / 2 ^ (-j).toNat)
    pure (if m < 0 then -(q : ℤ) else (q : ℤ))

/-- `dropsBits`: the remainder of the right shift. -/
def dropsBitsC (m j : ℤ) : Option Bool :=
  if m = 0 then some false
  else if 0 ≤ j then some false
  else if m.natAbs.log2 < (-j).toNat then some true
  else do
    let r ← B.gn (m.natAbs % 2 ^ (-j).toNat)
    pure (decide (r ≠ 0))

/-- `scaleShiftZ`: the largest entry exponent and the scaling exponent. -/
def scaleShiftZC (P : ℕ) (xs : List (ℤ × ℤ)) : Option ℤ := do
  let c ← maxEntryExpC B xs
  match c with
  | none => pure 0
  | some c => B.ge (P - c)

/-- `scaleTruncZ`: each shift amount, then the truncating shift. -/
def scaleTruncZC (s : ℤ) (xs : List (ℤ × ℤ)) : Option (List ℤ) :=
  xs.mapM fun a => do
    let j ← B.ge (a.2 + s)
    truncShiftZC B a.1 j

/-- `dropsZ`: each shift amount, then the test for dropped bits. -/
def dropsZC (s : ℤ) (xs : List (ℤ × ℤ)) : Option Bool := do
  let ds ← xs.mapM fun a => do
    let j ← B.ge (a.2 + s)
    dropsBitsC B a.1 j
  pure (ds.any id)

/-- `residueProduct`: the modulus as read, the residues, the output of the matrix multiplier read
back, and its residue. -/
def residueProductC (mult : MatrixMultiplier) (m : ℕ) (a c : List ℤ) : Option (Option ℤ) := do
  let _ ← B.gn m
  let ra ← a.mapM fun z => symModC B z m
  let rc ← c.mapM fun z => symModC B z m
  match mult ra rc with
  | none => pure none
  | some v =>
    match toInt? v with
    | none => pure none
    | some z => do
      let z' ← B.gv z
      let r ← B.gv (z' % (m : ℤ))
      pure (some r)

/-- `crt`: the modulus, the weights in use (those paired with a modulus) as read, the weighted
sum, and its symmetric residue. -/
def crtC (Bs : CRTBasis) (rs : List ℤ) : Option ℤ := do
  let M ← B.gn Bs.modulus
  let _ ← (List.zipWith (fun w _ => w) Bs.weights Bs.moduli).mapM B.gv
  let d ← dotZC B Bs.weights rs
  symModC B d M

/-- `ozaki2IntZ`: scaling, truncation, the residue products on the matrix multiplier, the CRT. -/
def ozaki2IntZC (mult : MatrixMultiplier) (Bs : CRTBasis) (P : ℕ) (xs ys : List (ℤ × ℤ)) :
    Option (Option ℤ) := do
  let sx ← scaleShiftZC B P xs
  let sy ← scaleShiftZC B P ys
  let a ← scaleTruncZC B sx xs
  let c ← scaleTruncZC B sy ys
  let rs ← Bs.moduli.mapM fun m => residueProductC B mult m a c
  match rs.mapM id with
  | none => pure none
  | some rs => do
    let N ← crtC B Bs rs
    pure (some N)

/-- `boundK`: the two sums of magnitudes, the count, and the bound. -/
def boundKC (a c : List ℤ) (dx dy : Bool) (k : ℕ) : Option ℤ := do
  let sc ← sumNC B (c.map Int.natAbs)
  let sck ← B.gn (sc + k)
  let sa ← sumNC B (a.map Int.natAbs)
  B.gv ((if dx then (sck : ℤ) else 0) + (if dy then (sa : ℤ) else 0))

/-- `ozaki2EnclosureZ`: the reconstructed product, its exponent, and the bound. -/
def ozaki2EnclosureZC (mult : MatrixMultiplier) (Bs : CRTBasis) (P : ℕ) (xs ys : List (ℤ × ℤ)) :
    Option (Option (ℤ × ℤ × ℤ × ℤ)) := do
  let N ← ozaki2IntZC B mult Bs P xs ys
  let sx ← scaleShiftZC B P xs
  let sy ← scaleShiftZC B P ys
  let a ← scaleTruncZC B sx xs
  let c ← scaleTruncZC B sy ys
  let dx ← dropsZC B sx xs
  let dy ← dropsZC B sy ys
  let ss ← B.ge (sx + sy)
  let q ← B.ge (-ss)
  let K ← boundKC B a c dx dy xs.length
  pure (N.map fun N => (N, q, K, q))

/-- `enclosureTestB`: the enclosure test on an integer enclosure. -/
def enclosureTestBC (p : ℕ) (emin emax : ℤ) (e : ℤ × ℤ × ℤ × ℤ) : Option (Option ℚ) :=
  roundEnclosureBC B p emin emax e.1 e.2.1 e.2.2.1 e.2.2.2 0

/-- `roundingTestB` with the checked enclosure test. -/
def roundingTestBC (p : ℕ) (emin emax : ℤ) :
    List (Option (ℤ × ℤ × ℤ × ℤ)) → Option ℚ → Option (Option ℚ)
  | [], exact => some exact
  | e :: es, exact =>
    match e with
    | none => roundingTestBC p emin emax es exact
    | some t => do
      let r ← enclosureTestBC B p emin emax t
      match r with
      | some w => pure (some w)
      | none => roundingTestBC p emin emax es exact

/-- **Correctly rounded Ozaki-II in integers, every integer guarded.** -/
def ozaki2CRJC (mult : MatrixMultiplier) (p : ℕ) (emin emax : ℤ) (cfgs : List (CRTBasis × ℕ)) (b smax : ℕ)
    (xs ys : List (ℤ × ℤ)) : Option (Option ℚ) := do
  let es ← cfgs.mapM fun c => ozaki2EnclosureZC B mult c.1 c.2 xs ys
  let ex ← ozaki1ExactFallbackIC B mult p emin emax b smax xs ys
  roundingTestBC B p emin emax es ex

end Checked

open Checked

/-! ## Sums and dot products -/

theorem natSum_le_of_mem : ∀ {l : List ℕ} {n : ℕ}, n ∈ l → n ≤ l.sum
  | [], _, h => by simp at h
  | a :: l, n, h => by
    rcases List.mem_cons.mp h with rfl | h
    · simp only [List.sum_cons]; omega
    · have := natSum_le_of_mem h; simp only [List.sum_cons]; omega

theorem mapM_gv_eq {B : Widths} {zs : List ℤ} (h : ∀ z ∈ zs, z.natAbs < 2 ^ B.R) :
    zs.mapM B.gv = some zs := by
  have := mapM_eq_some_map (f := B.gv) (g := id) (l := zs) fun z hz => Widths.gv_ok (h z hz)
  rwa [List.map_id] at this

theorem sumC_eq {B : Widths} : ∀ {zs : List ℤ}, (zs.map Int.natAbs).sum < 2 ^ B.R →
    sumC B zs = some zs.sum
  | [], _ => rfl
  | z :: zs, h => by
    simp only [List.map_cons, List.sum_cons] at h
    unfold sumC
    rw [sumC_eq (by omega)]
    simp only [Option.bind_eq_bind, Option.bind_some, List.sum_cons]
    have := natAbs_listSum_le zs
    exact Widths.gv_ok (Nat.lt_of_le_of_lt (Int.natAbs_add_le _ _) (by omega))

theorem sumNC_eq {B : Widths} : ∀ {ns : List ℕ}, ns.sum < 2 ^ B.R → sumNC B ns = some ns.sum
  | [], _ => rfl
  | n :: ns, h => by
    simp only [List.sum_cons] at h
    unfold sumNC
    rw [sumNC_eq (by omega)]
    simp only [Option.bind_eq_bind, Option.bind_some, List.sum_cons]
    exact Widths.gn_ok h

theorem dotZC_eq {B : Widths} {a c : List ℤ} (h : dotAbs a c < 2 ^ B.R) :
    dotZC B a c = some (dotZ a c) := by
  have hs : ((List.zipWith (· * ·) a c).map Int.natAbs).sum = dotAbs a c := by
    rw [List.map_zipWith]; rfl
  unfold dotZC
  rw [mapM_gv_eq fun z hz => Nat.lt_of_le_of_lt
    (Nat.le_trans (natSum_le_of_mem (List.mem_map_of_mem hz)) (Nat.le_of_eq hs)) h]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [sumC_eq (by rw [hs]; exact h)]
  rfl

/-! ## Residues, shifts and the CRT -/

theorem symModC_eq {B : Widths} {x : ℤ} {m : ℕ} (hm : 0 < m) (hm2 : 2 * m < 2 ^ B.R) : symModC B x m = some (symMod x m) := by
  have h1 := Int.emod_nonneg x (show (m : ℤ) ≠ 0 by omega)
  have h2 := Int.emod_lt_of_pos x (show (0 : ℤ) < m by omega)
  unfold symModC symMod
  rw [Widths.gv_ok (by omega)]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [Widths.gv_ok (by omega)]
  simp only [Option.bind_some]
  split
  · rw [Widths.gv_ok (by omega)]
  · rfl

theorem truncShiftZC_eq {B : Widths} {m j : ℤ} (hm : m.natAbs < 2 ^ B.R)
    (hres : (truncShiftZ m j).natAbs < 2 ^ B.R) : truncShiftZC B m j = some (truncShiftZ m j) := by
  unfold truncShiftZC
  unfold truncShiftZ at hres ⊢
  split
  · rfl
  · rename_i hm0
    rw [if_neg hm0] at hres
    split
    · rename_i hj
      rw [if_pos hj] at hres
      exact Widths.gv_ok hres
    · rename_i hj
      rw [if_neg hj] at hres
      split
      · rfl
      · rw [Widths.gn_ok (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hm)]
        rfl

theorem floorShiftZC_eq' {B : Widths} {m j : ℤ} (hm : m.natAbs < 2 ^ B.R) :
    dropsBitsC B m j = some (dropsBits m j) := by
  unfold dropsBitsC dropsBits
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · rw [Widths.gn_ok (Nat.lt_of_le_of_lt (Nat.mod_le _ _) hm)]
        rfl

theorem dropsBitsC_eq {B : Widths} {m j : ℤ} (hm : m.natAbs < 2 ^ B.R) :
    dropsBitsC B m j = some (dropsBits m j) := floorShiftZC_eq' hm

/-- The scaling exponent is at most `P + p + 1 + EM` in magnitude. -/
theorem scaleShiftZ_natAbs_le {P p EM : ℕ} {xs : List (ℤ × ℤ)} (hx : EntriesIn p EM xs) :
    (scaleShiftZ P xs).natAbs ≤ P + p + 1 + EM := by
  unfold scaleShiftZ
  cases h : maxEntryExp xs with
  | none => simp
  | some c =>
    simp only
    obtain ⟨_, a, ha, hac⟩ := maxExp_eq_some h
    have := entryExp_natAbs_le (hx a ha).1 (hx a ha).2 hac
    omega

theorem scaleShiftZC_eq {B : Widths} {P p EM : ℕ} {xs : List (ℤ × ℤ)} (hx : EntriesIn p EM xs)
    (hR : p + 1 ≤ B.R) (hX : P + p + 1 + EM < 2 ^ B.X) :
    scaleShiftZC B P xs = some (scaleShiftZ P xs) := by
  have hb := scaleShiftZ_natAbs_le (P := P) hx
  unfold scaleShiftZC
  rw [maxEntryExpC_eq hR (by omega) hx]
  simp only [Option.bind_eq_bind, Option.bind_some]
  unfold scaleShiftZ at hb ⊢
  cases h : maxEntryExp xs with
  | none => rfl
  | some c => simp only [h] at hb ⊢; exact Widths.ge_ok (by omega)

theorem scaleTruncZC_eq {B : Widths} {P p EM : ℕ} {xs : List (ℤ × ℤ)} (hx : EntriesIn p EM xs)
    (hpR : p ≤ B.R) (hPR : P < B.R) (hX : EM + P + p + 1 + EM < 2 ^ B.X) :
    scaleTruncZC B (scaleShiftZ P xs) xs = some (scaleTruncZ (scaleShiftZ P xs) xs) := by
  have hb := scaleShiftZ_natAbs_le (P := P) hx
  have hres := scaleTruncZ_natAbs_le P xs
  unfold scaleTruncZC scaleTruncZ
  apply mapM_eq_some_map
  intro a ha
  have hj : (a.2 + scaleShiftZ P xs).natAbs < 2 ^ B.X := by
    have := (hx a ha).2
    have := Int.natAbs_add_le a.2 (scaleShiftZ P xs)
    omega
  rw [Widths.ge_ok hj]
  simp only [Option.bind_eq_bind, Option.bind_some]
  have hr := hres _ (List.mem_map_of_mem ha)
  have hP : 2 ^ P < 2 ^ B.R := Nat.pow_lt_pow_right (by decide) hPR
  exact truncShiftZC_eq (lt_two_pow_of_le (hx a ha).1 hpR) (by omega)

theorem dropsZC_eq {B : Widths} {P p EM : ℕ} {xs : List (ℤ × ℤ)} (hx : EntriesIn p EM xs)
    (hpR : p ≤ B.R) (hX : EM + P + p + 1 + EM < 2 ^ B.X) :
    dropsZC B (scaleShiftZ P xs) xs = some (dropsZ (scaleShiftZ P xs) xs) := by
  have hb := scaleShiftZ_natAbs_le (P := P) hx
  unfold dropsZC dropsZ
  rw [mapM_eq_some_map (g := fun a => dropsBits a.1 (a.2 + scaleShiftZ P xs)) fun a ha => by
    have hj : (a.2 + scaleShiftZ P xs).natAbs < 2 ^ B.X := by
      have := (hx a ha).2
      have := Int.natAbs_add_le a.2 (scaleShiftZ P xs)
      omega
    rw [Widths.ge_ok hj]
    simp only [Option.bind_eq_bind, Option.bind_some]
    exact dropsBitsC_eq (lt_two_pow_of_le (hx a ha).1 hpR)]
  simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, List.any_map]
  rfl

theorem residueProductC_eq {B : Widths} {mult : MatrixMultiplier} {b bound : ℕ}
    (hmult : mult.ExactOn b bound) {m : ℕ} (hm : 0 < m) (hmb : m ≤ 2 ^ (b + 1)) {a c : List ℤ}
    (hlen : a.length = c.length) (hbound : a.length * (2 ^ b * 2 ^ b) ≤ bound)
    (hm2 : 2 * m < 2 ^ B.R) (hbud : bound < 2 ^ B.R) :
    residueProductC B mult m a c = some (residueProduct mult m a c) := by
  rw [residueProduct_eq hmult hm hmb hlen hbound]
  have hres : ∀ z : ℤ, (symMod z m).natAbs ≤ 2 ^ b := by
    intro z
    have := natAbs_symMod_le z hm
    rw [Nat.pow_succ] at hmb
    omega
  have hx : ∀ z ∈ a.map fun z => symMod z m, z.natAbs ≤ 2 ^ b := by
    intro z hz; obtain ⟨w, _, rfl⟩ := List.mem_map.mp hz; exact hres w
  have hy : ∀ z ∈ c.map fun z => symMod z m, z.natAbs ≤ 2 ^ b := by
    intro z hz; obtain ⟨w, _, rfl⟩ := List.mem_map.mp hz; exact hres w
  have hab : dotAbs (a.map fun z => symMod z m) (c.map fun z => symMod z m) ≤ bound :=
    Nat.le_trans (dotAbs_le _ _ _ _ hx hy) (by simpa using hbound)
  unfold residueProductC
  rw [Widths.gn_ok (by omega)]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [mapM_eq_some_map (g := fun z => symMod z m) fun _ _ => symModC_eq hm hm2,
    mapM_eq_some_map (g := fun z => symMod z m) fun _ _ => symModC_eq hm hm2]
  simp only [Option.bind_some]
  rw [hmult _ _ (by simpa using hlen) hx hy hab]
  simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, toInt?_intCast]
  have hz := Nat.le_trans (natAbs_dotZ_le (a.map fun z => symMod z m) (c.map fun z => symMod z m))
    hab
  rw [Widths.gv_ok (by omega)]
  simp only [Option.bind_some]
  have h1 := Int.emod_nonneg (dotZ (a.map fun z => symMod z m) (c.map fun z => symMod z m))
    (show (m : ℤ) ≠ 0 by omega)
  have h2 := Int.emod_lt_of_pos (dotZ (a.map fun z => symMod z m) (c.map fun z => symMod z m))
    (show (0 : ℤ) < m by omega)
  rw [Widths.gv_ok (by omega)]
  rfl

/-- The weights times the moduli, summed: a bound on every partial sum of the CRT combination. -/
def crtSize (Bs : CRTBasis) : ℕ :=
  (List.zipWith (fun w m => w.natAbs * m) Bs.weights Bs.moduli).sum

/-- Each residue is below its modulus in magnitude, entry by entry. -/
def ResBelow : List ℤ → List ℕ → Prop
  | [], [] => True
  | r :: rs, m :: ms => r.natAbs < m ∧ ResBelow rs ms
  | _, _ => False

theorem dotAbs_le_crtSize : ∀ (ws : List ℤ) (ms : List ℕ) (rs : List ℤ), ResBelow rs ms →
    dotAbs ws rs ≤ (List.zipWith (fun w m => w.natAbs * m) ws ms).sum
  | [], _, _, _ => by simp [dotAbs]
  | _ :: _, [], [], _ => by simp [dotAbs]
  | _ :: _, [], _ :: _, h => by simp [ResBelow] at h
  | _ :: _, _ :: _, [], h => by simp [ResBelow] at h
  | w :: ws, m :: ms, r :: rs, h => by
    obtain ⟨hr, h⟩ := h
    have ih := dotAbs_le_crtSize ws ms rs h
    unfold dotAbs at ih ⊢
    simp only [List.zipWith_cons_cons, List.sum_cons]
    have : (w * r).natAbs ≤ w.natAbs * m := by
      rw [Int.natAbs_mul]; exact Nat.mul_le_mul_left _ (Nat.le_of_lt hr)
    omega

/-- A weight paired with a modulus is at most `crtSize`: every modulus is positive (each residue is
below its modulus). -/
theorem weight_le_crtSize_aux : ∀ {ws : List ℤ} {ms : List ℕ} {rs : List ℤ}, ResBelow rs ms →
    ∀ w ∈ List.zipWith (fun w _ => w) ws ms,
      w.natAbs ≤ (List.zipWith (fun w m => w.natAbs * m) ws ms).sum
  | [], _, _, _, w, hw => by simp at hw
  | _ :: _, [], _, _, w, hw => by simp at hw
  | v :: ws, m :: ms, [], h, _, _ => by simp [ResBelow] at h
  | v :: ws, m :: ms, r :: rs, h, w, hw => by
    obtain ⟨hr, h⟩ := h
    simp only [List.zipWith_cons_cons, List.mem_cons, List.sum_cons] at hw ⊢
    rcases hw with rfl | hw
    · have : w.natAbs ≤ w.natAbs * m := Nat.le_mul_of_pos_right _ (by omega)
      omega
    · have := weight_le_crtSize_aux h w hw
      omega

theorem weight_le_crtSize {Bs : CRTBasis} {rs : List ℤ} (hrs : ResBelow rs Bs.moduli) {w : ℤ}
    (hw : w ∈ List.zipWith (fun w _ => w) Bs.weights Bs.moduli) : w.natAbs ≤ crtSize Bs :=
  weight_le_crtSize_aux hrs w hw

theorem crtC_eq {B : Widths} {Bs : CRTBasis} {rs : List ℤ} (hM : 0 < Bs.modulus)
    (hrs : ResBelow rs Bs.moduli) (hsize : crtSize Bs < 2 ^ B.R)
    (hM2 : 2 * Bs.modulus < 2 ^ B.R) : crtC B Bs rs = some (crt Bs rs) := by
  have hd := Nat.lt_of_le_of_lt (dotAbs_le_crtSize Bs.weights Bs.moduli rs hrs) hsize
  unfold crtC crt
  rw [Widths.gn_ok (by omega)]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [mapM_gv_eq fun w hw => Nat.lt_of_le_of_lt (weight_le_crtSize hrs hw) hsize]
  simp only [Option.bind_some]
  rw [dotZC_eq hd]
  simp only [Option.bind_some]
  exact symModC_eq hM hM2

/-! ## The enclosure -/

theorem residues_lt {mult : MatrixMultiplier} {a c : List ℤ} : ∀ {ms : List ℕ} {rs : List ℤ},
    (∀ m ∈ ms, 0 < m) → (ms.mapM fun m => residueProduct mult m a c) = some rs → ResBelow rs ms
  | [], rs, _, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; trivial
  | m :: ms, rs, hm, h => by
    rw [List.mapM_cons] at h
    simp only [Option.bind_eq_bind, Option.pure_def] at h
    cases hr : residueProduct mult m a c with
    | none => simp [hr] at h
    | some r =>
      cases hrs : ms.mapM fun m => residueProduct mult m a c with
      | none => simp [hr, hrs] at h
      | some rs' =>
        simp only [hr, hrs, Option.bind_some, Option.some.injEq] at h
        subst h
        refine ⟨?_, residues_lt (fun m' hm' => hm m' (List.mem_cons_of_mem _ hm')) hrs⟩
        have hm0 := hm m List.mem_cons_self
        unfold residueProduct at hr
        simp only [Option.bind_eq_bind] at hr
        cases hv : mult (a.map fun z => symMod z m) (c.map fun z => symMod z m) with
        | none => simp [hv] at hr
        | some v =>
          cases ht : toInt? v with
          | none => simp [hv, ht] at hr
          | some z =>
            simp only [hv, ht, Option.bind_some, Option.pure_def, Option.some.injEq] at hr
            subst hr
            have h1 := Int.emod_nonneg z (show (m : ℤ) ≠ 0 by omega)
            have h2 := Int.emod_lt_of_pos z (show (0 : ℤ) < m by omega)
            omega

theorem ozaki2IntZC_eq {B : Widths} {mult : MatrixMultiplier} {b bound : ℕ} (hmult : mult.ExactOn b bound)
    {Bs : CRTBasis} {P p EM : ℕ} {xs ys : List (ℤ × ℤ)} (hlen : xs.length = ys.length)
    (hbound : xs.length * (2 ^ b * 2 ^ b) ≤ bound) (hx : EntriesIn p EM xs)
    (hy : EntriesIn p EM ys) (hm : ∀ m ∈ Bs.moduli, 0 < m ∧ m ≤ 2 ^ (b + 1))
    (hM : 0 < Bs.modulus) (hsize : crtSize Bs < 2 ^ B.R) (hM2 : 2 * Bs.modulus < 2 ^ B.R)
    (hpR : p + 1 ≤ B.R) (hPR : P < B.R) (hbR : b + 2 < B.R) (hbud : bound < 2 ^ B.R)
    (hX : EM + P + p + 1 + EM < 2 ^ B.X) :
    ozaki2IntZC B mult Bs P xs ys = some (ozaki2IntZ mult Bs P xs ys) := by
  have hP : 2 ^ P < 2 ^ B.R := Nat.pow_lt_pow_right (by decide) hPR
  have hb2 : 2 ^ (b + 2) < 2 ^ B.R := Nat.pow_lt_pow_right (by decide) hbR
  unfold ozaki2IntZC ozaki2IntZ
  rw [scaleShiftZC_eq hx hpR (by omega), scaleShiftZC_eq hy hpR (by omega)]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [scaleTruncZC_eq hx (by omega) hPR hX, scaleTruncZC_eq hy (by omega) hPR hX]
  simp only [Option.bind_some]
  have hla : (scaleTruncZ (scaleShiftZ P xs) xs).length = (scaleTruncZ (scaleShiftZ P ys) ys).length :=
    by simp [scaleTruncZ, hlen]
  have hba : (scaleTruncZ (scaleShiftZ P xs) xs).length * (2 ^ b * 2 ^ b) ≤ bound := by
    simpa [scaleTruncZ] using hbound
  rw [mapM_eq_some_map (g := fun m => residueProduct mult m (scaleTruncZ (scaleShiftZ P xs) xs)
      (scaleTruncZ (scaleShiftZ P ys) ys)) fun m hmem => by
    obtain ⟨hm0, hmb⟩ := hm m hmem
    have : 2 * m < 2 ^ B.R := by rw [Nat.pow_succ] at hmb; rw [Nat.pow_succ, Nat.pow_succ] at hb2; omega
    exact residueProductC_eq hmult hm0 hmb hla hba this hbud]
  simp only [Option.bind_some]
  have hmap : (Bs.moduli.map fun m => residueProduct mult m (scaleTruncZ (scaleShiftZ P xs) xs)
      (scaleTruncZ (scaleShiftZ P ys) ys)).mapM id =
      (Bs.moduli.mapM fun m => residueProduct mult m (scaleTruncZ (scaleShiftZ P xs) xs)
        (scaleTruncZ (scaleShiftZ P ys) ys)) := by
    rw [List.mapM_map]; rfl
  rw [hmap]
  cases hrs : (Bs.moduli.mapM fun m => residueProduct mult m (scaleTruncZ (scaleShiftZ P xs) xs)
      (scaleTruncZ (scaleShiftZ P ys) ys)) with
  | none => rfl
  | some rs =>
    simp only [Option.map_some]
    rw [crtC_eq hM (residues_lt (fun m hm' => (hm m hm').1) hrs) hsize hM2]
    rfl

theorem boundKC_eq {B : Widths} {a c : List ℤ} {dx dy : Bool} {k M : ℕ}
    (ha : ∀ z ∈ a, z.natAbs ≤ M) (hc : ∀ z ∈ c, z.natAbs ≤ M) (hla : a.length = k)
    (hlc : c.length = k) (hR : 2 * k * (M + 1) < 2 ^ B.R) :
    boundKC B a c dx dy k = some (boundK a c dx dy k) := by
  have hsa : (a.map Int.natAbs).sum ≤ k * M := by
    rw [← hla]; exact sum_natAbs_le_mul ha
  have hsc : (c.map Int.natAbs).sum ≤ k * M := by
    rw [← hlc]; exact sum_natAbs_le_mul hc
  have hkM : k * M + k ≤ k * (M + 1) := Nat.le_of_eq (Nat.mul_succ k M).symm
  have h2 : 2 * k * (M + 1) = k * (M + 1) + k * (M + 1) := by
    rw [Nat.mul_assoc, Nat.two_mul]
  unfold boundKC boundK
  rw [sumNC_eq (by omega)]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [Widths.gn_ok (by omega)]
  simp only [Option.bind_some]
  rw [sumNC_eq (by omega)]
  simp only [Option.bind_some]
  apply Widths.gv_ok
  cases dx <;> cases dy <;> simp <;> omega

/-- The requirement on `R` for one Ozaki-II configuration: the reconstructed product (at most
`M/2`) and the bound `K` (at most `2k(2^P + 1)`) below `2^E`, `E = max (bitlen M) (P + bitlen k +
3)`, and the enclosure test's `D = E + p + 2`, plus `3`. -/
def ozaki2R (Bs : CRTBasis) (P p k : ℕ) : ℕ :=
  max (bitlen Bs.modulus) (P + bitlen k + 3) + p + 7

/-- The requirement on `X` for one Ozaki-II configuration. -/
def ozaki2X (Bs : CRTBasis) (P p EM k : ℕ) (emin emax : ℤ) (R : ℕ) : ℕ :=
  8 * (P + p + 1 + EM) + 2 * ozaki2R Bs P p k + emin.natAbs + emax.natAbs + 2 * p + 2 * R + 8

theorem ozaki2EnclosureZC_eq {B : Widths} {mult : MatrixMultiplier} {b bound : ℕ}
    (hmult : mult.ExactOn b bound) {Bs : CRTBasis} {P p EM : ℕ} {xs ys : List (ℤ × ℤ)}
    (hlen : xs.length = ys.length) (hbound : xs.length * (2 ^ b * 2 ^ b) ≤ bound)
    (hx : EntriesIn p EM xs) (hy : EntriesIn p EM ys)
    (hm : ∀ m ∈ Bs.moduli, 0 < m ∧ m ≤ 2 ^ (b + 1)) (hM : 0 < Bs.modulus)
    (hsize : crtSize Bs < 2 ^ B.R) (hM2 : 2 * Bs.modulus < 2 ^ B.R)
    (hpR : p + 1 ≤ B.R) (hRq : ozaki2R Bs P p xs.length ≤ B.R) (hbR : b + 2 < B.R)
    (hbud : bound < 2 ^ B.R) (hX : EM + P + p + 1 + EM < 2 ^ B.X)
    (hXq : 4 * (P + p + 1 + EM) < 2 ^ B.X) :
    ozaki2EnclosureZC B mult Bs P xs ys = some (ozaki2EnclosureZ mult Bs P xs ys) := by
  unfold ozaki2R at hRq
  have hPR : P < B.R := by omega
  have hP : 2 ^ P < 2 ^ B.R := Nat.pow_lt_pow_right (by decide) hPR
  have hbx := scaleShiftZ_natAbs_le (P := P) hx
  have hby := scaleShiftZ_natAbs_le (P := P) hy
  unfold ozaki2EnclosureZC ozaki2EnclosureZ
  rw [ozaki2IntZC_eq hmult hlen hbound hx hy hm hM hsize hM2 hpR hPR hbR hbud hX]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [scaleShiftZC_eq hx hpR (by omega), scaleShiftZC_eq hy hpR (by omega)]
  simp only [Option.bind_some]
  rw [scaleTruncZC_eq hx (by omega) hPR hX, scaleTruncZC_eq hy (by omega) hPR hX]
  simp only [Option.bind_some]
  rw [dropsZC_eq hx (by omega) hX, dropsZC_eq hy (by omega) hX]
  simp only [Option.bind_some]
  have hs := Int.natAbs_add_le (scaleShiftZ P xs) (scaleShiftZ P ys)
  rw [Widths.ge_ok (by omega)]
  simp only [Option.bind_some]
  rw [Widths.ge_ok (by rw [Int.natAbs_neg]; omega)]
  simp only [Option.bind_some]
  have hk : 2 * xs.length * (2 ^ P + 1) < 2 ^ B.R := by
    have h1 : 2 * xs.length * (2 ^ P + 1) < 2 ^ (P + bitlen xs.length + 3) := by
      have hl := lt_two_pow_bitlen xs.length
      have : 2 ^ (P + bitlen xs.length + 3) = 2 ^ P * 2 ^ bitlen xs.length * 8 := by
        rw [Nat.pow_add, Nat.pow_add]
      rw [this]
      have : 2 * xs.length * (2 ^ P + 1) ≤ 2 * xs.length * (2 * 2 ^ P) :=
        Nat.mul_le_mul_left _ (by have := Nat.one_le_two_pow (n := P); omega)
      have : xs.length * 2 ^ P < 2 ^ bitlen xs.length * 2 ^ P :=
        Nat.mul_lt_mul_of_pos_right hl (Nat.two_pow_pos P)
      grind
    exact Nat.lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by decide) (by omega))
  rw [boundKC_eq (M := 2 ^ P) (fun z hz => scaleTruncZ_natAbs_le P xs z hz)
    (fun z hz => scaleTruncZ_natAbs_le P ys z hz) (by simp [scaleTruncZ])
    (by simp [scaleTruncZ, hlen]) hk]
  rfl

/-! ## The rounding test, the fallback and the scheme -/

theorem enclosureTestBC_eq {B : Widths} {p E D : ℕ} {emin emax : ℤ} {N q K : ℤ}
    (hN : N.natAbs < 2 ^ E) (hK : K.natAbs < 2 ^ E) (hED : E + 2 ≤ D) (hpD : p + 2 ≤ D)
    (hR : D + 3 ≤ B.R)
    (hX : 4 * q.natAbs + 2 * D + emin.natAbs + emax.natAbs + 2 * p + 2 * B.R + 8 < 2 ^ B.X) :
    enclosureTestBC B p emin emax (N, q, K, q) = some (enclosureTestB p emin emax (N, q, K, q)) := by
  unfold enclosureTestBC enclosureTestB
  simp only
  have h0 : (q - min q q).toNat = 0 := by simp
  exact roundEnclosureBC_eq (E := E) (D := D) (by rw [h0]; simpa using hN)
    (by rw [h0]; simpa using hK) (by rw [h0]; simp; exact Nat.two_pow_pos E) hED hpD hR (by omega)

theorem roundingTestBC_eq {B : Widths} {p : ℕ} {emin emax : ℤ} (exact : Option ℚ) :
    ∀ es : List (Option (ℤ × ℤ × ℤ × ℤ)),
      (∀ e ∈ es, ∀ t, e = some t → enclosureTestBC B p emin emax t = some (enclosureTestB p emin emax t)) →
      roundingTestBC B p emin emax es exact = some (roundingTestB p emin emax es exact)
  | [], _ => rfl
  | e :: es, h => by
    have ih := roundingTestBC_eq exact es fun e' he' => h e' (List.mem_cons_of_mem _ he')
    unfold roundingTestBC roundingTestB
    cases e with
    | none => exact ih
    | some t =>
      dsimp only
      rw [h _ List.mem_cons_self t rfl]
      simp only [Option.bind_eq_bind, Option.bind_some]
      cases enclosureTestB p emin emax t with
      | some w => rfl
      | none => exact ih

/-- The reconstructed product of a configuration is at most `M/2`, and the bound `K` at most
`2k(2^P + 1)`. -/
theorem ozaki2EnclosureZ_bounds {mult : MatrixMultiplier} {Bs : CRTBasis} {P : ℕ} {xs ys : List (ℤ × ℤ)}
    (hlen : xs.length = ys.length) (hM : 0 < Bs.modulus) {t : ℤ × ℤ × ℤ × ℤ}
    (ht : ozaki2EnclosureZ mult Bs P xs ys = some t) :
    t.1.natAbs ≤ Bs.modulus ∧ t.2.2.1.natAbs ≤ 2 * xs.length * (2 ^ P + 1) ∧ t.2.1 = t.2.2.2 ∧
      t.2.1 = -(scaleShiftZ P xs + scaleShiftZ P ys) := by
  unfold ozaki2EnclosureZ at ht
  cases hN : ozaki2IntZ mult Bs P xs ys with
  | none => simp [hN] at ht
  | some N =>
    simp only [hN, Option.map_some, Option.some.injEq] at ht
    subst ht
    refine ⟨?_, ?_, rfl, rfl⟩
    · unfold ozaki2IntZ crt at hN
      cases hrs : Bs.moduli.mapM fun m => residueProduct mult m
          (scaleTruncZ (scaleShiftZ P xs) xs) (scaleTruncZ (scaleShiftZ P ys) ys) with
      | none => simp [hrs] at hN
      | some rs =>
        simp only [hrs, Option.map_some, Option.some.injEq] at hN
        subst hN
        have := natAbs_symMod_le (dotZ Bs.weights rs) hM
        simp only; omega
    · have hb := boundK_le (k := xs.length) (n := 2 ^ P) (dx := dropsZ (scaleShiftZ P xs) xs)
        (dy := dropsZ (scaleShiftZ P ys) ys) (by simp [scaleTruncZ]) (by simp [scaleTruncZ, hlen])
        (fun z hz => scaleTruncZ_natAbs_le P xs z hz) (fun z hz => scaleTruncZ_natAbs_le P ys z hz)
      simp only
      have : xs.length * (2 * 2 ^ P + 1) ≤ 2 * xs.length * (2 ^ P + 1) := by grind
      omega

/-- **One theorem bounding every integer of correctly rounded Ozaki-II.** On binary entries with an
exact matrix multiplier, for configurations with moduli in `(0, 2^(b+1)]`, if `R` and `X` meet the
requirements of every configuration (`ozaki2R`, `ozaki2X`, `crtSize`, `2M`) and of the exact
fallback (`exactR`, `exactX`), the checked function returns exactly what `ozaki2CRJ` returns: no
guard ever fails. -/
theorem ozaki2CRJC_eq {B : Widths} {mult : MatrixMultiplier} {b bound : ℕ} (hmult : mult.ExactOn b bound)
    {p EM smax : ℕ} {emin emax : ℤ} {cfgs : List (CRTBasis × ℕ)} {xs ys : List (ℤ × ℤ)}
    (hlen : xs.length = ys.length) (hbound : xs.length * (2 ^ b * 2 ^ b) ≤ bound)
    (hx : EntriesIn p EM xs) (hy : EntriesIn p EM ys)
    (hcfg : ∀ c ∈ cfgs, (∀ m ∈ c.1.moduli, 0 < m ∧ m ≤ 2 ^ (b + 1)) ∧ 0 < c.1.modulus ∧
      crtSize c.1 < 2 ^ B.R ∧ 2 * c.1.modulus < 2 ^ B.R ∧ ozaki2R c.1 c.2 p xs.length ≤ B.R ∧
      ozaki2X c.1 c.2 p EM xs.length emin emax B.R < 2 ^ B.X)
    (hRe : exactR p smax bound ≤ B.R) (hRb : p + b + 3 ≤ B.R)
    (hXe : exactX p b EM smax bound emin emax B.R < 2 ^ B.X) :
    ozaki2CRJC B mult p emin emax cfgs b smax xs ys =
      some (ozaki2CRJ mult p emin emax cfgs b smax xs ys) := by
  have hbud : bound < 2 ^ B.R := by
    unfold exactR at hRe
    exact Nat.lt_of_lt_of_le (lt_two_pow_bitlen bound) (Nat.pow_le_pow_right (by decide) (by omega))
  unfold ozaki2CRJC ozaki2CRJ
  rw [mapM_eq_some_map (g := fun c => ozaki2EnclosureZ mult c.1 c.2 xs ys) fun c hc => by
    obtain ⟨hm, hM, hsize, hM2, hRq, hXq⟩ := hcfg c hc
    unfold ozaki2X at hXq
    exact ozaki2EnclosureZC_eq hmult hlen hbound hx hy hm hM hsize hM2 (by omega) hRq (by omega)
      hbud (by omega) (by omega)]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [ozaki1ExactFallbackIC_eq hmult hlen hbound hx hy hRe hRb hXe]
  simp only [Option.bind_some]
  apply roundingTestBC_eq
  intro e he t het
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp he
  obtain ⟨hm, hM, hsize, hM2, hRq, hXq⟩ := hcfg c hc
  obtain ⟨hN, hK, hqc, hq⟩ := ozaki2EnclosureZ_bounds hlen hM het
  obtain ⟨N, q, K, q'⟩ := t
  simp only at hN hK hqc hq
  subst hqc
  unfold ozaki2R at hRq
  unfold ozaki2X ozaki2R at hXq
  have hbx := scaleShiftZ_natAbs_le (P := c.2) hx
  have hby := scaleShiftZ_natAbs_le (P := c.2) hy
  have hqb : q.natAbs ≤ 2 * (c.2 + p + 1 + EM) := by
    rw [hq, Int.natAbs_neg]
    have := Int.natAbs_add_le (scaleShiftZ c.2 xs) (scaleShiftZ c.2 ys)
    omega
  have hE1 : c.1.modulus < 2 ^ max (bitlen c.1.modulus) (c.2 + bitlen xs.length + 3) :=
    Nat.lt_of_lt_of_le (lt_two_pow_bitlen _) (Nat.pow_le_pow_right (by decide) (by omega))
  have hE2 : 2 * xs.length * (2 ^ c.2 + 1) <
      2 ^ max (bitlen c.1.modulus) (c.2 + bitlen xs.length + 3) := by
    have h1 : 2 * xs.length * (2 ^ c.2 + 1) < 2 ^ (c.2 + bitlen xs.length + 3) := by
      have hl := lt_two_pow_bitlen xs.length
      have : 2 ^ (c.2 + bitlen xs.length + 3) = 2 ^ c.2 * 2 ^ bitlen xs.length * 8 := by
        rw [Nat.pow_add, Nat.pow_add]
      rw [this]
      have : 2 * xs.length * (2 ^ c.2 + 1) ≤ 2 * xs.length * (2 * 2 ^ c.2) :=
        Nat.mul_le_mul_left _ (by have := Nat.one_le_two_pow (n := c.2); omega)
      have : xs.length * 2 ^ c.2 < 2 ^ bitlen xs.length * 2 ^ c.2 :=
        Nat.mul_lt_mul_of_pos_right hl (Nat.two_pow_pos c.2)
      grind
    exact Nat.lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by decide) (by omega))
  exact enclosureTestBC_eq (E := max (bitlen c.1.modulus) (c.2 + bitlen xs.length + 3))
    (D := max (bitlen c.1.modulus) (c.2 + bitlen xs.length + 3) + p + 2) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)

/-! ## Concrete widths -/

/-- The twelve pairwise coprime moduli at most `4096` for FP64 Ozaki-II (`M ≈ 2^144`). -/
def fp64Moduli : List ℕ := [4096, 4095, 4093, 4091, 4087, 4079, 4073, 4063, 4061, 4057, 4051, 4049]

def fp64Basis : CRTBasis := crtBasis fp64Moduli

/-- Six pairwise coprime moduli at most `4096` for binary32 Ozaki-II (`M ≈ 2^72`). -/
def fp32Moduli6 : List ℕ := [4096, 4095, 4093, 4091, 4087, 4079]

def fp32Basis6 : CRTBasis := crtBasis fp32Moduli6

theorem fp64Basis_facts : (∀ m ∈ fp64Basis.moduli, 0 < m ∧ m ≤ 2 ^ (11 + 1)) ∧
    0 < fp64Basis.modulus ∧ crtSize fp64Basis < 2 ^ 159 ∧ 2 * fp64Basis.modulus < 2 ^ 145 ∧
    bitlen fp64Basis.modulus = 144 := by decide +kernel

theorem fp32Basis6_facts : (∀ m ∈ fp32Basis6.moduli, 0 < m ∧ m ≤ 2 ^ (11 + 1)) ∧
    0 < fp32Basis6.modulus ∧ crtSize fp32Basis6 < 2 ^ 85 ∧ 2 * fp32Basis6.modulus < 2 ^ 73 ∧
    bitlen fp32Basis6.modulus = 72 := by decide +kernel

theorem bitlen_length_le {k : ℕ} (hk : k ≤ 2 ^ 20) : bitlen k ≤ 21 := bitlen_le_iff.mpr (by omega)

/-- **Every integer of correctly rounded FP64 Ozaki-II fits 264 bits, every exponent and counter
24 bits**: on binary64 entries, `k ≤ 2^20`, the twelve moduli at most `4096` with any `P ≤ 69`,
`11`-bit slices and at most `175` slices in the exact fallback, with an exact matrix multiplier. -/
theorem ozaki2CRJC_binary64 {mult : MatrixMultiplier} {xs ys : List (ℤ × ℤ)} {cfgs : List (CRTBasis × ℕ)}
    (hmult : mult.ExactOn 11 (xs.length * (2 ^ 11 * 2 ^ 11))) (hlen : xs.length = ys.length)
    (hk : xs.length ≤ 2 ^ 20) (hx : ∀ a ∈ xs, FormatEntry 53 (-1022) 1023 a)
    (hy : ∀ a ∈ ys, FormatEntry 53 (-1022) 1023 a)
    (hcfgs : ∀ c ∈ cfgs, c.1 = fp64Basis ∧ c.2 ≤ 69) :
    ozaki2CRJC ⟨264, 24⟩ mult 53 (-1022) 1023 cfgs 11 175 xs ys =
      some (ozaki2CRJ mult 53 (-1022) 1023 cfgs 11 175 xs ys) := by
  have hE : ((-1022 : ℤ) - ((53 : ℕ) - 1 : ℤ)).natAbs ≤ 1074 ∧
      ((1023 : ℤ) - ((53 : ℕ) - 1 : ℤ)).natAbs ≤ 1074 := by decide
  have hbud := bitlen_dotAbsBound_le hk
  have hbk := bitlen_length_le hk
  have hW : exactW 53 175 = 72 := by decide
  have hb2 : bitlen (175 * 175 + 2) = 15 := by decide
  obtain ⟨hm, hM, hsize, hM2, hbl⟩ := fp64Basis_facts
  refine ozaki2CRJC_eq hmult hlen (Nat.le_refl _) (entriesIn_of_format hE hx)
    (entriesIn_of_format hE hy) ?_ ?_ (by decide) ?_
  · intro c hc
    obtain ⟨h1, h2⟩ := hcfgs c hc
    rw [h1]
    refine ⟨hm, hM, Nat.lt_of_lt_of_le hsize (Nat.pow_le_pow_right (by decide) (by decide)),
      Nat.lt_of_lt_of_le hM2 (Nat.pow_le_pow_right (by decide) (by decide)), ?_, ?_⟩
    · unfold ozaki2R; rw [hbl]; simp only; omega
    · unfold ozaki2X ozaki2R; rw [hbl]; simp only
      have : (-1022 : ℤ).natAbs = 1022 := by decide
      have : (1023 : ℤ).natAbs = 1023 := by decide
      omega
  · unfold exactR; rw [hW, hb2]; simp only; omega
  · unfold exactX; rw [hW]; simp only
    have : (-1022 : ℤ).natAbs = 1022 := by decide
    have : (1023 : ℤ).natAbs = 1023 := by decide
    omega

/-- **FP64 Ozaki-II, every integer within 264 bits, correctly rounded**: with configurations that
also meet the CRT range condition, the checked function returns the IEEE binary64 round to nearest
of `x · y`. -/
theorem ozaki2CRJC_binary64_eq {mult : MatrixMultiplier} {xs ys : List (ℤ × ℤ)} {cfgs : List (CRTBasis × ℕ)}
    (hmult : mult.ExactOn 11 (xs.length * (2 ^ 11 * 2 ^ 11))) (hlen : xs.length = ys.length)
    (hk : xs.length ≤ 2 ^ 20) (hx : ∀ a ∈ xs, FormatEntry 53 (-1022) 1023 a)
    (hy : ∀ a ∈ ys, FormatEntry 53 (-1022) 1023 a)
    (hcfgs : ∀ c ∈ cfgs, c.1 = fp64Basis ∧ c.2 ≤ 69)
    (hrange : ∀ c ∈ cfgs, 2 * xs.length * (2 ^ c.2 * 2 ^ c.2) < c.1.modulus) :
    ozaki2CRJC ⟨264, 24⟩ mult 53 (-1022) 1023 cfgs 11 175 xs ys =
      some (rne64 (dot (entryVals xs) (entryVals ys))) := by
  rw [ozaki2CRJC_binary64 hmult hlen hk hx hy hcfgs,
    ozaki2CRJ64_eq hmult (by decide) (by decide) (fun c hc => by
      obtain ⟨h1, _⟩ := hcfgs c hc
      refine ⟨?_, ?_, hrange c hc⟩
      · rw [h1]; decide +kernel
      · rw [h1]; exact fun m hm => (fp64Basis_facts.1 m hm).2) hlen (Nat.le_refl _)
    (fun v hv => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv; exact (hx a ha).formatValue)
    (fun v hv => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv; exact (hy a ha).formatValue)]

/-- **Every integer of correctly rounded binary32 Ozaki-II fits 161 bits, every exponent and
counter 17 bits**: on binary32 entries, `k ≤ 2^20`, six moduli at most `4096` with any `P ≤ 34`,
`11`-bit slices and at most `24` slices in the exact fallback. -/
theorem ozaki2CRJC_binary32 {mult : MatrixMultiplier} {xs ys : List (ℤ × ℤ)} {cfgs : List (CRTBasis × ℕ)}
    (hmult : mult.ExactOn 11 (xs.length * (2 ^ 11 * 2 ^ 11))) (hlen : xs.length = ys.length)
    (hk : xs.length ≤ 2 ^ 20) (hx : ∀ a ∈ xs, FormatEntry 24 (-126) 127 a)
    (hy : ∀ a ∈ ys, FormatEntry 24 (-126) 127 a)
    (hcfgs : ∀ c ∈ cfgs, c.1 = fp32Basis6 ∧ c.2 ≤ 34) :
    ozaki2CRJC ⟨161, 17⟩ mult 24 (-126) 127 cfgs 11 24 xs ys =
      some (ozaki2CRJ mult 24 (-126) 127 cfgs 11 24 xs ys) := by
  have hE : ((-126 : ℤ) - ((24 : ℕ) - 1 : ℤ)).natAbs ≤ 149 ∧
      ((127 : ℤ) - ((24 : ℕ) - 1 : ℤ)).natAbs ≤ 149 := by decide
  have hbud := bitlen_dotAbsBound_le hk
  have hbk := bitlen_length_le hk
  have hW : exactW 24 24 = 38 := by decide
  have hb2 : bitlen (24 * 24 + 2) = 10 := by decide
  obtain ⟨hm, hM, hsize, hM2, hbl⟩ := fp32Basis6_facts
  refine ozaki2CRJC_eq hmult hlen (Nat.le_refl _) (entriesIn_of_format hE hx)
    (entriesIn_of_format hE hy) ?_ ?_ (by decide) ?_
  · intro c hc
    obtain ⟨h1, h2⟩ := hcfgs c hc
    rw [h1]
    refine ⟨hm, hM, Nat.lt_of_lt_of_le hsize (Nat.pow_le_pow_right (by decide) (by decide)),
      Nat.lt_of_lt_of_le hM2 (Nat.pow_le_pow_right (by decide) (by decide)), ?_, ?_⟩
    · unfold ozaki2R; rw [hbl]; simp only; omega
    · unfold ozaki2X ozaki2R; rw [hbl]; simp only
      have : (-126 : ℤ).natAbs = 126 := by decide
      have : (127 : ℤ).natAbs = 127 := by decide
      omega
  · unfold exactR; rw [hW, hb2]; simp only; omega
  · unfold exactX; rw [hW]; simp only
    have : (-126 : ℤ).natAbs = 126 := by decide
    have : (127 : ℤ).natAbs = 127 := by decide
    omega

/-- **Binary32 Ozaki-II, every integer within 161 bits, correctly rounded.** -/
theorem ozaki2CRJC_binary32_eq {mult : MatrixMultiplier} {xs ys : List (ℤ × ℤ)} {cfgs : List (CRTBasis × ℕ)}
    (hmult : mult.ExactOn 11 (xs.length * (2 ^ 11 * 2 ^ 11))) (hlen : xs.length = ys.length)
    (hk : xs.length ≤ 2 ^ 20) (hx : ∀ a ∈ xs, FormatEntry 24 (-126) 127 a)
    (hy : ∀ a ∈ ys, FormatEntry 24 (-126) 127 a)
    (hcfgs : ∀ c ∈ cfgs, c.1 = fp32Basis6 ∧ c.2 ≤ 34)
    (hrange : ∀ c ∈ cfgs, 2 * xs.length * (2 ^ c.2 * 2 ^ c.2) < c.1.modulus) :
    ozaki2CRJC ⟨161, 17⟩ mult 24 (-126) 127 cfgs 11 24 xs ys =
      some (rne32Q (dot (entryVals xs) (entryVals ys))) := by
  rw [ozaki2CRJC_binary32 hmult hlen hk hx hy hcfgs,
    ozaki2CRJ32_eq hmult (by decide) (by decide) (fun c hc => by
      obtain ⟨h1, _⟩ := hcfgs c hc
      refine ⟨?_, ?_, hrange c hc⟩
      · rw [h1]; decide +kernel
      · rw [h1]; exact fun m hm => (fp32Basis6_facts.1 m hm).2) hlen (Nat.le_refl _)
    (fun v hv => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv; exact (hx a ha).formatValue)
    (fun v hv => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv; exact (hy a ha).formatValue)]

end Ozaki
