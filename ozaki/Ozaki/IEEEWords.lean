import Ozaki.IEEEInt

/-! # IEEE special values by integer operations on the stored words

`crIEEEI` decides the IEEE specification's special cases with `dotSpecial` on the data read as
IEEE values (`IDatum.toFVal`). Here every step of that decision is integer arithmetic on the
words a binary format stores:

* `wordFields` splits a word into its sign bit, exponent field and significand field by integer
  division and remainder; `wordClass` classifies it (zero, subnormal, normal, infinity, NaN) from
  the fields; `decodeWord` turns it into a stored datum (`IDatum`) with integer operations only.
  Every finite word decodes to a value of its format (`decodeWord_inFormat`).
* `dotSpecialI` decides the special cases from the stored data by tag tests, sign-bit
  exclusive ors and zero tests of integer significands, and agrees with `dotSpecial` on the data
  read as IEEE values (`dotSpecialI_eq`). So `crIEEEIW`, which uses it, is `crIEEEI`
  (`crIEEEIW_eq`), and `crIEEEWord` runs a scheme with special values on stored words with every
  step in integer arithmetic, meeting the IEEE specification (`crIEEEWord_eq`).

`OzakiTC.IEEEWords` proves that `decodeWord` agrees with TensorCore's decoding of binary64 and
binary32 words. -/

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

namespace Ozaki

/-- The layout of a binary interchange format: stored significand bits, exponent bits and bias. -/
structure WordFormat where
  mb : ℕ
  eb : ℕ
  bias : ℤ
  deriving DecidableEq, Repr

def WordFormat.binary64 : WordFormat := ⟨52, 11, 1023⟩
def WordFormat.binary32 : WordFormat := ⟨23, 8, 127⟩

/-- The sign bit, exponent field and significand field of a word, by integer division and
remainder. -/
def wordFields (F : WordFormat) (w : ℕ) : Bool × ℕ × ℕ :=
  (w / 2 ^ (F.mb + F.eb) % 2 == 1, w / 2 ^ F.mb % 2 ^ F.eb, w % 2 ^ F.mb)

/-- The class of a stored word. -/
inductive WordClass where
  | zero
  | subnormal
  | normal
  | inf
  | nan
  deriving DecidableEq, Repr

/-- **The class of a word**, from its fields: an all-ones exponent field is an infinity (zero
significand field) or NaN; a zero exponent field is a zero or a subnormal; anything else is
normal. -/
def wordClass (F : WordFormat) (w : ℕ) : WordClass :=
  let E := (wordFields F w).2.1
  let M := (wordFields F w).2.2
  if E = 2 ^ F.eb - 1 then (if M = 0 then .inf else .nan)
  else if E = 0 then (if M = 0 then .zero else .subnormal) else .normal

/-- The significand with its sign. -/
def signedSig (s : Bool) (m : ℕ) : ℤ := if s then -(m : ℤ) else m

/-- **A stored word as a stored IEEE datum**, by integer operations on its fields: `±Inf`, NaN,
or the entry `(±M, 1 − bias − mb)` (zero or subnormal) or `(±(2^mb + M), E − bias − mb)`
(normal), with the word's sign bit. -/
def decodeWord (F : WordFormat) (w : ℕ) : IDatum :=
  let s := (wordFields F w).1
  let E := (wordFields F w).2.1
  let M := (wordFields F w).2.2
  if E = 2 ^ F.eb - 1 then (if M = 0 then .inf s else .nan)
  else if E = 0 then .fin ((signedSig s M, 1 - F.bias - F.mb), s)
  else .fin ((signedSig s (2 ^ F.mb + M), (E : ℤ) - F.bias - F.mb), s)

theorem natAbs_signedSig (s : Bool) (m : ℕ) : (signedSig s m).natAbs = m := by
  unfold signedSig; cases s <;> simp

theorem entryVal_eq_mul (m e : ℤ) : entryVal (m, e) = (m : ℚ) * 2 ^ e := rfl

/-- **Every finite word decodes to a value of its format**: precision `mb + 1`, exponents from
`1 − bias` to `2^eb − 2 − bias`. -/
theorem decodeWord_inFormat (F : WordFormat) (hb : 1 < F.eb) (w : ℕ) :
    (decodeWord F w).InFormat (F.mb + 1) (1 - F.bias) (((2 ^ F.eb - 2 : ℕ) : ℤ) - F.bias) := by
  have hE : w / 2 ^ F.mb % 2 ^ F.eb < 2 ^ F.eb := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hM : w % 2 ^ F.mb < 2 ^ F.mb := Nat.mod_lt _ (Nat.two_pow_pos _)
  have h1 : 1 ≤ 2 ^ F.eb := Nat.one_le_two_pow
  have h2 : 4 ≤ 2 ^ F.eb := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) hb; simpa using this
  unfold decodeWord wordFields
  simp only
  generalize (w / 2 ^ (F.mb + F.eb) % 2 == 1) = sg
  generalize w / 2 ^ F.mb % 2 ^ F.eb = E at hE
  generalize w % 2 ^ F.mb = M at hM
  split
  · split <;> trivial
  · rename_i hne
    split
    · rename_i h0
      show FormatValue _ _ _ _
      refine ⟨signedSig sg M, 1 - F.bias, Int.le_refl _, ?_, ?_, ?_⟩
      · have : (2 : ℤ) ≤ ((2 ^ F.eb - 2 + 2 : ℕ) : ℤ) := by push_cast; omega
        have h3 : ((2 ^ F.eb - 2 : ℕ) : ℤ) = ((2 ^ F.eb : ℕ) : ℤ) - 2 := by omega
        omega
      · rw [natAbs_signedSig]
        exact Nat.lt_of_lt_of_le hM (Nat.pow_le_pow_right (by decide) (by omega))
      · rw [entryVal_eq_mul]; congr 2; push_cast; omega
    · rename_i h0
      show FormatValue _ _ _ _
      refine ⟨signedSig sg (2 ^ F.mb + M), (E : ℤ) - F.bias, by omega, ?_, ?_, ?_⟩
      · have : E ≤ 2 ^ F.eb - 2 := by omega
        omega
      · rw [natAbs_signedSig, Nat.pow_succ]; omega
      · rw [entryVal_eq_mul]; congr 2; push_cast; omega

/-! ## The special cases from stored data -/

/-- The class of a product: finite, an infinity with its sign, or NaN. -/
inductive PClass where
  | fin
  | inf (neg : Bool)
  | nan
  deriving DecidableEq, Repr

/-- The class of an IEEE value. -/
def FVal.cls : FVal → PClass
  | .fin _ => .fin
  | .inf n => .inf n
  | .nan => .nan

/-- **The class of a product of stored data**, by tag tests, the exclusive or of sign bits and a
zero test of an integer significand. -/
def mulClassI : IDatum → IDatum → PClass
  | .nan, _ => .nan
  | _, .nan => .nan
  | .inf a, .inf b => .inf (xor a b)
  | .inf a, .fin t => if t.1.1 = 0 then .nan else .inf (xor a t.2)
  | .fin s, .inf b => if s.1.1 = 0 then .nan else .inf (xor s.2 b)
  | .fin _, .fin _ => .fin

theorem mulClassI_eq (a c : IDatum) : mulClassI a c = (mulX a.toFVal c.toFVal).cls := by
  cases a <;> cases c <;>
    simp [mulClassI, mulX, IDatum.toFVal, FVal.cls, toSigned, entryVal_eq_zero_iff] <;>
    split <;> simp_all

/-- **The specification's special cases, decided on stored data.** -/
def dotSpecialI (xs ys : List IDatum) : Option FVal :=
  let ps := List.zipWith mulClassI xs ys
  if ps.contains .nan then some .nan
  else if ps.contains (.inf false) && ps.contains (.inf true) then some .nan
  else if ps.contains (.inf false) then some (.inf false)
  else if ps.contains (.inf true) then some (.inf true)
  else none

theorem contains_cls_nan : ∀ l : List FVal, (l.map FVal.cls).contains .nan = l.contains .nan
  | [] => rfl
  | v :: l => by
    have ih := contains_cls_nan l
    cases v <;> simp_all [FVal.cls]

theorem contains_cls_inf (n : Bool) :
    ∀ l : List FVal, (l.map FVal.cls).contains (.inf n) = l.contains (.inf n)
  | [] => rfl
  | v :: l => by
    have ih := contains_cls_inf n l
    cases v <;> simp_all [FVal.cls]

theorem zipWith_mulClassI : ∀ xs ys : List IDatum,
    List.zipWith mulClassI xs ys =
      (List.zipWith mulX (xs.map IDatum.toFVal) (ys.map IDatum.toFVal)).map FVal.cls
  | [], _ => rfl
  | _ :: _, [] => rfl
  | a :: xs, c :: ys => by
    simp only [List.zipWith_cons_cons, List.map_cons]
    rw [mulClassI_eq, zipWith_mulClassI xs ys]

/-- **Integer special-case detection agrees with the specification's.** -/
theorem dotSpecialI_eq (xs ys : List IDatum) :
    dotSpecialI xs ys = dotSpecial (xs.map IDatum.toFVal) (ys.map IDatum.toFVal) := by
  unfold dotSpecialI dotSpecial
  simp only
  rw [zipWith_mulClassI, contains_cls_nan, contains_cls_inf, contains_cls_inf]

/-- `crIEEEI` with the special cases decided on stored data (`dotSpecialI`). -/
def crIEEEIW (scheme : List (ℤ × ℤ) → List (ℤ × ℤ) → Option ℚ)
    (sgn : List (ℤ × ℤ) → List (ℤ × ℤ) → ℤ) (xs ys : List IDatum) : FVal :=
  match dotSpecialI xs ys with
  | some v => v
  | none =>
    match finPartsI xs, finPartsI ys with
    | some sx, some sy =>
      crFinite (scheme (sx.map (·.1)) (sy.map (·.1))) (sgn (sx.map (·.1)) (sy.map (·.1)))
        (allNegZeroI sx sy)
    | _, _ => .nan

theorem crIEEEIW_eq (scheme : List (ℤ × ℤ) → List (ℤ × ℤ) → Option ℚ)
    (sgn : List (ℤ × ℤ) → List (ℤ × ℤ) → ℤ) (xs ys : List IDatum) :
    crIEEEIW scheme sgn xs ys = crIEEEI scheme sgn xs ys := by
  unfold crIEEEIW crIEEEI
  rw [dotSpecialI_eq]
  rfl

/-- **A scheme with special values on stored words**, every step in integer arithmetic: decode the
words, decide the special cases on the stored data, otherwise run the integer scheme. -/
def crIEEEWord (F : WordFormat) (scheme : List (ℤ × ℤ) → List (ℤ × ℤ) → Option ℚ)
    (sgn : List (ℤ × ℤ) → List (ℤ × ℤ) → ℤ) (ws vs : List ℕ) : FVal :=
  crIEEEIW scheme sgn (ws.map (decodeWord F)) (vs.map (decodeWord F))

/-- **On stored words, an integer correctly rounded scheme with special values meets the IEEE
specification**, with the integer exact fallback as the sign oracle: the format is `mb + 1` bits of
precision with exponents from `1 − bias` to `2^eb − 2 − bias`, and the scheme is correctly rounded
on its values. -/
theorem crIEEEWord_eq (F : WordFormat) (hb : 1 < F.eb) {emin emax : ℤ}
    (hemin : emin = 1 - F.bias) (hemax : emax = ((2 ^ F.eb - 2 : ℕ) : ℤ) - F.bias)
    (hle : emin ≤ emax) {scheme : List (ℤ × ℤ) → List (ℤ × ℤ) → Option ℚ} {mult : MatrixMultiplier}
    {b smax : ℕ} (hmult : ∀ B, mult.ExactOn b B) {ws vs : List ℕ}
    (hvanish : ∀ x y : List (ℤ × ℤ), (∀ a ∈ x, FormatValue (F.mb + 1) emin emax (entryVal a)) →
      (∀ a ∈ y, FormatValue (F.mb + 1) emin emax (entryVal a)) →
      ∃ s ∈ List.range' 1 smax, vanishInt b s x y = true)
    (hscheme : ∀ x y : List (ℤ × ℤ),
      (∀ a ∈ x, FormatValue (F.mb + 1) emin emax (entryVal a)) →
      (∀ a ∈ y, FormatValue (F.mb + 1) emin emax (entryVal a)) → x.length = ws.length →
      y.length = ws.length →
      scheme x y = roundRNE (F.mb + 1) emin emax (dot (entryVals x) (entryVals y)))
    (hlen : ws.length = vs.length) :
    crIEEEWord F scheme (fun x y => (exactSignI mult b smax x y).getD 0) ws vs =
      dotIEEE (F.mb + 1) emin emax ((ws.map (decodeWord F)).map IDatum.toFVal)
        ((vs.map (decodeWord F)).map IDatum.toFVal) := by
  unfold crIEEEWord
  rw [crIEEEIW_eq]
  subst hemin hemax
  exact crIEEEI_exactSign (by omega) hle hmult hvanish
    (fun x y hx hy h1 h2 => hscheme x y hx hy (by simpa using h1) (by simpa using h2))
    (fun a ha => by
      obtain ⟨w, _, rfl⟩ := List.mem_map.mp ha
      exact decodeWord_inFormat F hb w)
    (fun a ha => by
      obtain ⟨w, _, rfl⟩ := List.mem_map.mp ha
      exact decodeWord_inFormat F hb w)
    (by simpa using hlen)

/-! ## Examples, checked by the kernel -/

/-- `+Inf`, NaN, `−0`, the smallest subnormal and `1` as binary64 words. -/
example : decodeWord .binary64 0x7FF0000000000000 = .inf false ∧
    decodeWord .binary64 0xFFF8000000000000 = .nan ∧
    decodeWord .binary64 0x8000000000000000 = .fin ((0, -1074), true) ∧
    decodeWord .binary64 1 = .fin ((1, -1074), false) ∧
    decodeWord .binary64 0x3FF0000000000000 = .fin ((4503599627370496, -52), false) := by
  decide +kernel

example : wordClass .binary32 0x7F800000 = .inf ∧ wordClass .binary32 0x7FC00000 = .nan ∧
    wordClass .binary32 0x00000001 = .subnormal ∧ wordClass .binary32 0x80000000 = .zero ∧
    wordClass .binary32 0x3F800000 = .normal := by
  decide +kernel

/-- `Inf · 0` is NaN, decided on stored data. -/
example : dotSpecialI [.inf false, .fin ((3, 0), false)] [.fin ((0, -1074), true), .fin ((1, 0), false)] =
    some .nan := by decide +kernel

end Ozaki
