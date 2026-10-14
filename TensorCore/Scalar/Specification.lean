import TensorCore.Scalar.Operations

/-! Total scalar contracts. -/

namespace TensorCore.IEEE

def InfinitySpec (f : BinaryFormat) (s : Bool) (r : Result f) : Prop :=
  decode f r.bits = .infinity s ∧ r.flags = {}

def InvalidSpec (f : BinaryFormat) (r : Result f) : Prop :=
  (∃ s p, decode f r.bits = .nan s false p) ∧ r.flags = { invalid := true }

def NaNSpec (f : BinaryFormat) (xs : List Datum) (extraInvalid : Bool) (r : Result f) : Prop :=
  let n := (chooseNaN xs).getD ⟨false, false, 0⟩
  decode f r.bits = .nan n.negative false (n.payload % quietBit f) ∧
  r.flags = { invalid := extraInvalid || xs.any Datum.isSignaling }

theorem infinityResult_correct (f : BinaryFormat) (s : Bool) :
    InfinitySpec f s (infinityResult f s) := ⟨decode_infinity f s, rfl⟩

theorem nanResult_correct (f : BinaryFormat) (xs : List Datum) (extraInvalid : Bool) :
    NaNSpec f xs extraInvalid (nanResult f xs extraInvalid) := ⟨decode_nan _ _ _, rfl⟩

theorem invalidResult_correct (f : BinaryFormat) : InvalidSpec f (invalidResult f) :=
  ⟨⟨false, 0, by simpa [invalidResult, nanResult, chooseNaN] using decode_nan f false 0⟩, rfl⟩

/-- Complete addition case table, including nonfinite inputs. -/
def AddSpec (f : BinaryFormat) (cfg : Context) (a b : Datum) (r : Result f) : Prop :=
  if a.isNaN || b.isNaN then NaNSpec f [a, b] false r else
  match a, b with
  | .finite sa x, .finite sb y => RoundSpec f cfg (sumZeroSign cfg.mode sa sb) (x + y) r
  | .infinity sa, .infinity sb =>
      if sa = sb then InfinitySpec f sa r else InvalidSpec f r
  | .infinity s, _ | _, .infinity s => InfinitySpec f s r
  | _, _ => False

def MulSpec (f : BinaryFormat) (cfg : Context) (a b : Datum) (r : Result f) : Prop :=
  if a.isNaN || b.isNaN then NaNSpec f [a, b] false r else
  match a, b with
  | .finite sa x, .finite sb y => RoundSpec f cfg (xor sa sb) (x * y) r
  | .infinity sa, .infinity sb => InfinitySpec f (xor sa sb) r
  | .infinity sa, .finite sb y =>
      if y = 0 then InvalidSpec f r else InfinitySpec f (xor sa sb) r
  | .finite sa x, .infinity sb =>
      if x = 0 then InvalidSpec f r else InfinitySpec f (xor sa sb) r
  | _, _ => False

def FmaSpec (f : BinaryFormat) (cfg : Context) (a b c : Datum) (r : Result f) : Prop :=
  if a.isNaN || b.isNaN || c.isNaN then NaNSpec f [a, b, c] (invalidProduct a b) r else
  match a, b, c with
  | .finite sa x, .finite sb y, .finite sc z =>
      RoundSpec f cfg (sumZeroSign cfg.mode (xor sa sb) sc) (x * y + z) r
  | .finite _ _, .finite _ _, .infinity sc => InfinitySpec f sc r
  | .infinity sa, .finite sb y, c =>
      if y = 0 then InvalidSpec f r else
      if c.isInfinite && xor sa sb != c.negative then InvalidSpec f r
      else InfinitySpec f (xor sa sb) r
  | .finite sa x, .infinity sb, c =>
      if x = 0 then InvalidSpec f r else
      if c.isInfinite && xor sa sb != c.negative then InvalidSpec f r
      else InfinitySpec f (xor sa sb) r
  | .infinity sa, .infinity sb, c =>
      if c.isInfinite && xor sa sb != c.negative then InvalidSpec f r
      else InfinitySpec f (xor sa sb) r
  | _, _, _ => False

def ConvertSpec (source target : BinaryFormat) (cfg : Context) (a : Datum) (r : Result target) : Prop :=
  match a with
  | .finite s x => RoundSpec target cfg s x r
  | .infinity s => InfinitySpec target s r
  | .nan s sig p =>
      decode target r.bits = .nan s false (convertPayload source target p % quietBit target) ∧
      r.flags = { invalid := sig }

theorem addDatum_correct (f : BinaryFormat) (cfg : Context) (a b : Datum) :
    AddSpec f cfg a b (addDatum f cfg a b) := by
  cases a <;> cases b <;>
    simp only [AddSpec, addDatum, Datum.isNaN, Bool.or_self, Bool.or_false,
      Bool.or_true, Bool.false_eq_true, ↓reduceIte, beq_iff_eq,
      round_correct, infinityResult_correct, nanResult_correct]
  split <;> first | exact infinityResult_correct _ _ | exact invalidResult_correct _

theorem mulDatum_correct (f : BinaryFormat) (cfg : Context) (a b : Datum) :
    MulSpec f cfg a b (mulDatum f cfg a b) := by
  cases a <;> cases b <;>
    simp only [MulSpec, mulDatum, Datum.isNaN, Bool.or_self, Bool.or_false,
      Bool.or_true, Bool.false_eq_true, ↓reduceIte,
      round_correct, infinityResult_correct, nanResult_correct]
  all_goals split <;> first | exact infinityResult_correct _ _ | exact invalidResult_correct _

theorem fmaDatum_correct (f : BinaryFormat) (cfg : Context) (a b c : Datum) :
    FmaSpec f cfg a b c (fmaDatum f cfg a b c) := by
  cases a <;> cases b <;> cases c <;>
    simp only [FmaSpec, fmaDatum, invalidProduct, Datum.isNaN, Datum.isInfinite, Datum.isZero,
      Datum.negative, Bool.or_self, Bool.false_or, Bool.or_false, Bool.or_true,
      Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true,
      ↓reduceIte, decide_eq_true_eq, round_correct, infinityResult_correct, nanResult_correct]
  all_goals split <;> (try simp only [infinityResult_correct, invalidResult_correct])
  all_goals split <;> first | exact infinityResult_correct _ _ | exact invalidResult_correct _

theorem convertDatum_correct (source target : BinaryFormat) (cfg : Context) (a : Datum) :
    ConvertSpec source target cfg a (convertDatum source target cfg a) := by
  cases a with
  | finite s x => exact round_correct _ _ _ _
  | infinity s => exact infinityResult_correct _ _
  | nan s sig p => exact ⟨decode_nan _ _ _, rfl⟩

/-- Every pair of encoded inputs satisfies the complete addition contract. -/
theorem add_correct (f : BinaryFormat) (cfg : Context) (a b : Word f) :
    AddSpec f cfg (decode f a) (decode f b) (add f cfg a b) := addDatum_correct _ _ _ _

theorem sub_correct (f : BinaryFormat) (cfg : Context) (a b : Word f) :
    AddSpec f cfg (decode f a) (decode f b).negate (sub f cfg a b) := addDatum_correct _ _ _ _

theorem mul_correct (f : BinaryFormat) (cfg : Context) (a b : Word f) :
    MulSpec f cfg (decode f a) (decode f b) (mul f cfg a b) := mulDatum_correct _ _ _ _

/-- Exactly one rounding of the original decoded product plus addend. -/
theorem fma_correct (f : BinaryFormat) (cfg : Context) (a b c : Word f) :
    FmaSpec f cfg (decode f a) (decode f b) (decode f c) (fma f cfg a b c) :=
  fmaDatum_correct _ _ _ _ _

theorem convert_correct (source target : BinaryFormat) (cfg : Context) (a : Word source) :
    ConvertSpec source target cfg (decode source a) (convert source target cfg a) :=
  convertDatum_correct _ _ _ _

end TensorCore.IEEE
