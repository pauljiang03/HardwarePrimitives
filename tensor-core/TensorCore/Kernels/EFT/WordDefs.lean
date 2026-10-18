import TensorCore.Kernels.EFT.BitScanDefs

/-! Fixed-width dyadics for the complete finite-input TC-EFT. -/

namespace TensorCore.EFMachine

abbrev Magnitude := BitVec 576
abbrev Grid := BitVec 10

structure Word where
  negative : Bool
  magnitude : Magnitude
  deriving Repr, DecidableEq

def Word.zero : Word := ⟨false, 0⟩

/-- Mathematical interpretation; never used to execute the bounded procedure. -/
def Word.coefficient (x : Word) : ℤ :=
  if x.negative then -(x.magnitude.toNat : ℤ) else x.magnitude.toNat

def Word.value (x : Word) : ℚ := (x.coefficient : ℚ) * pow2 (-272)

def Word.neg (x : Word) : Word := ⟨!x.negative, x.magnitude⟩

/-- Exact signed addition, rejecting unsigned magnitude overflow. -/
def Word.add (x y : Word) : Option Word :=
  if x.negative == y.negative then
    let m := x.magnitude + y.magnitude
    if m < x.magnitude then none else some ⟨x.negative, m⟩
  else if y.magnitude ≤ x.magnitude then
    some ⟨x.negative, x.magnitude - y.magnitude⟩
  else some ⟨y.negative, y.magnitude - x.magnitude⟩

def Word.sub (x y : Word) : Option Word := x.add y.neg

/-- The order is explicit; each accepted suffix is represented by a fixed word. -/
def sumWords : List Word → Option Word
  | [] => some Word.zero
  | x :: xs => do x.add (← sumWords xs)

structure WordSplit where
  coarse : Word
  low : Word
  deriving Repr, DecidableEq

/-- Quotient/remainder extraction at 2^(grid-272). -/
def Word.split (x : Word) (grid : Grid) : WordSplit :=
  if grid ≥ 576 then ⟨⟨x.negative, 0⟩, x⟩
  else
    let m := (x.magnitude >>> grid) <<< grid
    ⟨⟨x.negative, m⟩, ⟨x.negative, x.magnitude - m⟩⟩

/-- Largest finite FP32 magnitude in units of the common dyadic grid. -/
def maxMagnitude32 : Magnitude := (16777215 : Magnitude) <<< 376

/-- The output quantum in common-grid units, including subnormal and zero words. -/
def outputGrid (b : F32) : Grid :=
  let e := ((b >>> 23).setWidth 8).zeroExtend 10
  if e == 0 then 123 else e + 122

/-- Positive rounding to FP32 grid, using at most ten leading-support probes. -/
def roundingGrid (m : Magnitude) : Magnitude :=
  let length := (576 : Magnitude) - leadingZeros m
  if length ≤ 147 then 123 else length - 24

def roundingCoefficient (m g : Magnitude) : Magnitude :=
  let k := m >>> g
  let r := m - (k <<< g)
  let half := (1 : Magnitude) <<< (g - 1)
  if r > half || (r == half && (k &&& 1) == 1) then k + 1 else k

def encodeAtGrid (negative : Bool) (g k : Magnitude) : F32 :=
  let payload := if k < 8388608 then k else ((g - 122) <<< 23) + (k - 8388608)
  (if negative then (0x80000000 : F32) else 0) + payload.setWidth 32

def encodeRounded (negative : Bool) (g k : Magnitude) : F32 :=
  let (g, k) := if k == 16777216 then (g + 1, k >>> 1) else (g, k)
  encodeAtGrid negative g k

/-- Direct integer nearest-even conversion to FP32. -/
def Word.round32 (x : Word) : Option F32 :=
  if x.magnitude > maxMagnitude32 then none
  else if x.magnitude == 0 then some 0
  else
    let g := roundingGrid x.magnitude
    some (encodeRounded x.negative g (roundingCoefficient x.magnitude g))

end TensorCore.EFMachine
