import OzakiTC.ADPChecked
import OzakiTC.IEEEBounded

/-! # The integer Ozaki-II and ADP pipelines: jumping top-down summation, signed zeros, widths, specials

Small kernel-checked cases (`decide +kernel`) on four binary64 entries given as integer pairs,
on V100 fp16 blocks (Ozaki-II) and the split-K INT8 matrix multiplier (ADP):

* `tcOzaki2CRJ` with the twelve moduli at most `4096` (`P = 69`) and with no configuration, so
  that the entry goes through the jumping exact fallback, against the binary64 round to nearest of
  the exact product; the same for `adpCRJ` with the configuration `(8, 56)` and with none;
* signed zeros: products that are all `−0` give `−0`, products that cancel give `+0`
  (`tcOzaki2CRJS`, `adpCRJS`);
* every integer bounded: the checked `ozaki2CRJC` and `adpCRJC` return the unchecked results at the
  proven widths (`264` and `24`, `264` and `25` bits), and `none` when the data or the exponent
  registers are too narrow;
* IEEE special values on stored data (`tcOzaki2CRJI`, `adpCRJI`): a NaN input, `Inf · 0`, an
  overflow to `+Inf`, and `−0`, each against the specification `dotIEEE`. -/

open TensorCore Ozaki Ozaki.TC Ozaki.Checked

namespace OzakiTCTests.FinalPipelines

def xs : List (ℤ × ℤ) :=
  [(4503599627370497, -52), (-6004799503160661, -54), (7000000000000003, -55),
    (5000000000000001, -53)]
def ys : List (ℤ × ℤ) :=
  [(4503599627370499, -52), (6004799503160663, -53), (-3, -2), (8000000000000001, -56)]

def cfgs2 : List (CRTBasis × ℕ) := [(fp64Basis, 69)]

/-- Ozaki-II in integers: the rounding test succeeds on the configuration, and the jumping exact
fallback alone. -/
example : tcOzaki2CRJ v100F16F32 cfgs2 11 175 xs ys = rne64 (dot (entryVals xs) (entryVals ys)) ∧
    tcOzaki2CRJ v100F16F32 [] 11 175 xs ys = rne64 (dot (entryVals xs) (entryVals ys)) := by
  decide +kernel

/-- ADP in integers: the configuration `(8, 56)`, and the jumping exact fallback on the INT8 matrix
multiplier. -/
example : adpCRJ [(8, 56)] 300 xs ys = rne64 (dot (entryVals xs) (entryVals ys)) ∧
    adpCRJ [] 300 xs ys = rne64 (dot (entryVals xs) (entryVals ys)) := by
  decide +kernel

/-! ## Signed zeros -/

def negZ : List SEntry × List SEntry := ([((0, 0), true), ((0, 0), false)], [((1, 0), false), ((0, 0), true)])
def cancel : List SEntry × List SEntry := ([((1, 0), false), ((-1, 0), true)], [((1, 0), false), ((1, 0), false)])

example : tcOzaki2CRJS v100F16F32 cfgs2 11 175 negZ.1 negZ.2 = some ⟨0, true⟩ ∧
    tcOzaki2CRJS v100F16F32 cfgs2 11 175 cancel.1 cancel.2 = some ⟨0, false⟩ ∧
    adpCRJS [(8, 56)] 300 negZ.1 negZ.2 = some ⟨0, true⟩ ∧
    adpCRJS [(8, 56)] 300 cancel.1 cancel.2 = some ⟨0, false⟩ := by
  decide +kernel

/-! ## Every integer bounded -/

example : ozaki2CRJC ⟨264, 24⟩ (tcSplitK v100F16F32 11) 53 (-1022) 1023 cfgs2 11 175 xs ys =
    some (ozaki2CRJ (tcSplitK v100F16F32 11) 53 (-1022) 1023 cfgs2 11 175 xs ys) := by
  decide +kernel

/-- Too narrow: a `64`-bit data register, or an `8`-bit exponent register, fails a guard. -/
example : ozaki2CRJC ⟨64, 24⟩ (tcSplitK v100F16F32 11) 53 (-1022) 1023 cfgs2 11 175 xs ys = none ∧
    ozaki2CRJC ⟨264, 8⟩ (tcSplitK v100F16F32 11) 53 (-1022) 1023 cfgs2 11 175 xs ys = none := by
  decide +kernel

example : adpCRJC ⟨264, 25⟩ [(8, 56)] 300 xs ys = some (adpCRJ [(8, 56)] 300 xs ys) ∧
    adpCRJC ⟨264, 25⟩ [] 300 xs ys = some (adpCRJ [] 300 xs ys) := by
  decide +kernel

example : adpCRJC ⟨64, 25⟩ [(8, 56)] 300 xs ys = none ∧
    adpCRJC ⟨264, 8⟩ [(8, 56)] 300 xs ys = none := by
  decide +kernel

/-! ## IEEE special values on stored data -/

def fin (m e : ℤ) : IDatum := .fin ((m, e), decide (m < 0))
def spec (a c : List IDatum) : FVal := dotIEEE 53 (-1022) 1023 (a.map IDatum.toFVal) (c.map IDatum.toFVal)
def ii2 (a c : List IDatum) : FVal := tcOzaki2CRJI v100F16F32 cfgs2 11 175 a c
def iad (a c : List IDatum) : FVal := adpCRJI [(8, 56)] 300 a c

/-- A NaN input, `Inf · 0`, overflow to `+Inf` (`2^1023 · 4`), and products that are all `−0`. -/
example : ii2 [fin 1 0, .nan] [fin 2 0, fin 3 0] = .nan ∧ spec [fin 1 0, .nan] [fin 2 0, fin 3 0] = .nan ∧
    ii2 [.inf false, fin 1 0] [.fin ((0, 0), true), fin 2 0] = .nan ∧
    ii2 [fin 1 1023] [fin 4 0] = .inf false ∧ spec [fin 1 1023] [fin 4 0] = .inf false ∧
    ii2 [.fin ((0, 0), true)] [fin 1 0] = .fin ⟨0, true⟩ := by
  decide +kernel

example : iad [fin 1 0, .nan] [fin 2 0, fin 3 0] = .nan ∧
    iad [fin 1 1023] [fin 4 0] = .inf false ∧
    iad [.fin ((0, 0), true)] [fin 1 0] = .fin ⟨0, true⟩ ∧
    iad (xs.map fun a => fin a.1 a.2) (ys.map fun a => fin a.1 a.2) =
      spec (xs.map fun a => fin a.1 a.2) (ys.map fun a => fin a.1 a.2) := by
  decide +kernel

end OzakiTCTests.FinalPipelines
