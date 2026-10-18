import OzakiMC.Ozaki2Checked
import OzakiMC.IEEEBounded

/-! # Integer Ozaki-II on the Matrix Core model: jumping top-down summation, signed zeros, widths, specials

The cases of `tests/OzakiTCTests/FinalPipelines.lean` for Ozaki-II on CDNA 3 fp16 blocks with
split-K, checked by kernel evaluation: the configuration and the jumping exact fallback alone
against the binary64 round to nearest, signed zeros, the checked function at the proven widths and
with too narrow registers, and IEEE special values on stored data. -/

open MatrixCore Ozaki Ozaki.MC Ozaki.Checked

namespace OzakiMCTests.FinalPipelines

def xs : List (ℤ × ℤ) :=
  [(4503599627370497, -52), (-6004799503160661, -54), (7000000000000003, -55),
    (5000000000000001, -53)]
def ys : List (ℤ × ℤ) :=
  [(4503599627370499, -52), (6004799503160663, -53), (-3, -2), (8000000000000001, -56)]

def cfgs2 : List (CRTBasis × ℕ) := [(fp64Basis, 69)]

example : mcOzaki2CRJ cdna3F16 cfgs2 11 175 xs ys = rne64 (dot (entryVals xs) (entryVals ys)) ∧
    mcOzaki2CRJ cdna3F16 [] 11 175 xs ys = rne64 (dot (entryVals xs) (entryVals ys)) := by
  decide +kernel

def negZ : List SEntry × List SEntry := ([((0, 0), true), ((0, 0), false)], [((1, 0), false), ((0, 0), true)])
def cancel : List SEntry × List SEntry := ([((1, 0), false), ((-1, 0), true)], [((1, 0), false), ((1, 0), false)])

example : mcOzaki2CRJS cdna3F16 cfgs2 11 175 negZ.1 negZ.2 = some ⟨0, true⟩ ∧
    mcOzaki2CRJS cdna3F16 cfgs2 11 175 cancel.1 cancel.2 = some ⟨0, false⟩ := by
  decide +kernel

example : ozaki2CRJC ⟨264, 24⟩ (mcSplitK cdna3F16 11) 53 (-1022) 1023 cfgs2 11 175 xs ys =
      some (ozaki2CRJ (mcSplitK cdna3F16 11) 53 (-1022) 1023 cfgs2 11 175 xs ys) ∧
    ozaki2CRJC ⟨64, 24⟩ (mcSplitK cdna3F16 11) 53 (-1022) 1023 cfgs2 11 175 xs ys = none := by
  decide +kernel

def fin (m e : ℤ) : IDatum := .fin ((m, e), decide (m < 0))
def ii2 (a c : List IDatum) : FVal := mcOzaki2CRJI cdna3F16 cfgs2 11 175 a c

example : ii2 [fin 1 0, .nan] [fin 2 0, fin 3 0] = .nan ∧
    ii2 [.inf false, fin 1 0] [.fin ((0, 0), true), fin 2 0] = .nan ∧
    ii2 [fin 1 1023] [fin 4 0] = .inf false ∧
    ii2 [.fin ((0, 0), true)] [fin 1 0] = .fin ⟨0, true⟩ := by
  decide +kernel

end OzakiMCTests.FinalPipelines
