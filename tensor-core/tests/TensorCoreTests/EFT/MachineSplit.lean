import TensorCore.Kernels.EFT.Split

namespace TensorCore.Regression.EFMachine
open TensorCore.EFMachine

/-- Exercise every shift-count encoding on boundary and patterned magnitudes. -/
theorem split_boundaries :
    ([0, 1, 0x7fffff, 0x800000, 0xaaaaaa, 0xffffff] : List (BitVec 24)).all (fun m =>
      (List.range 256).all fun n =>
        let s := splitMagnitude m (BitVec.ofNat 8 n)
        s.coarse.toNat == m.toNat / 2^n * 2^n && s.low.toNat == m.toNat % 2^n) = true := by
  decide +kernel

theorem product_maximum :
    (multiplySignificands 2047 2047).toNat = 4190209 := by decide +kernel

/-- A negative residual is preserved by unsigned magnitude splitting plus its sign. -/
theorem negative_residual :
    signedDyadic true (splitMagnitude 0xffffff 23).low.toNat (-149) =
      signedDyadic true 0xffffff (-149) -
        truncGrid (signedDyadic true 0xffffff (-149)) (-126) := by
  exact splitMagnitude_low_residual true 0xffffff 23 (-149)

end TensorCore.Regression.EFMachine
