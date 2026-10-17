import OzakiTC.Correct

/-! # TensorCore's binary64 round to nearest is IEEE's, within the finite range

The Ozaki Tensor Core schemes round with IEEE's round to nearest even (`round32Value` is
`Ozaki.rne32Q`, `fp64Round` is `Ozaki.rne64`). TensorCore's own binary64 rounding (`roundBinary
fp64 .nearestEven`, `fp64RoundTC`) computes the same value before its overflow check: the same
exponent, grid and ties-to-even integer rounding (`binarySignedRounded_eq_rneU`). It differs only
in overflow: it returns no result above the largest finite value, where IEEE rounds values below
half an ulp above it down to it. So on every input of magnitude at most the largest finite value
the two agree (`fp64RoundTC_eq`), and every result TensorCore's rounding returns is IEEE's
(`fp64Round_of_TC`). The binary32 statements are in `OzakiTC.Rounding` (`round32ValueTC_eq`). -/

open TensorCore

namespace Ozaki.TC

theorem binaryMagnitudeRounded_eq_rneMag (neg : Bool) (m : ℚ) :
    binaryMagnitudeRounded fp64 .nearestEven neg m = rneMag 53 (-1022) m := rfl

/-- TensorCore's rounded binary64 value is IEEE's, before the overflow check. -/
theorem binarySignedRounded_eq_rneU (q : ℚ) :
    binarySignedRounded fp64 .nearestEven q = rneU 53 (-1022) q := by
  unfold binarySignedRounded rneU
  by_cases h : q < 0
  · have : absQ q = -q := by unfold absQ; simp [h]
    rw [if_pos h, if_pos h, this, binaryMagnitudeRounded_eq_rneMag]
  · have : absQ q = q := by unfold absQ; simp [h]
    rw [if_neg h, if_neg h, this, binaryMagnitudeRounded_eq_rneMag]

/-- **TensorCore's binary64 round to nearest is IEEE's** on every input of magnitude at most the
largest finite value. -/
theorem fp64RoundTC_eq {q : ℚ} (hq : absQ q ≤ fp64.maxFinite) : fp64RoundTC q = fp64Round q := by
  by_cases h0 : q = 0
  · subst h0; decide +kernel
  · obtain ⟨bits, hb, hv, _⟩ := roundBinary_nonzero_spec fp64 fp64_wellFormed .nearestEven q h0 hq
    have hfin := binaryValue_finiteValue fp64_wellFormed hv
    have habs := Format.finiteValue_abs_le fp64 hfin
    rw [binarySignedRounded_eq_rneU, absQ_eq] at habs
    unfold fp64RoundTC fp64Round rne64 roundRNE
    rw [hb, Option.bind_some, hv, binarySignedRounded_eq_rneU, ← fp64_maxFinite_eq_maxFormat,
      if_pos habs]

/-- A result TensorCore's binary64 rounding returns is IEEE's. -/
theorem fp64Round_of_TC {q v : ℚ} (h : fp64RoundTC q = some v) : fp64Round q = some v := by
  have hr : absQ q ≤ fp64.maxFinite := by
    unfold fp64RoundTC at h
    cases hw : roundBinary fp64 .nearestEven q with
    | none => simp [hw] at h
    | some w => exact (roundBinary_range hw).2
  rw [← fp64RoundTC_eq hr]; exact h

end Ozaki.TC
