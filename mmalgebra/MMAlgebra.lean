import MMAlgebra.Term
import MMAlgebra.Divergence
import MMAlgebra.Schedule

/-! # Reduction terms and their divergence, on any matrix multiplier

Terms for one output entry, their evaluation on any `Machine` (a block function and a binary32
addition), a structural error bound from per-block and per-addition error contracts, the
divergence of two schedules on one machine or two, the sharper bound when they share work, and
schedules for every length (any order and grouping of the products), as used by the bridge to the
Ozaki schemes.
Imports only Lean's standard library and `Ozaki.Basic`, so it can be used beside either hardware
model. -/
