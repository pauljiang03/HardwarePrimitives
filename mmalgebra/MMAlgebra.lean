import MMAlgebra.Term
import MMAlgebra.Divergence

/-! # Reduction terms and their divergence, on any matrix multiplier

Terms for one output entry, their evaluation on any `Machine` (a block function and a binary32
addition), a structural error bound from per-block and per-addition error contracts, the
divergence of two schedules on one machine or two, and the sharper bound when they share work.
Imports only Lean's standard library and `Ozaki.Basic`, so it can be used beside either hardware
model. -/
