import MMAlgebra.Term
import MMAlgebra.Divergence
import MMAlgebra.Schedule
import MMAlgebra.Partition
import MMAlgebra.ChainComplete
import MMAlgebra.LTree
import MMAlgebra.TermComplete
import MMAlgebra.Shapes
import MMAlgebra.Rigid
import MMAlgebra.Rounded
import MMAlgebra.Pairwise
import MMAlgebra.Sub
import MMAlgebra.ParityChain

/-! # Reduction terms and their divergence, on any matrix multiplier

Terms for one output entry, their evaluation on any `Machine` (a block function and a binary32
addition), a structural error bound from per-block and per-addition error contracts, the
divergence of two schedules on one machine or two, the sharper bound when they share work, and
schedules for every length (any order and grouping of the products), as used by the bridge to the
Ozaki schemes, and completeness from laws and base witnesses: chains on any rigid multiplier, and
terms with additions through the rigid, correctly rounded and pairwise normal forms, which are
labeled trees determined by their restrictions to triples of leaves; and chains on parity-pair
multipliers, whose blocks depend on their slots through the unordered pair {odd-slot multiset,
even-slot multiset}.
Imports only Lean's standard library and `Ozaki.Basic`, so it can be used beside either hardware
model. -/
