import MatrixCore.MC.Special

/-! # Inner products of any length and the MFMA operation

An inner product of length `k` is evaluated in `⌈k / N_FMA⌉` zero-padded blocks, each block's
output being the next block's `c`. -/

namespace MatrixCore

/-- Split into consecutive pieces of length `n` (the last one may be shorter). -/
def chunks (n : ℕ) : ℕ → List α → List (List α)
  | _, [] => []
  | 0, _ => []
  | fuel + 1, xs => xs.take n :: chunks n fuel (xs.drop n)

/-- Pad with zero words to a multiple of `N_FMA`. -/
def padToBlocks (n : ℕ) (xs : List (BitVec w)) : List (BitVec w) :=
  xs ++ List.replicate ((n - xs.length % n) % n) 0

/-- The blocks `(a, b)` of an inner product. -/
def blocks (P : Model) (a : List P.a.Word) (b : List P.b.Word) :
    List (List P.a.Word × List P.b.Word) :=
  let a' := padToBlocks P.nfma a
  let b' := padToBlocks P.nfma b
  List.zip (chunks P.nfma a'.length a') (chunks P.nfma b'.length b')

/-- Finite-domain inner product `d = Σ a_ℓ b_ℓ + c`, block by block. -/
def dotBits (P : Model) (a : List P.a.Word) (b : List P.b.Word) (c : F32) :
    Except ModelError F32 :=
  if a.length ≠ b.length then .error .wrongLength
  else (blocks P a b).foldlM (fun c ab => blockBits (P := P) ⟨ab.1, ab.2, c⟩) c

/-- An FP32 word as an observation. -/
def observe32 (w : F32) : Outcome :=
  match fp32.decode w with
  | .finite _ => .finite w
  | .infinity s => .infinity s
  | .nan => .nan

/-- Observed inner product for any input words; an infinity is passed on as the next `c`. -/
def dotOutcome (P : Model) (a : List P.a.Word) (b : List P.b.Word) (c : F32) : Option Outcome :=
  if a.length ≠ b.length then none
  else (blocks P a b).foldlM (fun o ab =>
    match o with
    | .finite c => blockOutcome (P := P) ⟨ab.1, ab.2, c⟩
    | .infinity s => blockOutcome (P := P) ⟨ab.1, ab.2, infinity32 s⟩
    | .nan => some .nan) (observe32 c)

/-- `D = AB + C` with `A` given by rows, `B` by columns, and `C` by rows. -/
def mfma (P : Model) (A : List (List P.a.Word)) (B : List (List P.b.Word))
    (C : List (List F32)) : List (List (Option Outcome)) :=
  List.zipWith (fun row cRow => List.zipWith (fun col c => dotOutcome P row col c) B cRow) A C

end MatrixCore
