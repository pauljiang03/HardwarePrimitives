import MatrixCore.MC.Composition
import MatrixCore.MC.CorrectRounding

/-! # Inner products of several blocks

An inner product of length `N_FMA` is one block, and binary32 inputs form an SFMA: each product
is added to the running result by one correctly rounded fused step,
`d = fl{(…fl{fl{c + p₁} + p₂}…) + p_k}`. -/

namespace MatrixCore

theorem chunks_single (n : ℕ) (xs : List α) (hn : 0 < n) (hlen : xs.length = n) (fuel : ℕ)
    (hf : 0 < fuel) : chunks n fuel xs = [xs] := by
  cases fuel with
  | zero => omega
  | succ f =>
    cases xs with
    | nil => simp at hlen; omega
    | cons x xs =>
      simp only [chunks]
      rw [List.take_of_length_le (by omega), List.drop_of_length_le (by omega)]
      cases f <;> rfl

theorem padToBlocks_exact (n : ℕ) (xs : List (BitVec w)) (h : xs.length = n) :
    padToBlocks n xs = xs := by
  unfold padToBlocks; rw [h]; simp

/-- An inner product with exactly `N_FMA` products is one block. -/
theorem dotBits_single (P : Model) (hn : 0 < P.nfma) (a : List P.a.Word) (b : List P.b.Word)
    (c : F32) (ha : a.length = P.nfma) (hb : b.length = P.nfma) :
    dotBits P a b c = blockBits (P := P) ⟨a, b, c⟩ := by
  unfold dotBits blocks
  rw [if_neg (by omega), padToBlocks_exact _ _ ha, padToBlocks_exact _ _ hb]
  dsimp only
  rw [chunks_single _ _ hn ha _ (by omega), chunks_single _ _ hn hb _ (by omega)]
  simp only [List.zip_cons_cons, List.zip_nil_left, List.foldlM_cons, List.foldlM_nil, bind_pure]

theorem chunks_one (xs : List α) : ∀ fuel, xs.length ≤ fuel → chunks 1 fuel xs = xs.map ([·]) := by
  induction xs with
  | nil => intro fuel _; cases fuel <;> rfl
  | cons x xs ih =>
    intro fuel h
    cases fuel with
    | zero => simp at h
    | succ f =>
      simp only [chunks, List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero,
        List.map_cons]
      rw [ih f (by simp at h; omega)]

theorem blocks_sfma (a : List sfmaF32.a.Word) (b : List sfmaF32.b.Word) :
    blocks sfmaF32 a b = List.zip (a.map ([·])) (b.map ([·])) := by
  unfold blocks
  have hpa : padToBlocks sfmaF32.nfma a = a := by
    unfold padToBlocks; rw [show sfmaF32.nfma = 1 from rfl, Nat.mod_one]; simp
  have hpb : padToBlocks sfmaF32.nfma b = b := by
    unfold padToBlocks; rw [show sfmaF32.nfma = 1 from rfl, Nat.mod_one]; simp
  rw [hpa, hpb]
  dsimp only
  rw [show sfmaF32.nfma = 1 from rfl, chunks_one a _ (Nat.le_refl _), chunks_one b _ (Nat.le_refl _)]

/-- binary32 inputs: one correctly rounded fused step per product, `c` first. -/
theorem dotBits_sfma_cons (a : sfmaF32.a.Word) (as : List sfmaF32.a.Word) (b : sfmaF32.b.Word)
    (bs : List sfmaF32.b.Word) (c : F32) (h : as.length = bs.length) :
    dotBits sfmaF32 (a :: as) (b :: bs) c =
      (blockBits (P := sfmaF32) ⟨[a], [b], c⟩).bind fun d => dotBits sfmaF32 as bs d := by
  have h1 : dotBits sfmaF32 (a :: as) (b :: bs) c =
      (blocks sfmaF32 (a :: as) (b :: bs)).foldlM
        (fun c ab => blockBits (P := sfmaF32) ⟨ab.1, ab.2, c⟩) c := by
    unfold dotBits; rw [if_neg (by simp [h])]
  have h2 : ∀ d, dotBits sfmaF32 as bs d =
      (blocks sfmaF32 as bs).foldlM (fun c ab => blockBits (P := sfmaF32) ⟨ab.1, ab.2, c⟩) d := by
    intro d; unfold dotBits; rw [if_neg (by simp [h])]
  rw [h1]
  simp only [h2]
  rw [blocks_sfma, blocks_sfma]
  simp only [List.map_cons, List.zip_cons_cons, List.foldlM_cons]
  rfl

/-- Each SFMA step is the binary32 value nearest to `c + a · b`, ties to even. -/
theorem sfma_step_nearestEven {a b c d : F32} {t : BlockTrace sfmaF32}
    (h : evalBlock (P := sfmaF32) ⟨[a], [b], c⟩ = .ok t) (hd : t.d = d) :
    NearestEven32 t.prepared.exact d := by
  rw [← hd]; exact sfmaF32_nearestEven h

end MatrixCore
