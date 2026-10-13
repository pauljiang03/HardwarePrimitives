import MCFloat.Equivalence.Block

/-! # Inner products

Chaining blocks: for any inner dimension and any input words, the FloatLib inner product
observes as Matrix-Core's `dotOutcome`. -/

set_option linter.unusedSimpArgs false

namespace MCFloat.Equivalence
open FloatLib.Floats.Formats.BinaryInterchange

theorem pad_map {w : ℕ} (n : ℕ) (xs : List (BitVec w)) :
    MCFloat.pad n (xs.map BitVec.toNat) = (MatrixCore.padToBlocks n xs).map BitVec.toNat := by
  simp [MCFloat.pad, MatrixCore.padToBlocks]

theorem chunks_map (f : α → β) (n : ℕ) :
    ∀ (k : ℕ) (l : List α),
      MCFloat.chunks n k (l.map f) = (MatrixCore.chunks n k l).map (List.map f)
  | _, [] => by simp [MCFloat.chunks, MatrixCore.chunks]
  | 0, _ :: _ => by simp [MCFloat.chunks, MatrixCore.chunks]
  | k + 1, x :: xs => by
    simp only [List.map_cons, MCFloat.chunks, MatrixCore.chunks]
    rw [← List.map_cons, ← List.map_take, ← List.map_drop, chunks_map f n k]

theorem decode_infinity_inv (n : ℕ) (hn : n < 2 ^ 32) (s : Bool)
    (h : MatrixCore.binary32.decodeNat n = .infinity s) : n = (MatrixCore.infinity32 s).toNat := by
  unfold MatrixCore.Format.decodeNat at h
  simp (config := { decide := true }) only [show MatrixCore.binary32.mantissaBits = 23 from rfl,
    show MatrixCore.binary32.exponentBits = 8 from rfl,
    show MatrixCore.binary32.specials = .ieee from rfl, Nat.reducePow, Nat.reduceAdd,
    Nat.reduceSub] at h
  split at h
  · split at h
    · simp only [MatrixCore.Datum.infinity.injEq] at h
      subst h
      unfold MatrixCore.infinity32
      split <;> rename_i hs <;> simp at hs <;> simp <;> omega
    · simp at h
  · simp at h

theorem inf_bits {w : MCFloat.F32} {s : Bool} (h : MCFloat.classifyModel w = .inf s) :
    MCFloat.bits w = (MatrixCore.infinity32 s).toNat := by
  have hc := classify_word w
  rw [h] at hc
  cases hd : MatrixCore.binary32.decodeNat (MCFloat.bits w) <;> rw [hd] at hc <;>
    simp only [Agree] at hc
  subst hc
  exact decode_infinity_inv _ (bits_lt w) _ hd

theorem observe_word (w : MatrixCore.F32) :
    observe (MCFloat.ofNat .binary32 w.toNat) = MatrixCore.observe32 w := by
  have hc := binary32_agree w.toNat w.isLt
  have hb : MCFloat.bits (MCFloat.ofNat .binary32 w.toNat) = w.toNat := ofNat_bits _ _ w.isLt
  unfold observe MatrixCore.observe32
  rw [hb]
  change Agree (MCFloat.classifyModel (MCFloat.ofNat .binary32 w.toNat))
    (MatrixCore.binary32.decode w) at hc
  cases hm : MCFloat.classifyModel (MCFloat.ofNat .binary32 w.toNat) <;>
    cases hd : MatrixCore.binary32.decode w <;> rw [hm, hd] at hc <;> simp only [Agree] at hc <;>
    simp [hc]

theorem fold_agree {P : MCFloat.MCModel} {Q : MatrixCore.Model} (h : Corresponds P Q)
    (L : List (List Q.a.Word × List Q.b.Word)) (w : MCFloat.F32) (o : MatrixCore.Outcome)
    (hwo : observe w = o) :
    ((L.map fun (ab : List Q.a.Word × List Q.b.Word) =>
        (ab.1.map BitVec.toNat, ab.2.map BitVec.toNat)).foldlM
        (fun (w : MCFloat.F32) (ab : List ℕ × List ℕ) => match MCFloat.classifyModel w with
          | .nan => some w
          | _ => MCFloat.block P ab.1 ab.2 (MCFloat.bits w)) w).map observe =
      L.foldlM (fun o ab => match o with
        | .finite c => MatrixCore.blockOutcome (P := Q) ⟨ab.1, ab.2, c⟩
        | .infinity s => MatrixCore.blockOutcome (P := Q) ⟨ab.1, ab.2, MatrixCore.infinity32 s⟩
        | .nan => some .nan) o := by
  induction L generalizing w o with
  | nil => simp [hwo]
  | cons ab L ih =>
    simp only [List.map_cons, List.foldlM_cons]
    cases hm : MCFloat.classifyModel w with
    | nan =>
      have : o = .nan := by rw [← hwo]; simp [observe, hm]
      subst this
      simp only [Option.bind_eq_bind, Option.bind_some]
      exact ih w .nan hwo
    | inf s =>
      have : o = .infinity s := by rw [← hwo]; simp [observe, hm]
      subst this
      have hb := block_agree h ⟨ab.1, ab.2, MatrixCore.infinity32 s⟩
      simp only [inf_bits hm] at hb ⊢
      cases hk : MCFloat.block P (ab.1.map BitVec.toNat) (ab.2.map BitVec.toNat)
          (MatrixCore.infinity32 s).toNat with
      | none => rw [hk] at hb; simp [← hb]
      | some w' =>
        rw [hk] at hb
        simp only [Option.map_some] at hb
        simp only [Option.bind_eq_bind, Option.bind_some, ← hb]
        exact ih w' _ rfl
    | finite t =>
      have : o = .finite (BitVec.ofNat 32 (MCFloat.bits w)) := by rw [← hwo]; simp [observe, hm]
      subst this
      have hb := block_agree h ⟨ab.1, ab.2, BitVec.ofNat 32 (MCFloat.bits w)⟩
      have hn : (BitVec.ofNat 32 (MCFloat.bits w)).toNat = MCFloat.bits w := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (bits_lt w)
      simp only [hn] at hb
      cases hk : MCFloat.block P (ab.1.map BitVec.toNat) (ab.2.map BitVec.toNat) (MCFloat.bits w) with
      | none => rw [hk] at hb; simp [← hb]
      | some w' =>
        rw [hk] at hb
        simp only [Option.map_some] at hb
        simp only [Option.bind_eq_bind, Option.bind_some, ← hb]
        exact ih w' _ rfl

/-- **Inner products.** For corresponding models, any inner dimension and any input words, the
FloatLib inner product observes as Matrix-Core's `dotOutcome`. -/
theorem dot_agree {P : MCFloat.MCModel} {Q : MatrixCore.Model} (h : Corresponds P Q)
    (a : List Q.a.Word) (b : List Q.b.Word) (c : MatrixCore.F32) :
    (MCFloat.dot P (a.map BitVec.toNat) (b.map BitVec.toNat) c.toNat).map observe =
      MatrixCore.dotOutcome Q a b c := by
  unfold MCFloat.dot MatrixCore.dotOutcome MatrixCore.blocks
  simp only [List.length_map]
  split
  · rfl
  · rw [pad_map, pad_map, List.length_map, List.length_map, h.nfma, chunks_map, chunks_map,
      List.zip_map]
    exact fold_agree h _ _ _ (observe_word c)

end MCFloat.Equivalence
