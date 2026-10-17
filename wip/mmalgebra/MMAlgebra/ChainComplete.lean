import MMAlgebra.Term
import MMAlgebra.Partition

/-! # Completeness for chains on any rigid matrix multiplier

A chain from the zero accumulator is run block by block on a `Machine` (`runChain`); as a reduction
term it is `Chain.term`. This file proves, once for every matrix multiplier, that the ordered
partition `Chain.nf` decides when two chains are equivalent, from a few laws of the machine and five
concrete block evaluations:

* **Restriction** (`runChain_mask`): an empty slot reads as a fixed operand pair `z` (on every model
  the zero pair), so on an input that is `z` outside a support `S` a chain runs as its restriction
  to `S`.
* **Laws** (`RigidLaws`): a block depends on its slots as a multiset, and an empty block passes a
  *good* accumulator through (on the models: finite and not `−0`).
* **Base witnesses** (`PairWitness`): two operand pairs and five block evaluations that separate the
  three ways a chain can hold two products.

`chain_complete`: two chains over the same products, each once, with different ordered partitions,
differ on an input supported on two products. `chain_sound`: if every block output is good, chains
with the same ordered partition agree on every input. Together (`chain_equiv_iff`): two chains are
equivalent exactly when they have the same ordered partition. Hardware-independent. -/

local notation "ℕ" => Nat

namespace MMAlgebra

variable {α β : Type}

/-- Run the blocks of a chain from the accumulator word `d`. -/
def runChain (m : Machine α β) (p : ℕ → α) : β → Chain → Option β
  | d, [] => some d
  | d, B :: σ => (m.block d (B.map (Option.map p))).bind fun d' => runChain m p d' σ

/-- A chain as a reduction term. -/
def Chain.term (σ : Chain) : Term := σ.foldl (fun t B => .blk t B) .zero

theorem eval_foldl (m : Machine α β) (p : ℕ → α) (c h : β) :
    ∀ (σ : Chain) (t : Term),
      eval m p c h (σ.foldl (fun t B => .blk t B) t) = (eval m p c h t).bind fun d => runChain m p d σ
  | [], t => by simp only [List.foldl_nil]; cases eval m p c h t <;> rfl
  | B :: σ, t => by
    simp only [List.foldl_cons]
    rw [eval_foldl m p c h σ (.blk t B)]
    simp only [eval, runChain, Option.bind_assoc]

/-- A chain term evaluates by running its blocks from the zero accumulator. -/
theorem eval_chain (m : Machine α β) (p : ℕ → α) (c h : β) (σ : Chain) :
    eval m p c h σ.term = runChain m p m.zero σ := by
  unfold Chain.term; rw [eval_foldl]; rfl

/-! ## Restriction to a support -/

/-- The input that is `p` on the support `S` and the operand pair `z` elsewhere. -/
def mask (z : α) (S : ℕ → Bool) (p : ℕ → α) : ℕ → α := fun i => if S i then p i else z

/-- Empty every slot outside `S`. -/
def Chain.restrict (S : ℕ → Bool) (σ : Chain) : Chain := σ.map (List.map (·.filter S))

/-- A machine whose blocks read an empty slot as the operand pair `z`. -/
def SlotZero (m : Machine α β) (z : α) : Prop :=
  ∀ d (ps qs : List (Option α)), ps.map (·.getD z) = qs.map (·.getD z) → m.block d ps = m.block d qs

/-- **Restriction.** On an input that is `z` outside `S`, a chain runs as its restriction to `S`. -/
theorem runChain_mask {m : Machine α β} {z : α} (hz : SlotZero m z) (S : ℕ → Bool) (p : ℕ → α) :
    ∀ (σ : Chain) (d : β), runChain m (mask z S p) d σ = runChain m p d (σ.restrict S)
  | [], _ => rfl
  | B :: σ, d => by
    simp only [Chain.restrict, List.map_cons, runChain] at *
    have hb : m.block d (B.map (Option.map (mask z S p))) =
        m.block d ((B.map (·.filter S)).map (Option.map p)) := by
      apply hz
      simp only [List.map_map]
      apply List.map_congr_left
      intro o _
      cases o with
      | none => rfl
      | some i => by_cases hi : S i = true <;> simp [mask, Option.filter, hi]
    rw [hb]
    cases m.block d ((B.map (·.filter S)).map (Option.map p)) with
    | none => rfl
    | some d' => exact runChain_mask hz S p σ d'

/-! ## Laws of a rigid matrix multiplier -/

/-- The laws of a rigid matrix multiplier with FMA size `K` that chain completeness uses: an empty
slot reads as the operand pair `z`; a block depends on its slots as a multiset; an empty block
passes a good accumulator through; the zero accumulator is good. -/
structure RigidLaws (m : Machine α β) (K : ℕ) where
  z : α
  good : β → Prop
  slot : SlotZero m z
  perm : ∀ d {ps qs : List (Option α)}, ps.Perm qs → m.block d ps = m.block d qs
  zero_good : good m.zero
  pass : ∀ d, good d → m.block d (List.replicate K none) = some d

/-! ## Blocks restricted to two products -/

/-- The support `{x, y}`. -/
def pairSet (x y : ℕ) : ℕ → Bool := fun i => i == x || i == y

/-- The canonical block of a kind: its products first, then empty slots. -/
def canon (K x y : ℕ) : PairKind → List (Option ℕ)
  | .none => List.replicate K none
  | .fst => some x :: List.replicate (K - 1) none
  | .snd => some y :: List.replicate (K - 1) none
  | .both => some x :: some y :: List.replicate (K - 2) none

theorem count_map_filter (S : ℕ → Bool) (B : List (Option ℕ)) (i : ℕ) :
    (B.map (·.filter S)).count (some i) = if S i then B.count (some i) else 0 := by
  induction B with
  | nil => simp
  | cons b B ih =>
    simp only [List.map_cons, List.count_cons, ih]
    cases b with
    | none => simp [Option.filter]
    | some j =>
      by_cases hji : j = i
      · subst hji; by_cases hj : S j = true <;> simp [Option.filter, hj]
      · by_cases hj : S j = true <;> by_cases hi : S i = true <;> simp [Option.filter, hj, hi, hji]

theorem length_eq_counts {x y : ℕ} (hxy : x ≠ y) :
    ∀ (R : List (Option ℕ)), (∀ o ∈ R, o = none ∨ o = some x ∨ o = some y) →
      R.length = R.count none + R.count (some x) + R.count (some y)
  | [], _ => rfl
  | o :: R, h => by
    have ih := length_eq_counts hxy R (fun o' h' => h o' (by simp [h']))
    rcases h o (by simp) with rfl | rfl | rfl <;>
      simp [hxy, Ne.symm hxy] <;> omega

theorem canon_length (K x y : ℕ) (hK : 2 ≤ K) (k : PairKind) : (canon K x y k).length = K := by
  cases k <;> simp [canon] <;> omega

theorem canon_mem (K x y : ℕ) (k : PairKind) :
    ∀ o ∈ canon K x y k, o = none ∨ o = some x ∨ o = some y := by
  intro o ho
  cases k <;> simp [canon, List.mem_replicate] at ho <;> grind

/-- A block restricted to `{x, y}` is a permutation of the canonical block of its kind. -/
theorem restrict_perm_canon {x y : ℕ} (hxy : x ≠ y) (K : ℕ) (hK : 2 ≤ K) (B : List (Option ℕ))
    (hlen : B.length = K) (hx1 : B.count (some x) ≤ 1) (hy1 : B.count (some y) ≤ 1) :
    (B.map (·.filter (pairSet x y))).Perm (canon K x y (pairKind x y B)) := by
  have hRm : ∀ o ∈ B.map (·.filter (pairSet x y)), o = none ∨ o = some x ∨ o = some y := by
    intro o ho
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp ho
    cases b with
    | none => simp
    | some j =>
      by_cases hj : pairSet x y j = true
      · have : j = x ∨ j = y := by simpa [pairSet] using hj
        rcases this with rfl | rfl <;> simp [Option.filter, hj]
      · simp [Option.filter, hj]
  have hRl : (B.map (·.filter (pairSet x y))).length = K := by simp [hlen]
  have hCl := canon_length K x y hK (pairKind x y B)
  have eR := length_eq_counts hxy _ hRm
  have eC := length_eq_counts hxy _ (canon_mem K x y (pairKind x y B))
  have cRx : (B.map (·.filter (pairSet x y))).count (some x) = B.count (some x) := by
    rw [count_map_filter]; simp [pairSet]
  have cRy : (B.map (·.filter (pairSet x y))).count (some y) = B.count (some y) := by
    rw [count_map_filter]; simp [pairSet]
  have kx : (some x ∈ B) ↔ B.count (some x) = 1 := by rw [← List.count_pos_iff]; omega
  have ky : (some y ∈ B) ↔ B.count (some y) = 1 := by rw [← List.count_pos_iff]; omega
  have hCx : (canon K x y (pairKind x y B)).count (some x) = B.count (some x) := by
    unfold pairKind
    by_cases h1 : some x ∈ B <;> by_cases h2 : some y ∈ B <;>
      simp only [h1, h2, if_true, if_false] <;>
      simp [canon, List.count_replicate, Ne.symm hxy] <;>
      first | exact (kx.mp h1).symm | exact (List.count_eq_zero.mpr h1).symm
  have hCy : (canon K x y (pairKind x y B)).count (some y) = B.count (some y) := by
    unfold pairKind
    by_cases h1 : some x ∈ B <;> by_cases h2 : some y ∈ B <;>
      simp only [h1, h2, if_true, if_false] <;>
      simp [canon, List.count_replicate, hxy] <;>
      first | exact (ky.mp h2).symm | exact (List.count_eq_zero.mpr h2).symm
  rw [List.perm_iff_count]
  intro o
  cases o with
  | none => omega
  | some i =>
    by_cases hix : i = x
    · subst hix; rw [cRx, hCx]
    · by_cases hiy : i = y
      · subst hiy; rw [cRy, hCy]
      · have h1 : (B.map (·.filter (pairSet x y))).count (some i) = 0 := by
          rw [count_map_filter]; simp [pairSet, hix, hiy]
        have h2 : (canon K x y (pairKind x y B)).count (some i) = 0 := by
          apply List.count_eq_zero.mpr
          intro hm
          rcases canon_mem K x y _ _ hm with h | h | h <;> simp at h <;> omega
        rw [h1, h2]

/-- Run the canonical blocks of a list of kinds. -/
def runPat (m : Machine α β) (p : ℕ → α) (K x y : ℕ) : β → List PairKind → Option β
  | d, [] => some d
  | d, k :: ks => (m.block d ((canon K x y k).map (Option.map p))).bind fun d' => runPat m p K x y d' ks

theorem count_blockLeaves (B : List (Option ℕ)) (i : ℕ) :
    B.count (some i) = (blockLeaves B).count i := by
  induction B with
  | nil => rfl
  | cons o B ih =>
    cases o with
    | none => simpa [blockLeaves] using ih
    | some j =>
      simp only [blockLeaves, List.filterMap_cons, id, List.count_cons] at ih ⊢
      rw [ih]
      by_cases hj : j = i <;> simp [hj]

theorem count_le_one_of_nodup {σ : Chain} (h : σ.leaves.Nodup) {B : List (Option ℕ)} (hB : B ∈ σ)
    (i : ℕ) : B.count (some i) ≤ 1 := by
  rw [count_blockLeaves]
  have hsub : (blockLeaves B).Sublist σ.leaves := by
    unfold Chain.leaves
    exact List.sublist_flatten_of_mem (List.mem_map.mpr ⟨B, hB, rfl⟩)
  exact List.nodup_iff_count.mp (hsub.nodup h) i

/-- On the support `{x, y}`, a chain runs its pattern of canonical blocks, provided every value the
pattern passes through is good (empty blocks pass those values through). -/
theorem runChain_pair {m : Machine α β} {K : ℕ} (L : RigidLaws m K) (hK : 2 ≤ K) {x y : ℕ}
    (hxy : x ≠ y) (p : ℕ → α) :
    ∀ (σ : Chain) (d : β),
      (∀ B ∈ σ, B.length = K ∧ B.count (some x) ≤ 1 ∧ B.count (some y) ≤ 1) →
      (∀ ks₁ ks₂ v, pattern x y σ = ks₁ ++ ks₂ → runPat m p K x y d ks₁ = some v → L.good v) →
      runChain m p d (σ.restrict (pairSet x y)) = runPat m p K x y d (pattern x y σ)
  | [], _, _, _ => rfl
  | B :: σ, d, hwf, hgood => by
    have hB := hwf B (by simp)
    have hperm := restrict_perm_canon hxy K hK B hB.1 hB.2.1 hB.2.2
    have hblk := L.perm d (hperm.map (Option.map p))
    have hwf' : ∀ B' ∈ σ, B'.length = K ∧ B'.count (some x) ≤ 1 ∧ B'.count (some y) ≤ 1 :=
      fun B' h' => hwf B' (by simp [h'])
    simp only [Chain.restrict, List.map_cons, runChain] at hblk ⊢
    rw [hblk]
    rw [pattern_cons] at hgood ⊢
    by_cases hk : pairKind x y B = .none
    · rw [if_pos hk] at hgood ⊢
      have hd : L.good d := hgood [] (pattern x y σ) d (by simp) rfl
      rw [hk]
      simp only [canon, List.map_replicate, Option.map_none]
      rw [L.pass d hd]
      exact runChain_pair L hK hxy p σ d hwf' hgood
    · rw [if_neg hk] at hgood ⊢
      simp only [runPat]
      cases hb : m.block d ((canon K x y (pairKind x y B)).map (Option.map p)) with
      | none => rfl
      | some d' =>
        simp only [Option.bind_some]
        refine runChain_pair L hK hxy p σ d' hwf' ?_
        intro ks₁ ks₂ v he hv
        exact hgood (pairKind x y B :: ks₁) ks₂ v (by rw [he]; rfl)
          (by simp only [runPat, hb, Option.bind_some]; exact hv)

/-- The three ways a chain can hold two products, each once. -/
def pairPats : List (List PairKind) := [[.both], [.fst, .snd], [.snd, .fst]]

theorem pattern_nil_of_not_mem {x y : ℕ} : ∀ {σ : Chain}, x ∉ σ.leaves → y ∉ σ.leaves →
    pattern x y σ = []
  | [], _, _ => rfl
  | B :: σ, hx, hy => by
    rw [leaves_cons, List.mem_append, not_or] at hx hy
    rw [pattern_cons, if_pos (pairKind_none (fun h => hx.1 (mem_blockLeaves.mpr h))
      (fun h => hy.1 (mem_blockLeaves.mpr h)))]
    exact pattern_nil_of_not_mem hx.2 hy.2

theorem pattern_snd {x y : ℕ} : ∀ {σ : Chain}, σ.leaves.Nodup → x ∉ σ.leaves → y ∈ σ.leaves →
    pattern x y σ = [.snd]
  | [], _, _, hy => by simp [Chain.leaves] at hy
  | B :: σ, hn, hx, hy => by
    obtain ⟨n', _, o⟩ := nodup_tail hn
    rw [leaves_cons, List.mem_append, not_or] at hx
    rw [leaves_cons, List.mem_append] at hy
    have hxB : some x ∉ B := fun h => hx.1 (mem_blockLeaves.mpr h)
    rw [pattern_cons]
    by_cases hyB : y ∈ blockLeaves B
    · have hk : pairKind x y B = .snd := by
        unfold pairKind; rw [if_neg hxB, if_pos (mem_blockLeaves.mp hyB)]
      rw [hk, if_neg (by decide), pattern_nil_of_not_mem hx.2 (o y hyB)]
    · have hy' : y ∈ Chain.leaves σ := by rcases hy with h | h; exact absurd h hyB; exact h
      rw [if_pos (pairKind_none hxB (fun h => hyB (mem_blockLeaves.mpr h)))]
      exact pattern_snd n' hx.2 hy'

theorem pattern_fst {x y : ℕ} : ∀ {σ : Chain}, σ.leaves.Nodup → x ∈ σ.leaves → y ∉ σ.leaves →
    pattern x y σ = [.fst]
  | [], _, hx, _ => by simp [Chain.leaves] at hx
  | B :: σ, hn, hx, hy => by
    obtain ⟨n', _, o⟩ := nodup_tail hn
    rw [leaves_cons, List.mem_append, not_or] at hy
    rw [leaves_cons, List.mem_append] at hx
    have hyB : some y ∉ B := fun h => hy.1 (mem_blockLeaves.mpr h)
    rw [pattern_cons]
    by_cases hxB : x ∈ blockLeaves B
    · have hk : pairKind x y B = .fst := by
        unfold pairKind; rw [if_pos (mem_blockLeaves.mp hxB), if_neg hyB]
      rw [hk, if_neg (by decide), pattern_nil_of_not_mem (o x hxB) hy.2]
    · have hx' : x ∈ Chain.leaves σ := by rcases hx with h | h; exact absurd h hxB; exact h
      rw [if_pos (pairKind_none (fun h => hxB (mem_blockLeaves.mpr h)) hyB)]
      exact pattern_fst n' hx' hy.2

/-- A chain holding two products, each once, holds them in one of three patterns. -/
theorem pattern_mem {x y : ℕ} (hxy : x ≠ y) : ∀ {σ : Chain}, σ.leaves.Nodup → x ∈ σ.leaves →
    y ∈ σ.leaves → pattern x y σ ∈ pairPats
  | [], _, hx, _ => by simp [Chain.leaves] at hx
  | B :: σ, hn, hx, hy => by
    obtain ⟨n', _, o⟩ := nodup_tail hn
    rw [leaves_cons, List.mem_append] at hx hy
    rw [pattern_cons]
    by_cases hxB : x ∈ blockLeaves B <;> by_cases hyB : y ∈ blockLeaves B
    · have hk : pairKind x y B = .both := by
        unfold pairKind; rw [if_pos (mem_blockLeaves.mp hxB), if_pos (mem_blockLeaves.mp hyB)]
      rw [hk, if_neg (by decide), pattern_nil_of_not_mem (o x hxB) (o y hyB)]; simp [pairPats]
    · have hy' : y ∈ Chain.leaves σ := by rcases hy with h | h; exact absurd h hyB; exact h
      have hk : pairKind x y B = .fst := by
        unfold pairKind
        rw [if_pos (mem_blockLeaves.mp hxB), if_neg (fun h => hyB (mem_blockLeaves.mpr h))]
      rw [hk, if_neg (by decide), pattern_snd n' (o x hxB) hy']; simp [pairPats]
    · have hx' : x ∈ Chain.leaves σ := by rcases hx with h | h; exact absurd h hxB; exact h
      have hk : pairKind x y B = .snd := by
        unfold pairKind
        rw [if_neg (fun h => hxB (mem_blockLeaves.mpr h)), if_pos (mem_blockLeaves.mp hyB)]
      rw [hk, if_neg (by decide), pattern_fst n' hx' (o y hyB)]; simp [pairPats]
    · have hx' : x ∈ Chain.leaves σ := by rcases hx with h | h; exact absurd h hxB; exact h
      have hy' : y ∈ Chain.leaves σ := by rcases hy with h | h; exact absurd h hyB; exact h
      rw [if_pos (pairKind_none (fun h => hxB (mem_blockLeaves.mpr h))
        (fun h => hyB (mem_blockLeaves.mpr h)))]
      exact pattern_mem hxy n' hx' hy'

/-! ## Base witnesses and completeness -/

/-- Base witnesses for two products on a rigid machine: operand pairs `a` and `b`, and the five
block evaluations of the three patterns (`[a b]`, `[a] [b]`, `[b] [a]`), with good values; the
patterns `[a] [b]` and `[b] [a]` differ, and the joint block differs from one of them. -/
structure PairWitness {m : Machine α β} {K : ℕ} (L : RigidLaws m K) where
  a : α
  b : α
  vx : β
  vy : β
  vxy : β
  vlt : β
  vgt : β
  e₁ : m.block m.zero (some a :: List.replicate (K - 1) none) = some vx
  e₂ : m.block m.zero (some b :: List.replicate (K - 1) none) = some vy
  e₃ : m.block m.zero (some a :: some b :: List.replicate (K - 2) none) = some vxy
  e₄ : m.block vx (some b :: List.replicate (K - 1) none) = some vlt
  e₅ : m.block vy (some a :: List.replicate (K - 1) none) = some vgt
  g₁ : L.good vx
  g₂ : L.good vy
  g₃ : L.good vxy
  g₄ : L.good vlt
  g₅ : L.good vgt
  sep : vlt ≠ vgt ∧ (vxy ≠ vlt ∨ vxy ≠ vgt)

/-- The input with products `u` at `x`, `v` at `y`, and `z` elsewhere. -/
def pairInput (z : α) (x y : ℕ) (u v : α) : ℕ → α :=
  fun i => if i = x then u else if i = y then v else z

theorem pairInput_mask (z : α) (x y : ℕ) (u v : α) :
    mask z (pairSet x y) (pairInput z x y u v) = pairInput z x y u v := by
  funext i
  unfold mask pairInput pairSet
  by_cases hx : i = x
  · simp [hx]
  · by_cases hy : i = y
    · simp [hy]
    · simp [hx, hy]

/-- The value of a chain on a two-product input is the value of its pattern. -/
theorem runChain_pairInput {m : Machine α β} {K : ℕ} (L : RigidLaws m K) (hK : 2 ≤ K) {x y : ℕ}
    (hxy : x ≠ y) (u v : α) (wx wy wxy wl wg : β)
    (f₁ : m.block m.zero (some u :: List.replicate (K - 1) none) = some wx)
    (f₂ : m.block m.zero (some v :: List.replicate (K - 1) none) = some wy)
    (f₃ : m.block m.zero (some u :: some v :: List.replicate (K - 2) none) = some wxy)
    (f₄ : m.block wx (some v :: List.replicate (K - 1) none) = some wl)
    (f₅ : m.block wy (some u :: List.replicate (K - 1) none) = some wg)
    (k₁ : L.good wx) (k₂ : L.good wy) (k₃ : L.good wxy) (k₄ : L.good wl) (k₅ : L.good wg)
    (σ : Chain) (hlen : ∀ B ∈ σ, B.length = K) (hn : σ.leaves.Nodup) (hx : x ∈ σ.leaves)
    (hy : y ∈ σ.leaves) :
    runChain m (pairInput L.z x y u v) m.zero σ =
      some (if pattern x y σ = [.both] then wxy else if pattern x y σ = [.fst, .snd] then wl else wg) := by
  have hpx : (canon K x y .fst).map (Option.map (pairInput L.z x y u v)) =
      some u :: List.replicate (K - 1) none := by
    simp [canon, pairInput, List.map_replicate]
  have hpy : (canon K x y .snd).map (Option.map (pairInput L.z x y u v)) =
      some v :: List.replicate (K - 1) none := by
    simp [canon, pairInput, List.map_replicate, Ne.symm hxy]
  have hpxy : (canon K x y .both).map (Option.map (pairInput L.z x y u v)) =
      some u :: some v :: List.replicate (K - 2) none := by
    simp [canon, pairInput, List.map_replicate, Ne.symm hxy]
  rw [← pairInput_mask, runChain_mask L.slot]
  have hmem := pattern_mem hxy hn hx hy
  have hwf : ∀ B ∈ σ, B.length = K ∧ B.count (some x) ≤ 1 ∧ B.count (some y) ≤ 1 :=
    fun B hB => ⟨hlen B hB, count_le_one_of_nodup hn hB x, count_le_one_of_nodup hn hB y⟩
  simp only [pairPats, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rw [runChain_pair L hK hxy _ σ m.zero hwf]
  · rcases hmem with h | h | h <;> rw [h] <;> simp [runPat, hpx, hpy, hpxy, f₁, f₂, f₃, f₄, f₅]
  · intro ks₁ ks₂ w he hw
    rcases hmem with h | h | h <;> rw [h] at he
    · rcases List.append_eq_singleton_iff.mp he.symm with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · simp only [runPat, Option.some.injEq] at hw; subst hw; exact L.zero_good
      · simp only [runPat, hpxy, f₃, Option.bind_some, Option.some.injEq] at hw; subst hw; exact k₃
    · rcases ks₁ with _ | ⟨k, ks₁⟩
      · simp only [runPat, Option.some.injEq] at hw; subst hw; exact L.zero_good
      · simp only [List.cons_append, List.cons.injEq] at he
        obtain ⟨rfl, he⟩ := he
        rcases List.append_eq_singleton_iff.mp he.symm with ⟨rfl, _⟩ | ⟨rfl, _⟩
        · simp only [runPat, hpx, f₁, Option.bind_some, Option.some.injEq] at hw; subst hw; exact k₁
        · simp only [runPat, hpx, hpy, f₁, f₄, Option.bind_some, Option.some.injEq] at hw
          subst hw; exact k₄
    · rcases ks₁ with _ | ⟨k, ks₁⟩
      · simp only [runPat, Option.some.injEq] at hw; subst hw; exact L.zero_good
      · simp only [List.cons_append, List.cons.injEq] at he
        obtain ⟨rfl, he⟩ := he
        rcases List.append_eq_singleton_iff.mp he.symm with ⟨rfl, _⟩ | ⟨rfl, _⟩
        · simp only [runPat, hpy, f₂, Option.bind_some, Option.some.injEq] at hw; subst hw; exact k₂
        · simp only [runPat, hpx, hpy, f₂, f₅, Option.bind_some, Option.some.injEq] at hw
          subst hw; exact k₅

/-- **Completeness for two products.** Two chains holding `x` and `y` (each product once) in
different patterns differ on an input that is `z` outside `{x, y}`. -/
theorem complete_pair {m : Machine α β} {K : ℕ} (L : RigidLaws m K) (hK : 2 ≤ K) (W : PairWitness L)
    (σ τ : Chain) (hσ : ∀ B ∈ σ, B.length = K) (hτ : ∀ B ∈ τ, B.length = K)
    (nσ : σ.leaves.Nodup) (nτ : τ.leaves.Nodup) {x y : ℕ} (hxy : x ≠ y)
    (hxσ : x ∈ σ.leaves) (hyσ : y ∈ σ.leaves) (hxτ : x ∈ τ.leaves) (hyτ : y ∈ τ.leaves)
    (hne : pattern x y σ ≠ pattern x y τ) :
    ∃ p : ℕ → α, (∀ i, i ≠ x → i ≠ y → p i = L.z) ∧
      runChain m p m.zero σ ≠ runChain m p m.zero τ := by
  have e₃' : m.block m.zero (some W.b :: some W.a :: List.replicate (K - 2) none) = some W.vxy := by
    rw [L.perm _ (List.Perm.swap _ _ _)]; exact W.e₃
  have hz : ∀ (u v : α) i, i ≠ x → i ≠ y → pairInput L.z x y u v i = L.z := by
    intro u v i h1 h2; simp [pairInput, h1, h2]
  have V := fun ρ hρ nρ hx hy => runChain_pairInput L hK hxy W.a W.b W.vx W.vy W.vxy W.vlt W.vgt
    W.e₁ W.e₂ W.e₃ W.e₄ W.e₅ W.g₁ W.g₂ W.g₃ W.g₄ W.g₅ ρ hρ nρ hx hy
  have U := fun ρ hρ nρ hx hy => runChain_pairInput L hK hxy W.b W.a W.vy W.vx W.vxy W.vgt W.vlt
    W.e₂ W.e₁ e₃' W.e₅ W.e₄ W.g₂ W.g₁ W.g₃ W.g₅ W.g₄ ρ hρ nρ hx hy
  have mσ := pattern_mem hxy nσ hxσ hyσ
  have mτ := pattern_mem hxy nτ hxτ hyτ
  simp only [pairPats, List.mem_cons, List.mem_nil_iff, or_false] at mσ mτ
  have sep := W.sep
  by_cases hV : (if pattern x y σ = [.both] then W.vxy else if pattern x y σ = [.fst, .snd] then W.vlt
      else W.vgt) ≠
      (if pattern x y τ = [.both] then W.vxy else if pattern x y τ = [.fst, .snd] then W.vlt
      else W.vgt)
  · refine ⟨pairInput L.z x y W.a W.b, hz _ _, ?_⟩
    rw [V σ hσ nσ hxσ hyσ, V τ hτ nτ hxτ hyτ]
    intro h; exact hV (Option.some.inj h)
  · refine ⟨pairInput L.z x y W.b W.a, hz _ _, ?_⟩
    rw [U σ hσ nσ hxσ hyσ, U τ hτ nτ hxτ hyτ]
    intro h
    have h' := Option.some.inj h
    apply hV
    rcases mσ with h1 | h1 | h1 <;> rcases mτ with h2 | h2 | h2 <;>
      simp only [h1, h2] at h' hne ⊢ <;> simp_all

/-- **Completeness for chains.** On a rigid machine with base witnesses for two products, two
chains over the same products, each product once, with different ordered partitions, differ on an
input that is `z` outside two of the products. -/
theorem chain_complete {m : Machine α β} {K : ℕ} (L : RigidLaws m K) (hK : 2 ≤ K)
    (W : PairWitness L) (σ τ : Chain) (hσ : ∀ B ∈ σ, B.length = K) (hτ : ∀ B ∈ τ, B.length = K)
    (nσ : σ.leaves.Nodup) (nτ : τ.leaves.Nodup) (hl : ∀ i, i ∈ σ.leaves ↔ i ∈ τ.leaves)
    (hne : σ.nf ≠ τ.nf) :
    ∃ (x y : ℕ) (p : ℕ → α), x ≠ y ∧ (∀ i, i ≠ x → i ≠ y → p i = L.z) ∧
      runChain m p m.zero σ ≠ runChain m p m.zero τ := by
  obtain ⟨x, y, hx, hy, hxy, hp⟩ := exists_pattern_ne nσ nτ hl hne
  obtain ⟨p, hz, hd⟩ := complete_pair L hK W σ τ hσ hτ nσ nτ hxy hx hy ((hl x).mp hx)
    ((hl y).mp hy) hp
  exact ⟨x, y, p, hxy, hz, hd⟩

/-! ## Soundness -/

theorem count_none_blockLeaves (B : List (Option ℕ)) :
    B.count none + (blockLeaves B).length = B.length := by
  unfold blockLeaves
  induction B with
  | nil => rfl
  | cons o B ih => cases o <;> simp at ih ⊢ <;> omega

/-- Blocks of the same length whose products are a permutation of each other are permutations of
each other. -/
theorem perm_of_blockLeaves {B C : List (Option ℕ)} (hlen : B.length = C.length)
    (h : (blockLeaves B).Perm (blockLeaves C)) : B.Perm C := by
  rw [List.perm_iff_count]
  intro o
  cases o with
  | none =>
    have h1 := count_none_blockLeaves B
    have h2 := count_none_blockLeaves C
    have := h.length_eq
    omega
  | some i => rw [count_blockLeaves, count_blockLeaves]; exact List.perm_iff_count.mp h i

theorem eq_replicate_of_blockLeaves {B : List (Option ℕ)} (h : blockLeaves B = []) :
    B = List.replicate B.length none := by
  apply List.eq_replicate_iff.mpr
  refine ⟨rfl, ?_⟩
  intro o ho
  cases o with
  | none => rfl
  | some i =>
    have := mem_blockLeaves.mpr ho
    rw [h] at this; simp at this

/-- A block without products passes a good accumulator through. -/
theorem runChain_empty {m : Machine α β} {K : ℕ} (L : RigidLaws m K) (p : ℕ → α) {B : List (Option ℕ)}
    (hB : blockLeaves B = []) (hlen : B.length = K) (σ : Chain) {d : β} (hd : L.good d) :
    runChain m p d (B :: σ) = runChain m p d σ := by
  have e := eq_replicate_of_blockLeaves hB
  rw [hlen] at e
  simp only [runChain]
  rw [e]
  simp only [List.map_replicate, Option.map_none]
  rw [L.pass d hd]; rfl

/-- **Soundness for chains.** If every block output is good, two chains with blocks of `K` slots and
the same ordered partition give the same output on every input, from any good accumulator. -/
theorem chain_sound {m : Machine α β} {K : ℕ} (L : RigidLaws m K)
    (hgood : ∀ d ps o, m.block d ps = some o → L.good o) (p : ℕ → α) :
    ∀ (n : ℕ) (σ τ : Chain) (d : β), σ.length + τ.length ≤ n → L.good d →
      (∀ B ∈ σ, B.length = K) → (∀ B ∈ τ, B.length = K) → σ.nf = τ.nf →
      runChain m p d σ = runChain m p d τ
  | 0, σ, τ, d, hn, _, _, _, _ => by
    have h1 : σ = [] := List.length_eq_zero_iff.mp (by omega)
    have h2 : τ = [] := List.length_eq_zero_iff.mp (by omega)
    subst h1; subst h2; rfl
  | n + 1, σ, τ, d, hn, hd, hσ, hτ, hnf => by
    -- drop a leading empty block on either side
    cases σ with
    | cons B σ' =>
      by_cases hB : blockLeaves B = []
      · rw [runChain_empty L p hB (hσ B (by simp)) σ' hd]
        rw [nf_cons, if_pos hB] at hnf
        exact chain_sound L hgood p n σ' τ d (by simp at hn; omega) hd
          (fun B' h' => hσ B' (by simp [h'])) hτ hnf
      · cases τ with
        | cons C τ' =>
          by_cases hC : blockLeaves C = []
          · rw [runChain_empty L p hC (hτ C (by simp)) τ' hd]
            rw [nf_cons C, if_pos hC] at hnf
            exact chain_sound L hgood p n (B :: σ') τ' d (by simp at hn ⊢; omega) hd hσ
              (fun C' h' => hτ C' (by simp [h'])) hnf
          · rw [nf_cons, nf_cons C, if_neg hB, if_neg hC] at hnf
            obtain ⟨hs, hrest⟩ := List.cons.inj hnf
            have hp : (blockLeaves B).Perm (blockLeaves C) := by
              have h1 := List.mergeSort_perm (blockLeaves B) (fun a b => decide (a ≤ b))
              have h2 := List.mergeSort_perm (blockLeaves C) (fun a b => decide (a ≤ b))
              rw [hs] at h1
              exact h1.symm.trans h2
            have hBC := perm_of_blockLeaves (by rw [hσ B (by simp), hτ C (by simp)]) hp
            simp only [runChain]
            rw [L.perm d (hBC.map (Option.map p))]
            cases ho : m.block d (C.map (Option.map p)) with
            | none => rfl
            | some o =>
              exact chain_sound L hgood p n σ' τ' o (by simp at hn; omega) (hgood _ _ _ ho)
                (fun B' h' => hσ B' (by simp [h'])) (fun C' h' => hτ C' (by simp [h'])) hrest
        | nil =>
          rw [nf_cons, if_neg hB] at hnf
          exact absurd hnf (by simp [Chain.nf])
    | nil =>
      cases τ with
      | nil => rfl
      | cons C τ' =>
        by_cases hC : blockLeaves C = []
        · rw [runChain_empty L p hC (hτ C (by simp)) τ' hd]
          rw [nf_cons C, if_pos hC] at hnf
          exact chain_sound L hgood p n [] τ' d (by simp at hn ⊢; omega) hd hσ
            (fun C' h' => hτ C' (by simp [h'])) hnf
        · rw [nf_cons C, if_neg hC] at hnf
          exact absurd hnf (by simp [Chain.nf])

/-- **Chains are equivalent exactly when their ordered partitions agree.** On a rigid machine whose
block outputs are all good, with base witnesses for two products: two chains from the zero
accumulator over the same products, each product once, with blocks of `K` slots, give the same
output on every input if and only if they have the same ordered partition. -/
theorem chain_equiv_iff {m : Machine α β} {K : ℕ} (L : RigidLaws m K) (hK : 2 ≤ K)
    (W : PairWitness L) (hgood : ∀ d ps o, m.block d ps = some o → L.good o)
    (σ τ : Chain) (hσ : ∀ B ∈ σ, B.length = K) (hτ : ∀ B ∈ τ, B.length = K)
    (nσ : σ.leaves.Nodup) (nτ : τ.leaves.Nodup) (hl : ∀ i, i ∈ σ.leaves ↔ i ∈ τ.leaves) :
    (∀ p : ℕ → α, runChain m p m.zero σ = runChain m p m.zero τ) ↔ σ.nf = τ.nf := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro hne
    obtain ⟨_, _, p, _, _, hd⟩ := chain_complete L hK W σ τ hσ hτ nσ nτ hl hne
    exact hd (h p)
  · intro h p
    exact chain_sound L hgood p _ σ τ m.zero (Nat.le_refl _) L.zero_good hσ hτ h

end MMAlgebra
