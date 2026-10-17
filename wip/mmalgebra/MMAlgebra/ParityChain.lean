import MMAlgebra.ChainComplete

/-! # Completeness for chains on parity-pair matrix multipliers

A block of a parity-pair machine (CDNA 3 binary8: odd/even grouping) depends on its slots only
through the unordered pair {multiset of the slots at odd positions, multiset of the slots at even
positions} (the parity law, `ParityLaws.grp`). The normal form of a chain is then its ordered
partition with, in every block, the split of the block's products into the two parity groups, up
to exchanging the groups. For two products `x` and `y` this is one of four patterns
(`ppattern`): together in one group, in one block but different groups, `x` before `y`, or `y`
before `x`; and two chains have the same normal form exactly when every pair of products has the
same pattern in both.

`chain_complete_parity`: on a machine with the laws of `ParityLaws` and base witnesses
(`ParityWitness`: two products whose four patterns give four different words), two chains over the
same products, each once, that differ in the pattern of some pair differ on an input supported on
that pair. In particular, chains with different ordered partitions differ (`ppattern_ne_of_nf`).
Hardware-independent. -/

local notation "ℕ" => Nat

namespace MMAlgebra.Parity

open MMAlgebra

variable {α β γ : Type}

/-! ## Odd and even positions -/

/-- The slots at odd positions `1, 3, …` (1-based). -/
def oddSlots : List γ → List γ
  | [] => []
  | [x] => [x]
  | x :: _ :: xs => x :: oddSlots xs

/-- The slots at even positions `2, 4, …` (1-based). -/
def evenSlots : List γ → List γ
  | [] => []
  | [_] => []
  | _ :: y :: xs => y :: evenSlots xs

theorem perm_odd_even : ∀ l : List γ, l.Perm (oddSlots l ++ evenSlots l)
  | [] => by simp [oddSlots, evenSlots]
  | [x] => by simp [oddSlots, evenSlots]
  | x :: y :: xs => by
    have ih := perm_odd_even xs
    simp only [oddSlots, evenSlots, List.cons_append]
    exact List.Perm.cons x ((ih.cons y).trans List.perm_middle.symm)

theorem oddSlots_map (f : γ → β) : ∀ l : List γ, oddSlots (l.map f) = (oddSlots l).map f
  | [] => rfl
  | [_] => rfl
  | x :: y :: xs => by simp [oddSlots, oddSlots_map f xs]

theorem evenSlots_map (f : γ → β) : ∀ l : List γ, evenSlots (l.map f) = (evenSlots l).map f
  | [] => rfl
  | [_] => rfl
  | x :: y :: xs => by simp [evenSlots, evenSlots_map f xs]

theorem oddSlots_sublist : ∀ l : List γ, (oddSlots l).Sublist l
  | [] => List.Sublist.slnil
  | [_] => List.Sublist.refl _
  | x :: y :: xs => ((oddSlots_sublist xs).cons y).cons_cons x

theorem evenSlots_sublist : ∀ l : List γ, (evenSlots l).Sublist l
  | [] => List.Sublist.slnil
  | [_] => List.Sublist.slnil.cons _
  | x :: y :: xs => ((evenSlots_sublist xs).cons_cons y).cons x

theorem length_oddSlots : ∀ l : List γ, (oddSlots l).length = (l.length + 1) / 2
  | [] => by simp [oddSlots]
  | [_] => by simp [oddSlots]
  | x :: y :: xs => by simp [oddSlots, length_oddSlots xs]; omega

theorem length_evenSlots : ∀ l : List γ, (evenSlots l).length = l.length / 2
  | [] => by simp [evenSlots]
  | [_] => by simp [evenSlots]
  | x :: y :: xs => by simp [evenSlots, length_evenSlots xs]; omega

/-- Two slot lists with the same unordered pair {odd multiset, even multiset}. -/
def ParityEquiv (l m : List γ) : Prop :=
  ((oddSlots l).Perm (oddSlots m) ∧ (evenSlots l).Perm (evenSlots m)) ∨
  ((oddSlots l).Perm (evenSlots m) ∧ (evenSlots l).Perm (oddSlots m))

/-! ## Laws -/

/-- The laws of a parity-pair matrix multiplier with FMA size `K`: an empty slot reads as the operand
pair `z`; a block depends on its slots only through {odd multiset, even multiset}; an empty block
passes a good accumulator through; the zero accumulator is good. -/
structure ParityLaws (m : Machine α β) (K : ℕ) where
  z : α
  good : β → Prop
  slot : SlotZero m z
  grp : ∀ d {ps qs : List (Option α)}, ParityEquiv ps qs → m.block d ps = m.block d qs
  zero_good : good m.zero
  pass : ∀ d, good d → m.block d (List.replicate K none) = some d

/-! ## Patterns with parity -/

/-- What a block holds of `x` and `y`: nothing, one of them, both in one parity group, or both in
different groups. -/
inductive PKind | none | fst | snd | same | diff
  deriving DecidableEq, Repr

def PKind.erase : PKind → PairKind
  | .none => .none
  | .fst => .fst
  | .snd => .snd
  | .same => .both
  | .diff => .both

/-- Whether `x` sits at an odd position of the block. -/
def inOdd (x : ℕ) (B : List (Option ℕ)) : Bool := decide (some x ∈ oddSlots B)

def pkind (x y : ℕ) (B : List (Option ℕ)) : PKind :=
  if some x ∈ B then
    (if some y ∈ B then (if inOdd x B = inOdd y B then .same else .diff) else .fst)
  else (if some y ∈ B then .snd else .none)

/-- The pattern of `x` and `y` with parity: the parity kinds of the blocks that hold either. -/
def ppattern (x y : ℕ) (σ : Chain) : List PKind :=
  (σ.map (pkind x y)).filter fun k => decide (k ≠ .none)

theorem pkind_erase (x y : ℕ) (B : List (Option ℕ)) : (pkind x y B).erase = pairKind x y B := by
  unfold pkind pairKind
  by_cases hx : some x ∈ B <;> by_cases hy : some y ∈ B <;>
    by_cases hp : inOdd x B = inOdd y B <;> simp [hx, hy, hp, PKind.erase]

theorem pkind_none_iff (x y : ℕ) (B : List (Option ℕ)) :
    pkind x y B = .none ↔ pairKind x y B = .none := by
  unfold pkind pairKind
  by_cases hx : some x ∈ B <;> by_cases hy : some y ∈ B <;>
    by_cases hp : inOdd x B = inOdd y B <;> simp [hx, hy, hp]

theorem ppattern_cons (x y : ℕ) (B : List (Option ℕ)) (σ : Chain) :
    ppattern x y (B :: σ) =
      if pkind x y B = .none then ppattern x y σ else pkind x y B :: ppattern x y σ := by
  unfold ppattern
  simp only [List.map_cons, List.filter_cons]
  by_cases h : pkind x y B = .none <;> simp [h]

/-- Erasing the parity gives the pattern. -/
theorem ppattern_erase (x y : ℕ) : ∀ σ : Chain, (ppattern x y σ).map PKind.erase = pattern x y σ
  | [] => rfl
  | B :: σ => by
    rw [ppattern_cons, pattern_cons]
    by_cases h : pkind x y B = .none
    · rw [if_pos h, if_pos ((pkind_none_iff x y B).mp h)]; exact ppattern_erase x y σ
    · rw [if_neg h, if_neg (fun h' => h ((pkind_none_iff x y B).mpr h'))]
      simp only [List.map_cons, pkind_erase, ppattern_erase x y σ]

/-- The four ways a chain can hold two products, each once. -/
def ppats : List (List PKind) := [[.same], [.diff], [.fst, .snd], [.snd, .fst]]

theorem ppattern_mem {x y : ℕ} (hxy : x ≠ y) {σ : Chain} (hn : σ.leaves.Nodup) (hx : x ∈ σ.leaves)
    (hy : y ∈ σ.leaves) : ppattern x y σ ∈ ppats := by
  have hm := pattern_mem hxy hn hx hy
  have he := ppattern_erase x y σ
  generalize ppattern x y σ = P at he
  simp only [pairPats, List.mem_cons, List.mem_nil_iff, or_false] at hm
  simp only [ppats, List.mem_cons, List.mem_nil_iff, or_false]
  rcases hm with h | h | h <;> rw [h] at he
  · rcases P with _ | ⟨k, _ | ⟨k', P⟩⟩ <;> simp at he
    cases k <;> simp_all [PKind.erase]
  · rcases P with _ | ⟨k, _ | ⟨k', _ | ⟨k'', P⟩⟩⟩ <;> simp at he
    cases k <;> cases k' <;> simp_all [PKind.erase]
  · rcases P with _ | ⟨k, _ | ⟨k', _ | ⟨k'', P⟩⟩⟩ <;> simp at he
    cases k <;> cases k' <;> simp_all [PKind.erase]

/-- Chains with different ordered partitions differ in the parity pattern of some pair. -/
theorem ppattern_ne_of_nf {σ τ : Chain} (n₁ : σ.leaves.Nodup) (n₂ : τ.leaves.Nodup)
    (hl : ∀ i, i ∈ σ.leaves ↔ i ∈ τ.leaves) (hne : σ.nf ≠ τ.nf) :
    ∃ x y, x ∈ σ.leaves ∧ y ∈ σ.leaves ∧ x ≠ y ∧ ppattern x y σ ≠ ppattern x y τ := by
  obtain ⟨x, y, hx, hy, hxy, hp⟩ := exists_pattern_ne n₁ n₂ hl hne
  refine ⟨x, y, hx, hy, hxy, fun h => hp ?_⟩
  rw [← ppattern_erase, ← ppattern_erase, h]

/-! ## A block restricted to two products -/

/-- The canonical block of a kind: `x` at position 1, `y` at position 3 (same group) or 2
(different groups), then empty slots. -/
def canonP (K x y : ℕ) : PKind → List (Option ℕ)
  | .none => List.replicate K none
  | .fst => some x :: List.replicate (K - 1) none
  | .snd => some y :: List.replicate (K - 1) none
  | .same => some x :: none :: some y :: List.replicate (K - 3) none
  | .diff => some x :: some y :: List.replicate (K - 2) none

theorem count_some_replicate_none (i n : ℕ) {l : List (Option ℕ)}
    (h : l.Sublist (List.replicate n none)) : l.count (some i) = 0 := by
  apply List.count_eq_zero.mpr
  intro hm
  have := h.subset hm
  simp [List.mem_replicate] at this

theorem canonP_length (K x y : ℕ) (hK : 3 ≤ K) (k : PKind) : (canonP K x y k).length = K := by
  cases k <;> simp [canonP] <;> omega

theorem canonP_mem (K x y : ℕ) (k : PKind) :
    ∀ o ∈ canonP K x y k, o = none ∨ o = some x ∨ o = some y := by
  intro o ho
  cases k <;> simp [canonP, List.mem_replicate] at ho <;> grind

/-- Two lists over `{none, some x, some y}` of the same length and the same counts of `x` and `y`
are permutations of each other. -/
theorem perm_of_counts {x y : ℕ} (hxy : x ≠ y) {l₁ l₂ : List (Option ℕ)}
    (h₁ : ∀ o ∈ l₁, o = none ∨ o = some x ∨ o = some y)
    (h₂ : ∀ o ∈ l₂, o = none ∨ o = some x ∨ o = some y) (hlen : l₁.length = l₂.length)
    (hx : l₁.count (some x) = l₂.count (some x)) (hy : l₁.count (some y) = l₂.count (some y)) :
    l₁.Perm l₂ := by
  have e₁ := length_eq_counts hxy l₁ h₁
  have e₂ := length_eq_counts hxy l₂ h₂
  rw [List.perm_iff_count]
  intro o
  cases o with
  | none => omega
  | some i =>
    by_cases hix : i = x
    · subst hix; exact hx
    · by_cases hiy : i = y
      · subst hiy; exact hy
      · rw [List.count_eq_zero.mpr (fun hm => by rcases h₁ _ hm with h | h | h <;> simp at h <;> omega),
          List.count_eq_zero.mpr (fun hm => by rcases h₂ _ hm with h | h | h <;> simp at h <;> omega)]

theorem mem_xy_sub {x y : ℕ} {l m : List (Option ℕ)} (hs : l.Sublist m)
    (h : ∀ o ∈ m, o = none ∨ o = some x ∨ o = some y) : ∀ o ∈ l, o = none ∨ o = some x ∨ o = some y :=
  fun o ho => h o (hs.subset ho)

/-- **A block restricted to `{x, y}` has the same unordered pair of parity groups as the canonical
block of its kind** (blocks of even length `K ≥ 4`, each product at most once). -/
theorem restrict_parityEquiv_canon {x y : ℕ} (hxy : x ≠ y) (K : ℕ) (hK : 4 ≤ K) (hev : K % 2 = 0)
    (B : List (Option ℕ)) (hlen : B.length = K) (hx1 : B.count (some x) ≤ 1)
    (hy1 : B.count (some y) ≤ 1) :
    ParityEquiv (B.map (·.filter (pairSet x y))) (canonP K x y (pkind x y B)) := by
  generalize hR : B.map (·.filter (pairSet x y)) = R
  generalize hC : canonP K x y (pkind x y B) = C
  have hRm : ∀ o ∈ R, o = none ∨ o = some x ∨ o = some y := by
    rw [← hR]
    intro o ho
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp ho
    cases b with
    | none => simp
    | some j =>
      by_cases hj : pairSet x y j = true
      · have : j = x ∨ j = y := by simpa [pairSet] using hj
        rcases this with rfl | rfl <;> simp [Option.filter, hj]
      · simp [Option.filter, hj]
  have hCm : ∀ o ∈ C, o = none ∨ o = some x ∨ o = some y := by rw [← hC]; exact canonP_mem K x y _
  have hRl : R.length = K := by rw [← hR]; simp [hlen]
  have hCl : C.length = K := by rw [← hC]; exact canonP_length K x y (by omega) _
  -- counts in the halves of R are those of B
  have hoR : ∀ i, (i = x ∨ i = y) → (oddSlots R).count (some i) = (oddSlots B).count (some i) := by
    intro i hi
    rw [← hR, oddSlots_map, count_map_filter]
    rcases hi with rfl | rfl <;> simp [pairSet]
  have heR : ∀ i, (i = x ∨ i = y) → (evenSlots R).count (some i) = (evenSlots B).count (some i) := by
    intro i hi
    rw [← hR, evenSlots_map, count_map_filter]
    rcases hi with rfl | rfl <;> simp [pairSet]
  have hsplit : ∀ i, B.count (some i) = (oddSlots B).count (some i) + (evenSlots B).count (some i) := by
    intro i
    rw [(perm_odd_even B).count_eq, List.count_append]
  have hmemB : ∀ i, (some i ∈ B ↔ 1 ≤ B.count (some i)) := fun i => by
    rw [← List.count_pos_iff]; omega
  have hodd : ∀ i, (inOdd i B = true ↔ 1 ≤ (oddSlots B).count (some i)) := fun i => by
    unfold inOdd; rw [decide_eq_true_iff, ← List.count_pos_iff]; omega
  -- lengths of the halves
  have lo : (oddSlots R).length = K / 2 := by rw [length_oddSlots, hRl]; omega
  have le : (evenSlots R).length = K / 2 := by rw [length_evenSlots, hRl]
  have lo' : (oddSlots C).length = K / 2 := by rw [length_oddSlots, hCl]; omega
  have le' : (evenSlots C).length = K / 2 := by rw [length_evenSlots, hCl]
  have mRo := mem_xy_sub (oddSlots_sublist R) hRm
  have mRe := mem_xy_sub (evenSlots_sublist R) hRm
  have mCo := mem_xy_sub (oddSlots_sublist C) hCm
  have mCe := mem_xy_sub (evenSlots_sublist C) hCm
  -- the counts of the canonical block
  have cC : (oddSlots C).count (some x) = (if pkind x y B = .none ∨ pkind x y B = .snd then 0 else 1) ∧
      (oddSlots C).count (some y) =
        (if pkind x y B = .snd ∨ pkind x y B = .same then 1 else 0) ∧
      (evenSlots C).count (some x) = 0 ∧
      (evenSlots C).count (some y) = (if pkind x y B = .diff then 1 else 0) := by
    rw [← hC]
    have z1 : ∀ (i n : ℕ), (oddSlots (List.replicate n (none : Option ℕ))).count (some i) = 0 :=
      fun i n => count_some_replicate_none i n (oddSlots_sublist _)
    have z2 : ∀ (i n : ℕ), (evenSlots (List.replicate n (none : Option ℕ))).count (some i) = 0 :=
      fun i n => count_some_replicate_none i n (evenSlots_sublist _)
    have hK1 : K - 1 = (K - 2) + 1 := by omega
    have hK3 : K - 3 = (K - 4) + 1 := by omega
    cases hk : pkind x y B
    · simp only [canonP, reduceCtorEq, or_self, if_false]
      exact ⟨z1 _ _, z1 _ _, z2 _ _, z2 _ _⟩
    · simp only [canonP, reduceCtorEq, or_self, if_false]
      rw [hK1, List.replicate_succ]
      simp only [oddSlots, evenSlots, List.count_cons, z1, z2]
      simp [hxy]
    · simp only [canonP, reduceCtorEq, or_false, or_true, if_true, if_false]
      rw [hK1, List.replicate_succ]
      simp only [oddSlots, evenSlots, List.count_cons, z1, z2]
      simp [Ne.symm hxy]
    · simp only [canonP, reduceCtorEq, or_false, or_true, if_true, if_false]
      rw [hK3, List.replicate_succ]
      simp only [oddSlots, evenSlots, List.count_cons, z1, z2]
      simp [hxy, Ne.symm hxy]
    · simp only [canonP, reduceCtorEq, or_self, if_true, if_false]
      simp only [oddSlots, evenSlots, List.count_cons, z1, z2]
      simp [hxy, Ne.symm hxy]
  obtain ⟨c1, c2, c3, c4⟩ := cC
  have rx := hoR x (Or.inl rfl)
  have ry := hoR y (Or.inr rfl)
  have sx := heR x (Or.inl rfl)
  have sy := heR y (Or.inr rfl)
  have bx := hsplit x
  have byy := hsplit y
  have mx := hmemB x
  have my := hmemB y
  have ox := hodd x
  have oy := hodd y
  -- the nine possible placements, in counts
  have kx : (some x ∈ B) ↔ (oddSlots B).count (some x) + (evenSlots B).count (some x) = 1 := by
    rw [mx, bx]; omega
  have ky : (some y ∈ B) ↔ (oddSlots B).count (some y) + (evenSlots B).count (some y) = 1 := by
    rw [my, byy]; omega
  have px : inOdd x B = decide ((oddSlots B).count (some x) = 1) := by
    apply Bool.eq_iff_iff.mpr; rw [ox]; simp only [decide_eq_true_eq]; omega
  have py : inOdd y B = decide ((oddSlots B).count (some y) = 1) := by
    apply Bool.eq_iff_iff.mpr; rw [oy]; simp only [decide_eq_true_eq]; omega
  have hk : pkind x y B =
      (if (oddSlots B).count (some x) + (evenSlots B).count (some x) = 1 then
        (if (oddSlots B).count (some y) + (evenSlots B).count (some y) = 1 then
          (if decide ((oddSlots B).count (some x) = 1) = decide ((oddSlots B).count (some y) = 1)
            then .same else .diff) else .fst)
      else (if (oddSlots B).count (some y) + (evenSlots B).count (some y) = 1 then .snd else .none)) := by
    unfold pkind
    rw [px, py]
    simp only [kx, ky]
  rw [hk] at c1 c2 c4
  clear ox oy px py hk kx ky hodd hmemB mx my
  generalize (oddSlots B).count (some x) = cox at *
  generalize (evenSlots B).count (some x) = cex at *
  generalize (oddSlots B).count (some y) = coy at *
  generalize (evenSlots B).count (some y) = cey at *
  unfold ParityEquiv
  rcases (show (cox = 0 ∧ cex = 0) ∨ (cox = 1 ∧ cex = 0) ∨ (cox = 0 ∧ cex = 1) by omega) with
    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
  rcases (show (coy = 0 ∧ cey = 0) ∨ (coy = 1 ∧ cey = 0) ∨ (coy = 0 ∧ cey = 1) by omega) with
    ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
  subst h1 h2 h3 h4 <;>
  simp at c1 c2 c4 <;>
  first
    | exact Or.inl ⟨perm_of_counts hxy mRo mCo (by omega) (by omega) (by omega),
        perm_of_counts hxy mRe mCe (by omega) (by omega) (by omega)⟩
    | exact Or.inr ⟨perm_of_counts hxy mRo mCe (by omega) (by omega) (by omega),
        perm_of_counts hxy mRe mCo (by omega) (by omega) (by omega)⟩

theorem ParityEquiv.map (f : γ → β) {l m : List γ} (h : ParityEquiv l m) :
    ParityEquiv (l.map f) (m.map f) := by
  unfold ParityEquiv
  simp only [oddSlots_map, evenSlots_map]
  rcases h with ⟨ho, he⟩ | ⟨ho, he⟩
  · exact Or.inl ⟨ho.map f, he.map f⟩
  · exact Or.inr ⟨ho.map f, he.map f⟩

/-! ## Running a chain on two products -/

/-- Run the canonical blocks of a list of parity kinds. -/
def runPatP (m : Machine α β) (p : ℕ → α) (K x y : ℕ) : β → List PKind → Option β
  | d, [] => some d
  | d, k :: ks => (m.block d ((canonP K x y k).map (Option.map p))).bind fun d' => runPatP m p K x y d' ks

/-- On the support `{x, y}`, a chain runs its parity pattern of canonical blocks, provided every
value the pattern passes through is good. -/
theorem runChain_pairP {m : Machine α β} {K : ℕ} (L : ParityLaws m K) (hK : 4 ≤ K) (hev : K % 2 = 0)
    {x y : ℕ} (hxy : x ≠ y) (p : ℕ → α) :
    ∀ (σ : Chain) (d : β),
      (∀ B ∈ σ, B.length = K ∧ B.count (some x) ≤ 1 ∧ B.count (some y) ≤ 1) →
      (∀ ks₁ ks₂ v, ppattern x y σ = ks₁ ++ ks₂ → runPatP m p K x y d ks₁ = some v → L.good v) →
      runChain m p d (σ.restrict (pairSet x y)) = runPatP m p K x y d (ppattern x y σ)
  | [], _, _, _ => rfl
  | B :: σ, d, hwf, hgood => by
    have hB := hwf B (by simp)
    have hge := restrict_parityEquiv_canon hxy K hK hev B hB.1 hB.2.1 hB.2.2
    have hblk := L.grp d (hge.map (Option.map p))
    have hwf' : ∀ B' ∈ σ, B'.length = K ∧ B'.count (some x) ≤ 1 ∧ B'.count (some y) ≤ 1 :=
      fun B' h' => hwf B' (by simp [h'])
    simp only [Chain.restrict, List.map_cons, runChain] at hblk ⊢
    rw [List.map_map] at hblk
    rw [List.map_map, hblk]
    rw [ppattern_cons] at hgood ⊢
    by_cases hk : pkind x y B = .none
    · rw [if_pos hk] at hgood ⊢
      have hd : L.good d := hgood [] (ppattern x y σ) d (by simp) rfl
      rw [hk]
      simp only [canonP, List.map_replicate, Option.map_none]
      rw [L.pass d hd]
      exact runChain_pairP L hK hev hxy p σ d hwf' hgood
    · rw [if_neg hk] at hgood ⊢
      simp only [runPatP]
      cases hb : m.block d ((canonP K x y (pkind x y B)).map (Option.map p)) with
      | none => rfl
      | some d' =>
        simp only [Option.bind_some]
        refine runChain_pairP L hK hev hxy p σ d' hwf' ?_
        intro ks₁ ks₂ v he hv
        exact hgood (pkind x y B :: ks₁) ks₂ v (by rw [he]; rfl)
          (by simp only [runPatP, hb, Option.bind_some]; exact hv)

/-! ## Base witnesses and completeness -/

/-- Base witnesses for two products on a parity-pair machine: operand pairs `a` and `b` and the six
block evaluations of the four patterns (`[a b]` in one group, `[a | b]` in different groups,
`[a] [b]`, `[b] [a]`), with good values; the two one-block patterns differ, and so do the two
two-block patterns. -/
structure ParityWitness {m : Machine α β} {K : ℕ} (L : ParityLaws m K) where
  a : α
  b : α
  vx : β
  vy : β
  vs : β
  vd : β
  vlt : β
  vgt : β
  e₁ : m.block m.zero (some a :: List.replicate (K - 1) none) = some vx
  e₂ : m.block m.zero (some b :: List.replicate (K - 1) none) = some vy
  e₃ : m.block m.zero (some a :: none :: some b :: List.replicate (K - 3) none) = some vs
  e₄ : m.block m.zero (some a :: some b :: List.replicate (K - 2) none) = some vd
  e₅ : m.block vx (some b :: List.replicate (K - 1) none) = some vlt
  e₆ : m.block vy (some a :: List.replicate (K - 1) none) = some vgt
  g₁ : L.good vx
  g₂ : L.good vy
  g₃ : L.good vs
  g₄ : L.good vd
  g₅ : L.good vlt
  g₆ : L.good vgt
  sep : vs ≠ vd ∧ vlt ≠ vgt

/-- The value of a chain on a two-product input is the value of its parity pattern. -/
theorem runChain_pairInputP {m : Machine α β} {K : ℕ} (L : ParityLaws m K) (hK : 4 ≤ K)
    (hev : K % 2 = 0) {x y : ℕ} (hxy : x ≠ y) (u v : α) (wx wy ws wd wl wg : β)
    (f₁ : m.block m.zero (some u :: List.replicate (K - 1) none) = some wx)
    (f₂ : m.block m.zero (some v :: List.replicate (K - 1) none) = some wy)
    (f₃ : m.block m.zero (some u :: none :: some v :: List.replicate (K - 3) none) = some ws)
    (f₄ : m.block m.zero (some u :: some v :: List.replicate (K - 2) none) = some wd)
    (f₅ : m.block wx (some v :: List.replicate (K - 1) none) = some wl)
    (f₆ : m.block wy (some u :: List.replicate (K - 1) none) = some wg)
    (k₁ : L.good wx) (k₂ : L.good wy) (k₃ : L.good ws) (k₄ : L.good wd) (k₅ : L.good wl)
    (k₆ : L.good wg)
    (σ : Chain) (hlen : ∀ B ∈ σ, B.length = K) (hn : σ.leaves.Nodup) (hx : x ∈ σ.leaves)
    (hy : y ∈ σ.leaves) :
    runChain m (pairInput L.z x y u v) m.zero σ =
      some (if ppattern x y σ = [.same] then ws else if ppattern x y σ = [.diff] then wd
        else if ppattern x y σ = [.fst, .snd] then wl else wg) := by
  have hpx : (canonP K x y .fst).map (Option.map (pairInput L.z x y u v)) =
      some u :: List.replicate (K - 1) none := by
    simp [canonP, pairInput, List.map_replicate]
  have hpy : (canonP K x y .snd).map (Option.map (pairInput L.z x y u v)) =
      some v :: List.replicate (K - 1) none := by
    simp [canonP, pairInput, List.map_replicate, Ne.symm hxy]
  have hps : (canonP K x y .same).map (Option.map (pairInput L.z x y u v)) =
      some u :: none :: some v :: List.replicate (K - 3) none := by
    simp [canonP, pairInput, List.map_replicate, Ne.symm hxy]
  have hpd : (canonP K x y .diff).map (Option.map (pairInput L.z x y u v)) =
      some u :: some v :: List.replicate (K - 2) none := by
    simp [canonP, pairInput, List.map_replicate, Ne.symm hxy]
  rw [← pairInput_mask, runChain_mask L.slot]
  have hmem := ppattern_mem hxy hn hx hy
  have hwf : ∀ B ∈ σ, B.length = K ∧ B.count (some x) ≤ 1 ∧ B.count (some y) ≤ 1 :=
    fun B hB => ⟨hlen B hB, count_le_one_of_nodup hn hB x, count_le_one_of_nodup hn hB y⟩
  simp only [ppats, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rw [runChain_pairP L hK hev hxy _ σ m.zero hwf]
  · rcases hmem with h | h | h | h <;> rw [h] <;>
      simp [runPatP, hpx, hpy, hps, hpd, f₁, f₂, f₃, f₄, f₅, f₆]
  · intro ks₁ ks₂ w he hw
    rcases hmem with h | h | h | h <;> rw [h] at he
    · rcases List.append_eq_singleton_iff.mp he.symm with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · simp only [runPatP, Option.some.injEq] at hw; subst hw; exact L.zero_good
      · simp only [runPatP, hps, f₃, Option.bind_some, Option.some.injEq] at hw; subst hw; exact k₃
    · rcases List.append_eq_singleton_iff.mp he.symm with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · simp only [runPatP, Option.some.injEq] at hw; subst hw; exact L.zero_good
      · simp only [runPatP, hpd, f₄, Option.bind_some, Option.some.injEq] at hw; subst hw; exact k₄
    · rcases ks₁ with _ | ⟨k, ks₁⟩
      · simp only [runPatP, Option.some.injEq] at hw; subst hw; exact L.zero_good
      · simp only [List.cons_append, List.cons.injEq] at he
        obtain ⟨rfl, he⟩ := he
        rcases List.append_eq_singleton_iff.mp he.symm with ⟨rfl, _⟩ | ⟨rfl, _⟩
        · simp only [runPatP, hpx, f₁, Option.bind_some, Option.some.injEq] at hw; subst hw; exact k₁
        · simp only [runPatP, hpx, hpy, f₁, f₅, Option.bind_some, Option.some.injEq] at hw
          subst hw; exact k₅
    · rcases ks₁ with _ | ⟨k, ks₁⟩
      · simp only [runPatP, Option.some.injEq] at hw; subst hw; exact L.zero_good
      · simp only [List.cons_append, List.cons.injEq] at he
        obtain ⟨rfl, he⟩ := he
        rcases List.append_eq_singleton_iff.mp he.symm with ⟨rfl, _⟩ | ⟨rfl, _⟩
        · simp only [runPatP, hpy, f₂, Option.bind_some, Option.some.injEq] at hw; subst hw; exact k₂
        · simp only [runPatP, hpx, hpy, f₂, f₆, Option.bind_some, Option.some.injEq] at hw
          subst hw; exact k₆

theorem oddSlots_replicate (c : γ) : ∀ n : ℕ, oddSlots (List.replicate n c) = List.replicate ((n + 1) / 2) c
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
    simp only [List.replicate_succ, oddSlots, oddSlots_replicate c n]
    rw [show (n + 2 + 1) / 2 = (n + 1) / 2 + 1 by omega, List.replicate_succ]

theorem evenSlots_replicate (c : γ) : ∀ n : ℕ, evenSlots (List.replicate n c) = List.replicate (n / 2) c
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
    simp only [List.replicate_succ, evenSlots, evenSlots_replicate c n]
    rw [show (n + 2) / 2 = n / 2 + 1 by omega, List.replicate_succ]

/-- The slot list with `a` and `b` in one parity group is parity-equivalent to the one with `b` and
`a`, and likewise in different groups. -/
theorem parityEquiv_swap_same (K : ℕ) (a b : Option γ) :
    ParityEquiv (a :: none :: b :: List.replicate (K - 3) none) (b :: none :: a :: List.replicate (K - 3) none) := by
  left
  generalize K - 3 = n
  cases n with
  | zero => exact ⟨List.Perm.swap b a [], List.Perm.refl _⟩
  | succ n =>
    simp only [List.replicate_succ, oddSlots, evenSlots]
    exact ⟨List.Perm.swap b a _, List.Perm.refl _⟩

theorem parityEquiv_swap_diff (K : ℕ) (hev : K % 2 = 0) (a b : Option γ) :
    ParityEquiv (a :: b :: List.replicate (K - 2) none) (b :: a :: List.replicate (K - 2) none) := by
  right
  simp only [oddSlots, evenSlots, oddSlots_replicate, evenSlots_replicate]
  rw [show (K - 2 + 1) / 2 = (K - 2) / 2 by omega]
  exact ⟨List.Perm.refl _, List.Perm.refl _⟩

/-- **Completeness for chains on a parity-pair machine.** Two chains over the same products, each
once, with blocks of `K` slots (`K ≥ 4` even), that differ in the parity pattern of some pair of
products (in particular, two chains with different ordered partitions, or with the same ordered
partition but a different split of some block into its parity groups), differ on an input that is
`z` outside that pair. -/
theorem chain_complete_parity {m : Machine α β} {K : ℕ} (L : ParityLaws m K) (hK : 4 ≤ K)
    (hev : K % 2 = 0) (W : ParityWitness L) (σ τ : Chain) (hσ : ∀ B ∈ σ, B.length = K)
    (hτ : ∀ B ∈ τ, B.length = K) (nσ : σ.leaves.Nodup) (nτ : τ.leaves.Nodup)
    (hl : ∀ i, i ∈ σ.leaves ↔ i ∈ τ.leaves)
    (hne : ∃ x y, x ∈ σ.leaves ∧ y ∈ σ.leaves ∧ x ≠ y ∧ ppattern x y σ ≠ ppattern x y τ) :
    ∃ (x y : ℕ) (p : ℕ → α), x ≠ y ∧ (∀ i, i ≠ x → i ≠ y → p i = L.z) ∧
      runChain m p m.zero σ ≠ runChain m p m.zero τ := by
  obtain ⟨x, y, hx, hy, hxy, hp⟩ := hne
  have hx' := (hl x).mp hx
  have hy' := (hl y).mp hy
  have e₃' : m.block m.zero (some W.b :: none :: some W.a :: List.replicate (K - 3) none) = some W.vs := by
    rw [← W.e₃]; exact L.grp _ (parityEquiv_swap_same K _ _)
  have e₄' : m.block m.zero (some W.b :: some W.a :: List.replicate (K - 2) none) = some W.vd := by
    rw [← W.e₄]; exact L.grp _ (parityEquiv_swap_diff K hev _ _)
  have hz : ∀ (u v : α) i, i ≠ x → i ≠ y → pairInput L.z x y u v i = L.z := by
    intro u v i h1 h2; simp [pairInput, h1, h2]
  have V := fun ρ hρ nρ hx hy => runChain_pairInputP L hK hev hxy W.a W.b W.vx W.vy W.vs W.vd
    W.vlt W.vgt W.e₁ W.e₂ W.e₃ W.e₄ W.e₅ W.e₆ W.g₁ W.g₂ W.g₃ W.g₄ W.g₅ W.g₆ ρ hρ nρ hx hy
  have U := fun ρ hρ nρ hx hy => runChain_pairInputP L hK hev hxy W.b W.a W.vy W.vx W.vs W.vd
    W.vgt W.vlt W.e₂ W.e₁ e₃' e₄' W.e₆ W.e₅ W.g₂ W.g₁ W.g₃ W.g₄ W.g₆ W.g₅ ρ hρ nρ hx hy
  have mσ := ppattern_mem hxy nσ hx hy
  have mτ := ppattern_mem hxy nτ hx' hy'
  simp only [ppats, List.mem_cons, List.mem_nil_iff, or_false] at mσ mτ
  obtain ⟨s1, s2⟩ := W.sep
  by_cases hV : (if ppattern x y σ = [.same] then W.vs else if ppattern x y σ = [.diff] then W.vd
        else if ppattern x y σ = [.fst, .snd] then W.vlt else W.vgt) ≠
      (if ppattern x y τ = [.same] then W.vs else if ppattern x y τ = [.diff] then W.vd
        else if ppattern x y τ = [.fst, .snd] then W.vlt else W.vgt)
  · refine ⟨x, y, pairInput L.z x y W.a W.b, hxy, hz _ _, ?_⟩
    rw [V σ hσ nσ hx hy, V τ hτ nτ hx' hy']
    intro h; exact hV (Option.some.inj h)
  · refine ⟨x, y, pairInput L.z x y W.b W.a, hxy, hz _ _, ?_⟩
    rw [U σ hσ nσ hx hy, U τ hτ nτ hx' hy']
    intro h
    have h' := Option.some.inj h
    apply hV
    rcases mσ with h1 | h1 | h1 | h1 <;> rcases mτ with h2 | h2 | h2 | h2 <;>
      simp only [h1, h2] at h' hp ⊢ <;> simp_all

/-- In particular, chains with different ordered partitions are separated. -/
theorem chain_complete_parity_nf {m : Machine α β} {K : ℕ} (L : ParityLaws m K) (hK : 4 ≤ K)
    (hev : K % 2 = 0) (W : ParityWitness L) (σ τ : Chain) (hσ : ∀ B ∈ σ, B.length = K)
    (hτ : ∀ B ∈ τ, B.length = K) (nσ : σ.leaves.Nodup) (nτ : τ.leaves.Nodup)
    (hl : ∀ i, i ∈ σ.leaves ↔ i ∈ τ.leaves) (hne : σ.nf ≠ τ.nf) :
    ∃ (x y : ℕ) (p : ℕ → α), x ≠ y ∧ (∀ i, i ≠ x → i ≠ y → p i = L.z) ∧
      runChain m p m.zero σ ≠ runChain m p m.zero τ :=
  chain_complete_parity L hK hev W σ τ hσ hτ nσ nτ hl (ppattern_ne_of_nf nσ nτ hl hne)

end MMAlgebra.Parity
