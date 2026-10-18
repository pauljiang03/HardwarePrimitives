import MatrixCore.MC.Order

/-! # CDNA 3 FP8: the parity law of a block

On CDNA 3, FP8 operands (E4M3 FNUZ and E5M2 FNUZ, in any combination) accumulate the products of
the odd slots and the products of the even slots separately, each group aligned to its own largest
exponent, before the two group sums are combined (`odd_even_grouping`). A block depends on its
operand pairs only through the unordered pair {multiset of the odd slots, multiset of the even
slots}, and a permutation of the 16 slots preserves the output on every input exactly when it
preserves the parity partition: `2·(8!)² = 3,251,404,800` of the `16!` orders. Slots are numbered
from 1, as in `oddIndexed`. -/

namespace MatrixCore

/-! ## Operand pairs -/

/-- Decode an operand pair. -/
def decPair (P : Model) (q : P.a.Word × P.b.Word) : Option (Unpacked × Unpacked) :=
  ((P.a.read q.1).toFinite).bind fun u => ((P.b.read q.2).toFinite).map fun v => (u, v)

theorem mapM_pairs {γ : Type} (P : Model) (k : List Unpacked → List Unpacked → Option γ) :
    ∀ qs : List (P.a.Word × P.b.Word),
      ((qs.map Prod.fst).mapM fun w => (P.a.read w).toFinite).bind (fun a =>
        ((qs.map Prod.snd).mapM fun w => (P.b.read w).toFinite).bind (k a)) =
      (qs.mapM (decPair P)).bind fun L => k (L.map Prod.fst) (L.map Prod.snd)
  | [] => rfl
  | q :: qs => by
    simp only [List.map_cons, List.mapM_cons, decPair]
    cases ha : (P.a.read q.1).toFinite with
    | none => simp
    | some u =>
      cases hb : (P.b.read q.2).toFinite with
      | none =>
        simp only [Option.bind_some, Option.map_none]
        cases (qs.map Prod.fst).mapM (fun w => (P.a.read w).toFinite) <;> simp
      | some v =>
        have ih := mapM_pairs P (fun as bs => k (u :: as) (v :: bs)) qs
        simp only [Option.bind_some, Option.map_some]
        simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_assoc, Option.bind_some] at ih ⊢
        simp only [List.map_cons]
        exact ih

/-- **Preparing a block of operand pairs.** -/
theorem prepare_pairs (P : Model) (qs : List (P.a.Word × P.b.Word)) (d : F32) :
    prepare (P := P) ⟨qs.map Prod.fst, qs.map Prod.snd, d⟩ =
      (qs.mapM (decPair P)).bind fun L =>
        ((fp32.decode d).toFinite).map fun C => ⟨L.map Prod.fst, L.map Prod.snd, C⟩ := by
  unfold prepare
  simp only [Option.bind_eq_bind, Option.pure_def]
  refine (mapM_pairs P (fun a b => ((fp32.decode d).toFinite).bind fun c =>
    some (Prepared.mk a b c)) qs).trans ?_
  cases qs.mapM (decPair P) with
  | none => rfl
  | some L => cases (fp32.decode d).toFinite <;> rfl

theorem products_pairs (L : List (Unpacked × Unpacked)) (C : Unpacked) :
    (Prepared.mk (L.map Prod.fst) (L.map Prod.snd) C).p = L.map fun q => q.1.mul q.2 := by
  unfold Prepared.p
  induction L with
  | nil => rfl
  | cons q L ih => simp [ih]

/-- Relation between two optional lists: both fail, or both succeed with permuted results. -/
def PermOptM {γ : Type} : Option (List γ) → Option (List γ) → Prop
  | none, none => True
  | some u, some v => u.Perm v
  | _, _ => False

theorem mapM_permM {γ δ : Type} (f : γ → Option δ) {xs ys : List γ} (h : xs.Perm ys) :
    PermOptM (xs.mapM f) (ys.mapM f) := by
  induction h with
  | nil => simp [PermOptM]
  | @cons x l₁ l₂ _ ih =>
    simp only [List.mapM_cons]
    revert ih
    generalize List.mapM f l₁ = o₁
    generalize List.mapM f l₂ = o₂
    intro ih
    cases hx : f x <;> cases o₁ <;> cases o₂ <;> simp_all [PermOptM]
  | swap x y l =>
    simp only [List.mapM_cons]
    generalize List.mapM f l = o
    cases hx : f x <;> cases hy : f y <;> cases o <;> simp [PermOptM]
    exact List.Perm.swap _ _ _
  | trans _ _ ih₁ ih₂ =>
    revert ih₁ ih₂
    generalize List.mapM f _ = o₁
    generalize List.mapM f _ = o₂
    generalize List.mapM f _ = o₃
    intro h₁ h₂
    cases o₁ <;> cases o₂ <;> cases o₃ <;> simp_all [PermOptM]
    exact h₁.trans h₂

/-- The output word of a block whose prepared operands accumulate to the same value. -/
theorem blockBits_congr {P : Model} {x y : BlockInput P} (hla : x.a.length = y.a.length)
    (hlb : x.b.length = y.b.length)
    (hprep : (prepare x = none ∧ prepare y = none) ∨
      ∃ px py, prepare x = some px ∧ prepare y = some py ∧ accumulate P px = accumulate P py) :
    blockBits x = blockBits y := by
  unfold blockBits evalBlock
  rw [hla, hlb]
  split
  · rfl
  · rcases hprep with ⟨h₁, h₂⟩ | ⟨px, py, h₁, h₂, he⟩
    · rw [h₁, h₂]
    · rw [h₁, h₂]; simp only; rw [he]
      split <;> try rfl
      split <;> rfl

variable {α β : Type}

/-! ## Odd and even slots -/

theorem perm_oddIndexed_append : ∀ l : List α, l.Perm (oddIndexed l ++ evenIndexed l)
  | [] => by simp [oddIndexed, evenIndexed]
  | [x] => by simp [oddIndexed, evenIndexed]
  | x :: y :: xs => by
    have ih := perm_oddIndexed_append xs
    simp only [oddIndexed, evenIndexed, List.cons_append]
    exact List.Perm.cons x ((ih.cons y).trans List.perm_middle.symm)

/-- Two slot lists with the same unordered pair {odd multiset, even multiset}. -/
def ParityEquiv (l m : List α) : Prop :=
  ((oddIndexed l).Perm (oddIndexed m) ∧ (evenIndexed l).Perm (evenIndexed m)) ∨
  ((oddIndexed l).Perm (evenIndexed m) ∧ (evenIndexed l).Perm (oddIndexed m))

instance (l m : List ℕ) : Decidable (ParityEquiv l m) := by unfold ParityEquiv; infer_instance

theorem ParityEquiv.perm {l m : List α} (h : ParityEquiv l m) : l.Perm m := by
  have hl := perm_oddIndexed_append l
  have hm := perm_oddIndexed_append m
  rcases h with ⟨ho, he⟩ | ⟨ho, he⟩
  · exact hl.trans ((ho.append he).trans hm.symm)
  · exact hl.trans ((ho.append he).trans (List.perm_append_comm.trans hm.symm))

theorem oddIndexed_map' (f : α → β) : ∀ l : List α,
    oddIndexed (l.map f) = (oddIndexed l).map f ∧ evenIndexed (l.map f) = (evenIndexed l).map f
  | [] => by simp [oddIndexed, evenIndexed]
  | [_] => by simp [oddIndexed, evenIndexed]
  | a :: b :: r => by
    obtain ⟨h1, h2⟩ := oddIndexed_map' f r
    simp [oddIndexed, evenIndexed, h1, h2]

theorem ParityEquiv.map (f : α → β) {l m : List α} (h : ParityEquiv l m) :
    ParityEquiv (l.map f) (m.map f) := by
  unfold ParityEquiv
  simp only [(oddIndexed_map' f l).1, (oddIndexed_map' f l).2,
    (oddIndexed_map' f m).1, (oddIndexed_map' f m).2]
  rcases h with ⟨ho, he⟩ | ⟨ho, he⟩
  · exact Or.inl ⟨ho.map f, he.map f⟩
  · exact Or.inr ⟨ho.map f, he.map f⟩

theorem mapM_oddIndexed (f : α → Option β) : ∀ (l : List α) (L : List β), l.mapM f = some L →
    (oddIndexed l).mapM f = some (oddIndexed L) ∧ (evenIndexed l).mapM f = some (evenIndexed L)
  | [], L, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; simp [oddIndexed, evenIndexed]
  | [x], L, h => by
    simp only [List.mapM_cons, List.mapM_nil] at h
    cases hx : f x with
    | none => simp [hx] at h
    | some a =>
      simp only [hx, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq] at h
      subst h; simp [oddIndexed, evenIndexed, hx]
  | x :: y :: xs, L, h => by
    simp only [List.mapM_cons] at h
    cases hx : f x with
    | none => simp [hx] at h
    | some a =>
      cases hy : f y with
      | none => simp [hx, hy] at h
      | some b =>
        cases hxs : xs.mapM f with
        | none => simp [hx, hy, hxs] at h
        | some L' =>
          simp only [hx, hy, hxs, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
            Option.some.injEq] at h
          subst h
          obtain ⟨h1, h2⟩ := mapM_oddIndexed f xs L' hxs
          simp only [oddIndexed, evenIndexed, List.mapM_cons, hx, hy, h1, h2, Option.bind_eq_bind,
            Option.bind_some, Option.pure_def, and_self]

/-- Decoding respects the parity classes: both decodings fail, or both succeed with lists in the
same relation. -/
theorem mapM_parityEquiv (f : α → Option β) {l m : List α} (h : ParityEquiv l m) :
    (l.mapM f = none ∧ m.mapM f = none) ∨
      ∃ L M, l.mapM f = some L ∧ m.mapM f = some M ∧ ParityEquiv L M := by
  have hp := mapM_permM f h.perm
  cases hl : l.mapM f with
  | none =>
    cases hm : m.mapM f with
    | none => exact Or.inl ⟨rfl, rfl⟩
    | some M => rw [hl, hm] at hp; exact hp.elim
  | some L =>
    cases hm : m.mapM f with
    | none => rw [hl, hm] at hp; exact hp.elim
    | some M =>
      refine Or.inr ⟨L, M, rfl, rfl, ?_⟩
      obtain ⟨lo, le⟩ := mapM_oddIndexed f l L hl
      obtain ⟨mo, me⟩ := mapM_oddIndexed f m M hm
      rcases h with ⟨ho, he⟩ | ⟨ho, he⟩
      · left
        have p1 := mapM_permM f ho
        have p2 := mapM_permM f he
        rw [lo, mo] at p1; rw [le, me] at p2
        exact ⟨p1, p2⟩
      · right
        have p1 := mapM_permM f ho
        have p2 := mapM_permM f he
        rw [lo, me] at p1; rw [le, mo] at p2
        exact ⟨p1, p2⟩

/-! ## The parity law -/

theorem productSum_parityEquiv {P : Model} (hP : P.accumulation = .oddEvenGrouping)
    {ps qs : List Unpacked} (h : ParityEquiv ps qs) : productSum P ps = productSum P qs := by
  unfold productSum
  rw [hP]
  simp only
  rcases h with ⟨ho, he⟩ | ⟨ho, he⟩
  · rw [alignedSum_perm _ ho, alignedSum_perm _ he]
  · rw [alignedSum_perm _ ho, alignedSum_perm _ he]
    generalize alignedSum P.padding (oddIndexed qs) = A
    generalize alignedSum P.padding (evenIndexed qs) = B
    obtain ⟨a1, a2⟩ := A
    obtain ⟨b1, b2⟩ := B
    cases a1 <;> cases b1 <;> simp [joinExp, Int.max_comm, Rat.add_comm]

theorem accumulate_parityEquiv {P : Model} (hP : P.accumulation = .oddEvenGrouping)
    {x y : Prepared} (h : ParityEquiv x.p y.p) (hc : x.c = y.c) :
    accumulate P x = accumulate P y := by
  unfold accumulate Prepared.productOverflows
  rw [any_perm h.perm]
  simp only [hP, alignedAccumulation, productSum_parityEquiv hP h, hc]

/-- **The parity law.** On a model with odd/even grouping (CDNA 3 FP8, any combination of
E4M3 and E5M2 FNUZ operands), two blocks whose operand pairs agree as an unordered pair
{multiset of the odd slots, multiset of the even slots} return the same word, or the same error,
for every accumulator input `d`. -/
theorem blockBits_parityEquiv {P : Model} (hP : P.accumulation = .oddEvenGrouping) (d : F32)
    {qs rs : List (P.a.Word × P.b.Word)} (h : ParityEquiv qs rs) :
    blockBits (P := P) ⟨qs.map Prod.fst, qs.map Prod.snd, d⟩ =
      blockBits (P := P) ⟨rs.map Prod.fst, rs.map Prod.snd, d⟩ := by
  have hlen := h.perm.length_eq
  apply blockBits_congr (by simp [hlen]) (by simp [hlen])
  simp only [prepare_pairs]
  rcases mapM_parityEquiv (decPair P) h with ⟨h1, h2⟩ | ⟨L, M, h1, h2, hLM⟩
  · left; simp [h1, h2]
  · rw [h1, h2]
    cases hc : (fp32.decode d).toFinite with
    | none => left; simp
    | some C =>
      right
      refine ⟨⟨L.map Prod.fst, L.map Prod.snd, C⟩, ⟨M.map Prod.fst, M.map Prod.snd, C⟩,
        by simp, by simp, ?_⟩
      refine accumulate_parityEquiv (x := ⟨L.map Prod.fst, L.map Prod.snd, C⟩)
        (y := ⟨M.map Prod.fst, M.map Prod.snd, C⟩) hP ?_ rfl
      rw [products_pairs, products_pairs]
      exact hLM.map _

/-- **The parity law on CDNA 3 FP8**, for every pair of operand formats. -/
theorem cdna3FP8_parityEquiv (fa fb : Format) (d : F32)
    {qs rs : List ((cdna3FP8 fa fb).a.Word × (cdna3FP8 fa fb).b.Word)} (h : ParityEquiv qs rs) :
    blockBits (P := cdna3FP8 fa fb) ⟨qs.map Prod.fst, qs.map Prod.snd, d⟩ =
      blockBits (P := cdna3FP8 fa fb) ⟨rs.map Prod.fst, rs.map Prod.snd, d⟩ :=
  blockBits_parityEquiv rfl d h

/-! ## Separating witnesses: one parity class versus two

For each combination of operand formats, products `x < 0` and `y` with `y/x = 1.5·2^-24`. In
different classes, the smaller group sum is rounded down to the common grid, which rounds the
negative `y` away from zero, to `−2^-23·|x|`; in one class `y` is truncated toward zero, to `0`.
E4M3 FNUZ words: `0xE8 = −32`, `0x40 = 1`, `0xC0 = −1`, `0x83 = −3·2^-10`, `0x01 = 2^-10`,
`0x02 = 2^-9`; E5M2 FNUZ words: `0xC0 = −1`, `0x40 = 1`, `0x92 = −1.5·2^-12`, `0x10 = 2^-12`,
`0x04 = 2^-15`, `0x86 = −1.5·2^-15`. Binary32 outputs: `0xC2000000 = −32`,
`0xC2000001 = −(32 + 2^-18)`, `0xBF800000 = −1`, `0xBF800001 = −(1 + 2^-23)`. -/

/-- Sixteen slots with `x` and `y` in different parity classes (slots 1 and 2). -/
def twoClasses {γ : Type} (z x y : γ) : List γ := [x, y] ++ List.replicate 14 z

/-- Sixteen slots with `x` and `y` in the same parity class (slots 1 and 3). -/
def oneClass {γ : Type} (z x y : γ) : List γ := [x, z, y] ++ List.replicate 13 z

/-- The output word of a block of operand pairs from `c = 0`. -/
def pairBlock (P : Model) (qs : List (P.a.Word × P.b.Word)) : Except ModelError F32 :=
  blockBits (P := P) ⟨qs.map Prod.fst, qs.map Prod.snd, 0⟩

/-- E4M3 × E4M3: `x = −32·1`, `y = −3·2^-10 · 2^-10`; `−(32 + 2^-18)` in two classes, `−32` in
one. -/
theorem cdna3FP8_sep_e4m3 :
    pairBlock (cdna3FP8 e4m3fnuz e4m3fnuz) (twoClasses (0, 0) (0xE8, 0x40) (0x83, 0x01)) =
      .ok 0xC2000001 ∧
    pairBlock (cdna3FP8 e4m3fnuz e4m3fnuz) (oneClass (0, 0) (0xE8, 0x40) (0x83, 0x01)) =
      .ok 0xC2000000 := by
  decide +kernel

/-- E5M2 × E5M2: `x = −1·1`, `y = −1.5·2^-12 · 2^-12`; `−(1 + 2^-23)` in two classes, `−1` in one. -/
theorem cdna3FP8_sep_e5m2 :
    pairBlock (cdna3FP8 e5m2fnuz e5m2fnuz) (twoClasses (0, 0) (0xC0, 0x40) (0x92, 0x10)) =
      .ok 0xBF800001 ∧
    pairBlock (cdna3FP8 e5m2fnuz e5m2fnuz) (oneClass (0, 0) (0xC0, 0x40) (0x92, 0x10)) =
      .ok 0xBF800000 := by
  decide +kernel

/-- E4M3 × E5M2: `x = −1·1`, `y = −3·2^-10 · 2^-15`; `−(1 + 2^-23)` in two classes, `−1` in one. -/
theorem cdna3FP8_sep_e4m3_e5m2 :
    pairBlock (cdna3FP8 e4m3fnuz e5m2fnuz) (twoClasses (0, 0) (0xC0, 0x40) (0x83, 0x04)) =
      .ok 0xBF800001 ∧
    pairBlock (cdna3FP8 e4m3fnuz e5m2fnuz) (oneClass (0, 0) (0xC0, 0x40) (0x83, 0x04)) =
      .ok 0xBF800000 := by
  decide +kernel

/-- E5M2 × E4M3: `x = −1·1`, `y = −1.5·2^-15 · 2^-9`; `−(1 + 2^-23)` in two classes, `−1` in one. -/
theorem cdna3FP8_sep_e5m2_e4m3 :
    pairBlock (cdna3FP8 e5m2fnuz e4m3fnuz) (twoClasses (0, 0) (0xC0, 0x40) (0x86, 0x02)) =
      .ok 0xBF800001 ∧
    pairBlock (cdna3FP8 e5m2fnuz e4m3fnuz) (oneClass (0, 0) (0xC0, 0x40) (0x86, 0x02)) =
      .ok 0xBF800000 := by
  decide +kernel

/-! ## Which permutations of the 16 slots preserve the output

A permutation `σ` of the slots (a list that is a permutation of `0, …, 15`) moves slot `σ i` of a
block to slot `i`. It preserves the output on every input exactly when it preserves the parity
partition: `i` and `j` have the same parity iff `σ i` and `σ j` do. -/

/-- The slots of `qs` permuted by `σ`: slot `i` holds slot `σ i` of `qs` (`z` past the end). -/
def permuteSlots {γ : Type} (σ : List ℕ) (z : γ) (qs : List γ) : List γ :=
  σ.map fun i => qs.getD i z

/-- `σ` preserves the parity partition of the slots `0, …, 15`. -/
def ParityPreserving (σ : List ℕ) : Prop :=
  ∀ i j, i < 16 → j < 16 → (i % 2 = j % 2 ↔ σ.getD i 0 % 2 = σ.getD j 0 % 2)

theorem mem_oddIndexed_iff {γ : Type} {a : γ} : ∀ l : List γ,
    a ∈ oddIndexed l ↔ ∃ i, i % 2 = 0 ∧ l[i]? = some a
  | [] => by simp [oddIndexed]
  | [x] => by
    simp only [oddIndexed, List.mem_singleton]
    constructor
    · rintro rfl; exact ⟨0, rfl, rfl⟩
    · rintro ⟨i, hi, h⟩
      cases i with
      | zero => simpa [eq_comm] using h
      | succ i => simp at h
  | x :: y :: xs => by
    have ih := mem_oddIndexed_iff (a := a) xs
    simp only [oddIndexed, List.mem_cons, ih]
    constructor
    · rintro (rfl | ⟨i, hi, h⟩)
      · exact ⟨0, rfl, rfl⟩
      · exact ⟨i + 2, by omega, by simpa using h⟩
    · rintro ⟨i, hi, h⟩
      match i, hi, h with
      | 0, _, h => left; simpa [eq_comm] using h
      | 1, hi, _ => simp at hi
      | i + 2, hi, h => right; exact ⟨i, by omega, by simpa using h⟩

theorem mem_evenIndexed_iff {γ : Type} {a : γ} : ∀ l : List γ,
    a ∈ evenIndexed l ↔ ∃ i, i % 2 = 1 ∧ l[i]? = some a
  | [] => by simp [evenIndexed]
  | [x] => by
    simp only [evenIndexed, List.not_mem_nil, false_iff]
    rintro ⟨i, hi, h⟩
    match i, hi, h with
    | 0, hi, _ => simp at hi
    | i + 1, _, h => simp at h
  | x :: y :: xs => by
    have ih := mem_evenIndexed_iff (a := a) xs
    simp only [evenIndexed, List.mem_cons, ih]
    constructor
    · rintro (rfl | ⟨i, hi, h⟩)
      · exact ⟨1, rfl, rfl⟩
      · exact ⟨i + 2, by omega, by simpa using h⟩
    · rintro ⟨i, hi, h⟩
      match i, hi, h with
      | 0, hi, _ => simp at hi
      | 1, _, h => left; simpa [eq_comm] using h
      | i + 2, hi, h => right; exact ⟨i, by omega, by simpa using h⟩

theorem oddIndexed_sublist {γ : Type} : ∀ l : List γ, (oddIndexed l).Sublist l
  | [] => by simp [oddIndexed]
  | [x] => by simp [oddIndexed]
  | x :: y :: xs => by
    simp only [oddIndexed]
    exact ((oddIndexed_sublist xs).cons y).cons_cons x

theorem evenIndexed_sublist {γ : Type} : ∀ l : List γ, (evenIndexed l).Sublist l
  | [] => by simp [evenIndexed]
  | [x] => by simp [evenIndexed]
  | x :: y :: xs => by
    simp only [evenIndexed]
    exact ((evenIndexed_sublist xs).cons_cons y).cons x

private theorem getD_of_getElem? {σ : List ℕ} {i a : ℕ} (h : σ[i]? = some a) : σ.getD i 0 = a := by
  simp [List.getD, h]

private theorem mem_range16 {σ : List ℕ} (hσ : σ.Perm (List.range 16)) {a : ℕ} :
    a ∈ σ ↔ a < 16 := by
  rw [hσ.mem_iff, List.mem_range]

private theorem length16 {σ : List ℕ} (hσ : σ.Perm (List.range 16)) : σ.length = 16 := by
  rw [hσ.length_eq, List.length_range]

/-- The odd and the even positions of a parity-preserving permutation hold the slots of one
parity each. -/
theorem parityPreserving_mem {σ : List ℕ} (hσ : σ.Perm (List.range 16)) (hp : ParityPreserving σ)
    (a : ℕ) :
    (a ∈ oddIndexed σ ↔ a < 16 ∧ a % 2 = σ.getD 0 0 % 2) ∧
    (a ∈ evenIndexed σ ↔ a < 16 ∧ a % 2 ≠ σ.getD 0 0 % 2) := by
  have hl := length16 hσ
  have pos : ∀ i, i < 16 → (i % 2 = 0 ↔ σ.getD i 0 % 2 = σ.getD 0 0 % 2) := by
    intro i hi
    have := hp i 0 hi (by decide)
    simpa using this
  have back : a < 16 → ∃ i, i < 16 ∧ σ[i]? = some a := by
    intro ha
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp ((mem_range16 hσ).mpr ha)
    exact ⟨i, by omega, by simp [List.getElem?_eq_getElem hi, he]⟩
  have bound : ∀ i, σ[i]? = some a → i < 16 ∧ a < 16 := by
    intro i h
    have hi : i < σ.length := by
      rcases Nat.lt_or_ge i σ.length with hlt | hge
      · exact hlt
      · simp [List.getElem?_eq_none hge] at h
    refine ⟨by omega, (mem_range16 hσ).mp (List.mem_of_getElem? h)⟩
  constructor
  · rw [mem_oddIndexed_iff]
    constructor
    · rintro ⟨i, hi, h⟩
      obtain ⟨hi16, ha⟩ := bound i h
      refine ⟨ha, ?_⟩
      have := (pos i hi16).mp hi
      rwa [getD_of_getElem? h] at this
    · rintro ⟨ha, hs⟩
      obtain ⟨i, hi16, h⟩ := back ha
      refine ⟨i, ?_, h⟩
      apply (pos i hi16).mpr
      rw [getD_of_getElem? h]; exact hs
  · rw [mem_evenIndexed_iff]
    constructor
    · rintro ⟨i, hi, h⟩
      obtain ⟨hi16, ha⟩ := bound i h
      refine ⟨ha, ?_⟩
      intro hs
      have := (pos i hi16).mpr (by rw [getD_of_getElem? h]; exact hs)
      omega
    · rintro ⟨ha, hs⟩
      obtain ⟨i, hi16, h⟩ := back ha
      refine ⟨i, ?_, h⟩
      rcases Nat.mod_two_eq_zero_or_one i with h0 | h1
      · exact absurd (by have := (pos i hi16).mp h0; rwa [getD_of_getElem? h] at this) hs
      · exact h1

private theorem oddIndexed_range16 (a : ℕ) :
    a ∈ oddIndexed (List.range 16) ↔ a < 16 ∧ a % 2 = 0 := by
  have : oddIndexed (List.range 16) = [0, 2, 4, 6, 8, 10, 12, 14] := by decide
  rw [this]; simp only [List.mem_cons, List.not_mem_nil, or_false]; omega

private theorem evenIndexed_range16 (a : ℕ) :
    a ∈ evenIndexed (List.range 16) ↔ a < 16 ∧ a % 2 = 1 := by
  have : evenIndexed (List.range 16) = [1, 3, 5, 7, 9, 11, 13, 15] := by decide
  rw [this]; simp only [List.mem_cons, List.not_mem_nil, or_false]; omega

/-- A parity-preserving permutation keeps the pair {odd slots, even slots}. -/
theorem parityEquiv_of_parityPreserving {σ : List ℕ} (hσ : σ.Perm (List.range 16))
    (hp : ParityPreserving σ) : ParityEquiv σ (List.range 16) := by
  have nd : σ.Nodup := hσ.nodup_iff.mpr List.nodup_range
  have ndo : (oddIndexed σ).Nodup := nd.sublist (oddIndexed_sublist σ)
  have nde : (evenIndexed σ).Nodup := nd.sublist (evenIndexed_sublist σ)
  have ro : (oddIndexed (List.range 16)).Nodup := by decide
  have re : (evenIndexed (List.range 16)).Nodup := by decide
  rcases Nat.mod_two_eq_zero_or_one (σ.getD 0 0) with h0 | h1
  · left
    constructor
    · rw [List.perm_ext_iff_of_nodup ndo ro]
      intro a; rw [(parityPreserving_mem hσ hp a).1, oddIndexed_range16, h0]
    · rw [List.perm_ext_iff_of_nodup nde re]
      intro a; rw [(parityPreserving_mem hσ hp a).2, evenIndexed_range16, h0]; omega
  · right
    constructor
    · rw [List.perm_ext_iff_of_nodup ndo re]
      intro a; rw [(parityPreserving_mem hσ hp a).1, evenIndexed_range16, h1]
    · rw [List.perm_ext_iff_of_nodup nde ro]
      intro a; rw [(parityPreserving_mem hσ hp a).2, oddIndexed_range16, h1]; omega

private theorem eq_range_map {γ : Type} (z : γ) {qs : List γ} (h : qs.length = 16) :
    qs = (List.range 16).map fun i => qs.getD i z := by
  apply List.ext_getElem (by simp [h])
  intro i h1 h2
  simp [List.getD, List.getElem?_eq_getElem h1]

/-! ### Two marked slots -/

/-- Slot pattern: `1` at slot `a`, `2` at slot `b`, `0` elsewhere. -/
def markPattern (a b : ℕ) : List ℕ :=
  (List.range 16).map fun k => if k = a then 1 else if k = b then 2 else 0

/-- Fill a pattern: `1 ↦ x`, `2 ↦ y`, and `z` elsewhere. -/
def markFill {γ : Type} (z x y : γ) : ℕ → γ := fun n => if n = 1 then x else if n = 2 then y else z

/-- The two patterns of `oneClass` and `twoClasses`. -/
def markCanon (same : Bool) : List ℕ :=
  if same then [1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  else [1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem markPattern_parityEquiv_all : ∀ a, a < 16 → ∀ b, b < 16 → a ≠ b →
    ParityEquiv (markPattern a b) (markCanon (a % 2 == b % 2)) := by
  decide +kernel

theorem markPattern_parityEquiv {a b : ℕ} (ha : a < 16) (hb : b < 16) (hab : a ≠ b) :
    ParityEquiv (markPattern a b) (markCanon (a % 2 == b % 2)) :=
  markPattern_parityEquiv_all a ha b hb hab

theorem classes_markFill {γ : Type} (z x y : γ) :
    oneClass z x y = (markCanon true).map (markFill z x y) ∧
      twoClasses z x y = (markCanon false).map (markFill z x y) := by
  simp [oneClass, twoClasses, markFill, markCanon, List.replicate]

private theorem getD_range_map {γ : Type} (z : γ) (g : ℕ → γ) {n m : ℕ} (h : m < n) :
    ((List.range n).map g).getD m z = g m := by
  simp [List.getD, List.getElem?_range h]

/-- `σ` moves the marks from slots `σ i, σ j` to slots `i, j`. -/
theorem permuteSlots_markPattern {σ : List ℕ} (hσ : σ.Perm (List.range 16)) {i j : ℕ}
    (hi : i < 16) (hj : j < 16) {γ : Type} (z x y : γ) :
    permuteSlots σ z ((markPattern (σ.getD i 0) (σ.getD j 0)).map (markFill z x y)) =
      (markPattern i j).map (markFill z x y) := by
  have hl := length16 hσ
  have nd : σ.Nodup := hσ.nodup_iff.mpr List.nodup_range
  apply List.ext_getElem (by simp [permuteSlots, markPattern, hl])
  intro k h1 h2
  have hk : k < 16 := by simpa [permuteSlots, hl] using h1
  have hσk : σ[k]'(by omega) < 16 := (mem_range16 hσ).mp (List.getElem_mem _)
  simp only [permuteSlots, markPattern, List.getElem_map, List.getElem_range, List.map_map]
  show (List.map (markFill z x y ∘ fun k => if k = σ.getD i 0 then 1 else if k = σ.getD j 0 then 2
    else 0) (List.range 16)).getD σ[k] z =
    (markFill z x y ∘ fun k => if k = i then 1 else if k = j then 2 else 0) k
  have hgi : σ.getD i 0 = σ[i]'(by omega) := by
    simp [List.getD, List.getElem?_eq_getElem (show i < σ.length by omega)]
  have hgj : σ.getD j 0 = σ[j]'(by omega) := by
    simp [List.getD, List.getElem?_eq_getElem (show j < σ.length by omega)]
  have inj : ∀ m (hm : m < σ.length), σ[k]'(by omega) = σ[m] ↔ k = m := fun m hm =>
    List.getElem_inj nd
  rw [getD_range_map z _ hσk]
  simp only [Function.comp_apply, hgi, hgj]
  by_cases hki : k = i
  · subst hki; simp
  · have h1' : ¬ σ[k]'(by omega) = σ[i]'(by omega) := fun h => hki ((inj i (by omega)).mp h)
    by_cases hkj : k = j
    · subst hkj; simp [hki, h1']
    · have h2' : ¬ σ[k]'(by omega) = σ[j]'(by omega) := fun h => hkj ((inj j (by omega)).mp h)
      simp [hki, hkj, h1', h2']

/-- **Which slot permutations preserve the output.** On a model with odd/even grouping that has
a separating pair `x, y` (different words in one parity class and in two), a permutation `σ` of
the 16 slots gives the same word as the identity on every input and every accumulator input iff
it preserves the parity partition of the slots. -/
theorem blockBits_permute_iff {P : Model} (hP : P.accumulation = .oddEvenGrouping)
    (x y : P.a.Word × P.b.Word)
    (hsep : pairBlock P (twoClasses (0, 0) x y) ≠ pairBlock P (oneClass (0, 0) x y))
    {σ : List ℕ} (hσ : σ.Perm (List.range 16)) :
    (∀ (qs : List (P.a.Word × P.b.Word)) (d : F32), qs.length = 16 →
      blockBits (P := P) ⟨(permuteSlots σ (0, 0) qs).map Prod.fst,
          (permuteSlots σ (0, 0) qs).map Prod.snd, d⟩ =
        blockBits (P := P) ⟨qs.map Prod.fst, qs.map Prod.snd, d⟩) ↔ ParityPreserving σ := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro hnp
    have hex : ∃ i j, i < 16 ∧ j < 16 ∧ ¬(i % 2 = j % 2 ↔ σ.getD i 0 % 2 = σ.getD j 0 % 2) := by
      apply Classical.byContradiction; intro hne; apply hnp; intro i j hi hj
      apply Classical.byContradiction; intro hh; exact hne ⟨i, j, hi, hj, hh⟩
    obtain ⟨i, j, hi, hj, hij⟩ := hex
    have hl := length16 hσ
    have nd : σ.Nodup := hσ.nodup_iff.mpr List.nodup_range
    have hne : i ≠ j := by rintro rfl; exact hij (Iff.intro (fun _ => rfl) (fun _ => rfl))
    have hgi : σ.getD i 0 = σ[i]'(by omega) := by
      simp [List.getD, List.getElem?_eq_getElem (show i < σ.length by omega)]
    have hgj : σ.getD j 0 = σ[j]'(by omega) := by
      simp [List.getD, List.getElem?_eq_getElem (show j < σ.length by omega)]
    have hu : σ.getD i 0 < 16 := by rw [hgi]; exact (mem_range16 hσ).mp (List.getElem_mem _)
    have hv : σ.getD j 0 < 16 := by rw [hgj]; exact (mem_range16 hσ).mp (List.getElem_mem _)
    have huv : σ.getD i 0 ≠ σ.getD j 0 := by
      rw [hgi, hgj]; intro h'; exact hne ((List.getElem_inj nd).mp h')
    let z : P.a.Word × P.b.Word := (0, 0)
    let qs := (markPattern (σ.getD i 0) (σ.getD j 0)).map (markFill z x y)
    have hq := h qs 0 (by simp [qs, markPattern])
    rw [show permuteSlots σ (0, 0) qs = (markPattern i j).map (markFill z x y) from
      permuteSlots_markPattern hσ hi hj z x y] at hq
    rw [blockBits_parityEquiv hP 0 ((markPattern_parityEquiv hi hj hne).map (markFill z x y)),
      blockBits_parityEquiv hP 0 ((markPattern_parityEquiv hu hv huv).map (markFill z x y))] at hq
    obtain ⟨hs, hd⟩ := classes_markFill z x y
    have hb : (i % 2 == j % 2) ≠ (σ.getD i 0 % 2 == σ.getD j 0 % 2) := by
      intro hb; apply hij
      constructor
      · intro h1; have := congrArg (· = true) hb; simp_all
      · intro h1; have := congrArg (· = true) hb; simp_all
    revert hq hb
    cases (i % 2 == j % 2) <;> cases (σ.getD i 0 % 2 == σ.getD j 0 % 2) <;> intro hq hb
    · exact hb rfl
    · rw [← hs, ← hd] at hq; exact hsep (by unfold pairBlock; first | exact hq | exact hq.symm)
    · rw [← hs, ← hd] at hq; exact hsep (by unfold pairBlock; first | exact hq | exact hq.symm)
    · exact hb rfl
  · intro hp qs d hlen
    have hg := (parityEquiv_of_parityPreserving hσ hp).map (fun i => qs.getD i (0, 0))
    rw [← eq_range_map (0, 0) hlen] at hg
    exact blockBits_parityEquiv hP d (qs := permuteSlots σ (0, 0) qs) hg

/-- **CDNA 3 FP8, every combination of operand formats.** A permutation of the 16 slots of a
block preserves the output on every input iff it preserves the parity partition of the slots. -/
theorem cdna3FP8_permute_iff (fa fb : Format)
    (hfa : fa = e4m3fnuz ∨ fa = e5m2fnuz) (hfb : fb = e4m3fnuz ∨ fb = e5m2fnuz)
    {σ : List ℕ} (hσ : σ.Perm (List.range 16)) :
    (∀ (qs : List ((cdna3FP8 fa fb).a.Word × (cdna3FP8 fa fb).b.Word)) (d : F32),
      qs.length = 16 →
      blockBits (P := cdna3FP8 fa fb) ⟨(permuteSlots σ (0, 0) qs).map Prod.fst,
          (permuteSlots σ (0, 0) qs).map Prod.snd, d⟩ =
        blockBits (P := cdna3FP8 fa fb) ⟨qs.map Prod.fst, qs.map Prod.snd, d⟩) ↔
      ParityPreserving σ := by
  rcases hfa with rfl | rfl <;> rcases hfb with rfl | rfl
  · exact blockBits_permute_iff rfl (0xE8, 0x40) (0x83, 0x01)
      (by rw [cdna3FP8_sep_e4m3.1, cdna3FP8_sep_e4m3.2]; decide) hσ
  · exact blockBits_permute_iff rfl (0xC0, 0x40) (0x83, 0x04)
      (by rw [cdna3FP8_sep_e4m3_e5m2.1, cdna3FP8_sep_e4m3_e5m2.2]; decide) hσ
  · exact blockBits_permute_iff rfl (0xC0, 0x40) (0x86, 0x02)
      (by rw [cdna3FP8_sep_e5m2_e4m3.1, cdna3FP8_sep_e5m2_e4m3.2]; decide) hσ
  · exact blockBits_permute_iff rfl (0xC0, 0x40) (0x92, 0x10)
      (by rw [cdna3FP8_sep_e5m2.1, cdna3FP8_sep_e5m2.2]; decide) hσ

end MatrixCore
