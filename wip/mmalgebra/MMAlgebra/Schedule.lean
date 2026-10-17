import MMAlgebra.Term

/-! # Schedules for every length

A matrix multiplier is called on integer vectors of any length `k`. A `Schedule` fixes, for every
`k`, a reduction term over the products `0, …, k − 1`, each used once: a chain, a split-K, a
stream-K, a pairwise reduction, or any other order and grouping of block FMAs and binary32
additions. The lemmas here relate sums over a term's leaves to Ozaki's integer dot products. -/

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

namespace MMAlgebra

/-- A reduction schedule for every length: for each `k`, a term with blocks of `K` slots whose
products are the indices `0, …, k − 1`, each once. -/
structure Schedule (K : ℕ) where
  term : ℕ → Term
  wf : ∀ k, TermWF K (term k)
  leaves : ∀ k, (term k).leaves.Perm (List.range k)

theorem range_sum_dotZ : ∀ (x y : List ℤ), x.length = y.length →
    ((List.range x.length).map fun i => ((x.getD i 0 : ℤ) : ℚ) * ((y.getD i 0 : ℤ) : ℚ)).sum =
      ((Ozaki.dotZ x y : ℤ) : ℚ)
  | [], [], _ => by simp [Ozaki.dotZ]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: xs, c :: ys, h => by
    have ih := range_sum_dotZ xs ys (by simpa using h)
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.sum_cons]
    simp only [Function.comp_def, Nat.succ_eq_add_one, List.getD_cons_succ, List.getD_cons_zero]
    rw [ih]
    simp [Ozaki.dotZ, Rat.intCast_add, Rat.intCast_mul]

theorem range_sum_dotAbs : ∀ (x y : List ℤ), x.length = y.length →
    ((List.range x.length).map fun i => Rat.abs (((x.getD i 0 : ℤ) : ℚ) * ((y.getD i 0 : ℤ) : ℚ))).sum =
      ((Ozaki.dotAbs x y : ℕ) : ℚ)
  | [], [], _ => by simp [Ozaki.dotAbs]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: xs, c :: ys, h => by
    have ih := range_sum_dotAbs xs ys (by simpa using h)
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.sum_cons]
    simp only [Function.comp_def, Nat.succ_eq_add_one, List.getD_cons_succ, List.getD_cons_zero]
    rw [ih, ← Rat.intCast_mul, Ozaki.abs_intCast]
    simp [Ozaki.dotAbs, Rat.natCast_add]

/-- Below the length, `getD` of a mapped list is the image of `getD`. -/
theorem getD_map_lt {γ δ : Type} (f : γ → δ) (d : δ) (e : γ) :
    ∀ (x : List γ) (i : ℕ), i < x.length → (x.map f).getD i d = f (x.getD i e)
  | [], _, h => by simp at h
  | _ :: _, 0, _ => by simp
  | _ :: xs, i + 1, h => by
    simp only [List.map_cons, List.getD_cons_succ]
    exact getD_map_lt f d e xs i (by simpa using h)

/-- An entry of a mapped list is the default or the image of a member. -/
theorem getD_map_cases {γ δ : Type} (f : γ → δ) (d : δ) :
    ∀ (x : List γ) (i : ℕ), (x.map f).getD i d = d ∨ ∃ z ∈ x, (x.map f).getD i d = f z
  | [], _ => Or.inl (by simp)
  | z :: _, 0 => Or.inr ⟨z, by simp, by simp⟩
  | _ :: xs, i + 1 => by
    simp only [List.map_cons, List.getD_cons_succ]
    rcases getD_map_cases f d xs i with h | ⟨z, hz, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨z, List.mem_cons_of_mem _ hz, h⟩

/-- `getD` below the length is a member. -/
theorem getD_mem_of_lt {γ : Type} (e : γ) : ∀ (x : List γ) (i : ℕ), i < x.length → x.getD i e ∈ x
  | [], _, h => by simp at h
  | _ :: _, 0, _ => by simp
  | _ :: xs, i + 1, h => by
    simp only [List.getD_cons_succ]
    exact List.mem_cons_of_mem _ (getD_mem_of_lt e xs i (by simpa using h))

theorem sum_perm {l₁ l₂ : List ℚ} (h : l₁.Perm l₂) : l₁.sum = l₂.sum := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp [ih]
  | swap x y l => simp only [List.sum_cons]; grind
  | trans _ _ ih₁ ih₂ => rw [ih₁, ih₂]

/-- Sums over a term's leaves are sums over `0, …, k − 1` when the leaves are a permutation of
them. -/
theorem sum_leaves_eq_range {t : Term} {k : ℕ} (h : t.leaves.Perm (List.range k)) (f : ℕ → ℚ) :
    (t.leaves.map f).sum = ((List.range k).map f).sum :=
  sum_perm (h.map f)

/-! ## An example: the serial schedule -/

/-- The serial chain over `0, …, k − 1`: one product per block FMA, in order. -/
def serialTerm (K : ℕ) : ℕ → Term
  | 0 => .zero
  | k + 1 => .blk (serialTerm K k) (some k :: List.replicate (K - 1) none)

theorem serialTerm_leaves (K : ℕ) : ∀ k, (serialTerm K k).leaves = List.range k
  | 0 => rfl
  | k + 1 => by
    simp only [serialTerm, Term.leaves, serialTerm_leaves K k, List.range_succ]
    simp

theorem serialTerm_wf {K : ℕ} (hK : 0 < K) : ∀ k, TermWF K (serialTerm K k)
  | 0 => trivial
  | k + 1 => ⟨serialTerm_wf hK k, by simp; omega⟩

/-- The serial schedule, one product per block FMA: a schedule for every FMA size. -/
def serialSchedule (K : ℕ) (hK : 0 < K) : Schedule K where
  term := serialTerm K
  wf := serialTerm_wf hK
  leaves k := by rw [serialTerm_leaves]

end MMAlgebra
