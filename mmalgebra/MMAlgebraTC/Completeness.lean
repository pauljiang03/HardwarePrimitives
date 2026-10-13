import MMAlgebraTC.Chain

/-! # Completeness for two products

Two chains hold two products `x` and `y` in one of three patterns: together in one block, `x` in an
earlier block than `y`, or `y` earlier than `x`. `complete_pair` shows that chains with different
patterns give different output words on some finite input supported on `{x, y}`, from five concrete
block evaluations; `v100_complete_pair`, `a100_complete_pair` and `h100_complete_pair` discharge
them by kernel evaluation on the fp16 models of V100, A100 and H100.

The proof restricts both chains to `{x, y}` (`chain_restrict`), replaces every restricted block by
the canonical block of its kind (`evalBlock_bits_perm`), drops the empty blocks (they pass a finite
accumulator other than `−0` through, `zero_products_passthrough`), and evaluates the pattern. -/

open TensorCore

namespace MMAlgebra.TC

/-! ## Two products: the kinds of a restricted block -/

/-- The two-index support `{x, y}`. -/
def pairSet (x y : ℕ) : ℕ → Bool := fun i => i == x || i == y

/-- What a block holds of `x` and `y`. -/
inductive Kind | e | x | y | xy
  deriving DecidableEq, Repr

def kindOf (x y : ℕ) (B : List (Option ℕ)) : Kind :=
  match B.contains (some x), B.contains (some y) with
  | false, false => .e
  | true, false => .x
  | false, true => .y
  | true, true => .xy

/-- The canonical block of a kind: its products first, then empty slots. -/
def canonBlock (K x y : ℕ) : Kind → List (Option ℕ)
  | .e => List.replicate K none
  | .x => some x :: List.replicate (K - 1) none
  | .y => some y :: List.replicate (K - 1) none
  | .xy => some x :: some y :: List.replicate (K - 2) none

section counts
variable (x y : ℕ)

theorem count_restrict_x (hxy : x ≠ y) (B : List (Option ℕ)) :
    (B.map (fun o => o.filter (pairSet x y))).count (some x) = B.count (some x) := by
  induction B with
  | nil => rfl
  | cons o B ih =>
    simp only [List.map_cons, List.count_cons, ih]
    cases o with
    | none => simp [Option.filter]
    | some z =>
      by_cases hz : z = x
      · subst hz; simp [Option.filter, pairSet]
      · by_cases hzy : z = y
        · subst hzy; simp [Option.filter, pairSet, hz]
        · simp [Option.filter, pairSet, hz, hzy]

theorem count_restrict_y (hxy : x ≠ y) (B : List (Option ℕ)) :
    (B.map (fun o => o.filter (pairSet x y))).count (some y) = B.count (some y) := by
  induction B with
  | nil => rfl
  | cons o B ih =>
    simp only [List.map_cons, List.count_cons, ih]
    cases o with
    | none => simp [Option.filter]
    | some z =>
      by_cases hz : z = y
      · subst hz; simp [Option.filter, pairSet]
      · by_cases hzx : z = x
        · subst hzx; simp [Option.filter, pairSet, hz]
        · simp [Option.filter, pairSet, hz, hzx]

theorem count_restrict_other (w : ℕ) (hw : w ≠ x ∧ w ≠ y) (B : List (Option ℕ)) :
    (B.map (fun o => o.filter (pairSet x y))).count (some w) = 0 := by
  induction B with
  | nil => rfl
  | cons o B ih =>
    simp only [List.map_cons, List.count_cons, ih]
    cases o with
    | none => simp [Option.filter]
    | some z =>
      by_cases hz : z = x
      · subst hz; simp [Option.filter, pairSet]; omega
      · by_cases hzy : z = y
        · subst hzy; simp [Option.filter, pairSet]; omega
        · simp [Option.filter, pairSet, hz, hzy]

theorem count_restrict_none (hxy : x ≠ y) (B : List (Option ℕ)) :
    (B.map (fun o => o.filter (pairSet x y))).count none + B.count (some x) + B.count (some y) =
      B.length := by
  induction B with
  | nil => rfl
  | cons o B ih =>
    simp only [List.map_cons, List.count_cons, List.length_cons]
    cases o with
    | none => simp [Option.filter] at ih ⊢; omega
    | some z =>
      by_cases hz : z = x
      · subst hz; simp [Option.filter, pairSet, hxy] at ih ⊢; omega
      · by_cases hzy : z = y
        · subst hzy; simp [Option.filter, pairSet, hz] at ih ⊢; omega
        · simp [Option.filter, pairSet, hz, hzy] at ih ⊢; omega

theorem count_of_contains {B : List (Option ℕ)} {o : Option ℕ} (h : B.count o ≤ 1)
    (hc : B.contains o = true) : B.count o = 1 := by
  have := List.count_pos_iff.mpr (List.contains_iff_mem.mp hc)
  omega

theorem count_of_not_contains {B : List (Option ℕ)} {o : Option ℕ}
    (hc : B.contains o = false) : B.count o = 0 := by
  apply List.count_eq_zero.mpr
  intro hm
  have := List.contains_iff_mem.mpr hm
  rw [hc] at this
  contradiction

/-- A restricted block is a permutation of the canonical block of its kind. -/
theorem restrict_perm_canon (hxy : x ≠ y) (K : ℕ) (hK : 2 ≤ K) (B : List (Option ℕ))
    (hlen : B.length = K) (hx1 : B.count (some x) ≤ 1) (hy1 : B.count (some y) ≤ 1) :
    (B.map (fun o => o.filter (pairSet x y))).Perm (canonBlock K x y (kindOf x y B)) := by
  have hnone := count_restrict_none x y hxy B
  have hX := count_restrict_x x y hxy B
  have hY := count_restrict_y x y hxy B
  have hO := fun w hw => count_restrict_other x y w hw B
  generalize B.map (fun o => o.filter (pairSet x y)) = R at hnone hX hY hO ⊢
  rw [List.perm_iff_count]
  intro o
  have kx : B.count (some x) = if B.contains (some x) then 1 else 0 := by
    cases h : B.contains (some x)
    · exact count_of_not_contains h
    · exact count_of_contains hx1 h
  have ky : B.count (some y) = if B.contains (some y) then 1 else 0 := by
    cases h : B.contains (some y)
    · exact count_of_not_contains h
    · exact count_of_contains hy1 h
  unfold kindOf
  rcases o with _ | w
  · cases h1 : B.contains (some x) <;> cases h2 : B.contains (some y) <;>
      simp only [h1, h2, if_true, if_false, Bool.false_eq_true] at kx ky ⊢ <;>
      simp [canonBlock] <;> omega
  · by_cases hw : w = x
    · subst hw
      cases h1 : B.contains (some w) <;> cases h2 : B.contains (some y) <;>
        simp only [h1, h2, if_true, if_false, Bool.false_eq_true] at kx ky ⊢ <;>
        simp [canonBlock, List.count_replicate, Ne.symm hxy] <;> omega
    · by_cases hwy : w = y
      · subst hwy
        cases h1 : B.contains (some x) <;> cases h2 : B.contains (some w) <;>
          simp only [h1, h2, if_true, if_false, Bool.false_eq_true] at kx ky ⊢ <;>
          simp [canonBlock, List.count_replicate, hxy] <;> omega
      · have := hO w ⟨hw, hwy⟩
        cases h1 : B.contains (some x) <;> cases h2 : B.contains (some y) <;>
          simp [canonBlock, List.count_replicate, Ne.symm hw, Ne.symm hwy] <;>
          omega

end counts


/-! ## Chains restricted to two products run canonical blocks -/

/-- Run the canonical blocks of a list of kinds. -/
def runKinds (p : Model) (a b : ℕ → p.Word) (x y : ℕ) : F32 → List Kind → Except ModelError F32
  | c, [] => .ok c
  | c, k :: ks => match blockOut (p := p) ⟨(canonBlock p.nfma x y k).map (slotPair a b), c⟩ with
    | .error e => .error e
    | .ok d => runKinds p a b x y d ks

/-- Blocks of length `K` holding `x` and `y` at most once each. -/
def WF (K x y : ℕ) (σ : Sched) : Prop :=
  ∀ B ∈ σ, B.length = K ∧ B.count (some x) ≤ 1 ∧ B.count (some y) ≤ 1

theorem chain_kinds (p : Model) (hK : 2 ≤ p.nfma) (x y : ℕ) (hxy : x ≠ y)
    (a b : ℕ → p.Word) (σ : Sched) (hwf : WF p.nfma x y σ) (c : F32) :
    chainOut p a b c (restrict (pairSet x y) σ) = runKinds p a b x y c (σ.map (kindOf x y)) := by
  induction σ generalizing c with
  | nil => rfl
  | cons B σ ih =>
    have hB := hwf B (by simp)
    have hperm := restrict_perm_canon x y hxy p.nfma hK B hB.1 hB.2.1 hB.2.2
    have hblk := evalBlock_bits_perm (p := p) (hperm.map (slotPair a b)) c
    have ih' := ih (fun B' hB' => hwf B' (by simp [hB'])) 
    simp only [restrict, List.map_cons, chainOut, runKinds] at ih' ⊢
    rw [hblk]
    cases blockOut (p := p) ⟨(canonBlock p.nfma x y (kindOf x y B)).map (slotPair a b), c⟩ with
    | error e => rfl
    | ok d => exact ih' d

/-- A finite accumulator other than `−0`. -/
def Good (c : F32) : Prop := (finite32 c).isSome = true ∧ c ≠ 0x80000000

instance (c : F32) : Decidable (Good c) := by unfold Good; infer_instance

/-- Empty canonical blocks pass a good accumulator through (fp16 profiles). -/
theorem runKinds_e (K neab : ℕ) (eAlignMin : Option ℤ) (hfl : ∀ f ∈ eAlignMin, f ≤ -126)
    (a b : ℕ → (fp16Fp32Model K neab eAlignMin).Word) (x y : ℕ) (c : F32) (hc : Good c)
    (ks : List Kind) :
    runKinds (fp16Fp32Model K neab eAlignMin) a b x y c (.e :: ks) =
      runKinds (fp16Fp32Model K neab eAlignMin) a b x y c ks := by
  obtain ⟨hfs, hneg⟩ := hc
  obtain ⟨f, hf⟩ := Option.isSome_iff_exists.mp hfs
  obtain ⟨t, ht, hbits⟩ := zero_products_passthrough K neab eAlignMin hfl c f hf hneg
  have hmap : (canonBlock (fp16Fp32Model K neab eAlignMin).nfma x y .e).map (slotPair a b) =
      List.replicate K (0, 0) := by
    simp [canonBlock, fp16Fp32Model, List.map_replicate, slotPair]
  simp only [runKinds, hmap, blockOut, ht, Except.map, hbits]

theorem runKinds_es (K neab : ℕ) (eAlignMin : Option ℤ) (hfl : ∀ f ∈ eAlignMin, f ≤ -126)
    (a b : ℕ → (fp16Fp32Model K neab eAlignMin).Word) (x y : ℕ) (c : F32) (hc : Good c)
    (m : ℕ) (ks : List Kind) :
    runKinds (fp16Fp32Model K neab eAlignMin) a b x y c (List.replicate m .e ++ ks) =
      runKinds (fp16Fp32Model K neab eAlignMin) a b x y c ks := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.replicate_succ, List.cons_append, runKinds_e K neab eAlignMin hfl a b x y c hc, ih]

/-- A list of kinds whose nonempty kinds start with `k` is some empties, `k`, then the rest. -/
theorem kinds_split (l : List Kind) (k : Kind) (r : List Kind)
    (h : l.filter (· != .e) = k :: r) :
    ∃ i l', l = List.replicate i .e ++ k :: l' ∧ l'.filter (· != .e) = r := by
  induction l with
  | nil => simp at h
  | cons z l ih =>
    by_cases hz : z = .e
    · subst hz
      simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, if_false] at h
      obtain ⟨i, l', hl, hr⟩ := ih h
      exact ⟨i + 1, l', by rw [hl, List.replicate_succ, List.cons_append], hr⟩
    · have hz' : (z != Kind.e) = true := by simpa using hz
      simp only [List.filter_cons, hz', if_true, List.cons.injEq] at h
      obtain ⟨rfl, hr⟩ := h
      exact ⟨0, l, by simp, hr⟩

theorem kinds_nil (l : List Kind) (h : l.filter (· != .e) = []) : l = List.replicate l.length .e := by
  induction l with
  | nil => rfl
  | cons z l ih =>
    by_cases hz : z = .e
    · subst hz
      simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, if_false] at h
      rw [List.length_cons, List.replicate_succ, ← ih h]
    · have hz' : (z != Kind.e) = true := by simpa using hz
      simp [hz'] at h

/-- With good intermediate values, empty blocks can be dropped: one nonempty kind. -/
theorem runKinds_one (K neab : ℕ) (eAlignMin : Option ℤ) (hfl : ∀ f ∈ eAlignMin, f ≤ -126)
    (a b : ℕ → (fp16Fp32Model K neab eAlignMin).Word) (x y : ℕ) (c : F32) (hc : Good c)
    (l : List Kind) (k : Kind) (h : l.filter (· != .e) = [k]) (d : F32)
    (hd : runKinds (fp16Fp32Model K neab eAlignMin) a b x y c [k] = .ok d) (hdg : Good d) :
    runKinds (fp16Fp32Model K neab eAlignMin) a b x y c l = .ok d := by
  obtain ⟨i, l', rfl, hr⟩ := kinds_split l k [] h
  rw [runKinds_es K neab eAlignMin hfl a b x y c hc, kinds_nil l' hr]
  simp only [runKinds] at hd ⊢
  revert hd
  cases blockOut (p := fp16Fp32Model K neab eAlignMin)
      ⟨(canonBlock (fp16Fp32Model K neab eAlignMin).nfma x y k).map (slotPair a b), c⟩ with
  | error e => simp
  | ok d' =>
    simp only
    intro hd
    cases hd
    rw [← List.append_nil (List.replicate l'.length Kind.e),
      runKinds_es K neab eAlignMin hfl a b x y _ hdg]
    rfl

/-- Two nonempty kinds. -/
theorem runKinds_two (K neab : ℕ) (eAlignMin : Option ℤ) (hfl : ∀ f ∈ eAlignMin, f ≤ -126)
    (a b : ℕ → (fp16Fp32Model K neab eAlignMin).Word) (x y : ℕ) (c : F32) (hc : Good c)
    (l : List Kind) (k₁ k₂ : Kind) (h : l.filter (· != .e) = [k₁, k₂]) (d₁ d : F32)
    (hd₁ : runKinds (fp16Fp32Model K neab eAlignMin) a b x y c [k₁] = .ok d₁) (hdg₁ : Good d₁)
    (hd : runKinds (fp16Fp32Model K neab eAlignMin) a b x y d₁ [k₂] = .ok d) (hdg : Good d) :
    runKinds (fp16Fp32Model K neab eAlignMin) a b x y c l = .ok d := by
  obtain ⟨i, l', rfl, hr⟩ := kinds_split l k₁ [k₂] h
  rw [runKinds_es K neab eAlignMin hfl a b x y c hc]
  simp only [runKinds] at hd₁ ⊢
  revert hd₁
  cases blockOut (p := fp16Fp32Model K neab eAlignMin)
      ⟨(canonBlock (fp16Fp32Model K neab eAlignMin).nfma x y k₁).map (slotPair a b), c⟩ with
  | error e => simp
  | ok d' =>
    simp only
    intro hd₁
    cases hd₁
    exact runKinds_one K neab eAlignMin hfl a b x y d₁ hdg₁ l' k₂ hr d hd hdg


/-! ## Completeness for two products -/

theorem runKinds_step {p : Model} {a b : ℕ → p.Word} {x y : ℕ} {c d : F32} {k : Kind}
    (h : runKinds p a b x y c [k] = .ok d) (ks : List Kind) :
    runKinds p a b x y c (k :: ks) = runKinds p a b x y d ks := by
  simp only [runKinds] at h ⊢
  revert h
  cases blockOut (p := p) ⟨(canonBlock p.nfma x y k).map (slotPair a b), c⟩ with
  | error e => simp
  | ok d' => intro h; cases h; rfl

/-- The three ways a chain can hold two products. -/
def pairPatterns : List (List Kind) := [[.xy], [.x, .y], [.y, .x]]

/-- The value of a chain on an input supported on `{x, y}` is that of its pattern. -/
theorem chain_value (K neab : ℕ) (eAlignMin : Option ℤ) (hfl : ∀ f ∈ eAlignMin, f ≤ -126) (hK : 2 ≤ K)
    (A B : ℕ → (fp16Fp32Model K neab eAlignMin).Word) (x y : ℕ) (hxy : x ≠ y)
    (hA : ∀ i, i ≠ x → i ≠ y → A i = 0)
    (hB : ∀ i, ((fp16Fp32Model K neab eAlignMin).decode (B i)).isSome)
    (hz : ∃ z : Decoded, (fp16Fp32Model K neab eAlignMin).decode 0 = some z ∧ z.significand = 0)
    (σ : Sched) (hwf : WF K x y σ) (pat : List Kind)
    (hpat : (σ.map (kindOf x y)).filter (· != .e) = pat) (hmem : pat ∈ pairPatterns)
    (vx vy vxy vxy' vyx : F32)
    (h1 : runKinds (fp16Fp32Model K neab eAlignMin) A B x y 0 [.x] = .ok vx)
    (h2 : runKinds (fp16Fp32Model K neab eAlignMin) A B x y 0 [.y] = .ok vy)
    (h3 : runKinds (fp16Fp32Model K neab eAlignMin) A B x y 0 [.xy] = .ok vxy)
    (h4 : runKinds (fp16Fp32Model K neab eAlignMin) A B x y vx [.y] = .ok vxy')
    (h5 : runKinds (fp16Fp32Model K neab eAlignMin) A B x y vy [.x] = .ok vyx)
    (g1 : Good vx) (g2 : Good vy) (g3 : Good vxy) (g4 : Good vxy') (g5 : Good vyx) :
    chainOut (fp16Fp32Model K neab eAlignMin) A B 0 σ =
      runKinds (fp16Fp32Model K neab eAlignMin) A B x y 0 pat := by
  have hmask : mask (pairSet x y) A = A := by
    funext i
    unfold mask pairSet
    by_cases hix : i = x
    · simp [hix]
    · by_cases hiy : i = y
      · simp [hiy]
      · simp [hix, hiy, hA i hix hiy]
  have g0 : Good 0 := by decide
  have hK' : 2 ≤ (fp16Fp32Model K neab eAlignMin).nfma := hK
  have hr := chain_restrict _ (pairSet x y) A B hz hB 0 σ
  rw [hmask] at hr
  rw [hr, chain_kinds _ hK' x y hxy A B σ hwf 0]
  simp only [pairPatterns, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl
  · rw [runKinds_one K neab eAlignMin hfl A B x y 0 g0 _ .xy hpat vxy h3 g3, h3]
  · rw [runKinds_two K neab eAlignMin hfl A B x y 0 g0 _ .x .y hpat vx vxy' h1 g1 h4 g4,
      runKinds_step h1, h4]
  · rw [runKinds_two K neab eAlignMin hfl A B x y 0 g0 _ .y .x hpat vy vyx h2 g2 h5 g5,
      runKinds_step h2, h5]


section Witness
variable (K neab : ℕ) (eAlignMin : Option ℤ)

local notation "P" => fp16Fp32Model K neab eAlignMin

/-- An input with products `x ↦ u`, `y ↦ v` and zero elsewhere. -/
def wfun (x y : ℕ) (u v : (fp16Fp32Model K neab eAlignMin).Word) : ℕ → (fp16Fp32Model K neab eAlignMin).Word :=
  fun i => if i = x then u else if i = y then v else 0

theorem canon_x (x y : ℕ) (_hxy : x ≠ y) (ax ay bx by_ : (P).Word) :
    (canonBlock (P).nfma x y .x).map (slotPair (wfun K neab eAlignMin x y ax ay) (wfun K neab eAlignMin x y bx by_)) =
      (ax, bx) :: List.replicate (K - 1) (0, 0) := by
  simp [canonBlock, slotPair, wfun, List.map_replicate, fp16Fp32Model]

theorem canon_y (x y : ℕ) (hxy : x ≠ y) (ax ay bx by_ : (P).Word) :
    (canonBlock (P).nfma x y .y).map (slotPair (wfun K neab eAlignMin x y ax ay) (wfun K neab eAlignMin x y bx by_)) =
      (ay, by_) :: List.replicate (K - 1) (0, 0) := by
  simp [canonBlock, slotPair, wfun, List.map_replicate, fp16Fp32Model, Ne.symm hxy]

theorem canon_xy (x y : ℕ) (hxy : x ≠ y) (ax ay bx by_ : (P).Word) :
    (canonBlock (P).nfma x y .xy).map (slotPair (wfun K neab eAlignMin x y ax ay) (wfun K neab eAlignMin x y bx by_)) =
      (ax, bx) :: (ay, by_) :: List.replicate (K - 2) (0, 0) := by
  simp [canonBlock, slotPair, wfun, List.map_replicate, fp16Fp32Model, Ne.symm hxy]

theorem runKinds_single {a b : ℕ → (P).Word} {x y : ℕ} {c d : F32} {k : Kind}
    {ps : List ((P).Word × (P).Word)}
    (hm : (canonBlock (P).nfma x y k).map (slotPair a b) = ps)
    (h : blockOut (p := P) ⟨ps, c⟩ = .ok d) :
    runKinds (P) a b x y c [k] = .ok d := by
  simp only [runKinds, hm, h]

/-- **Completeness for two products (Tensor Cores, fp16).** If two chains hold `x` and `y` in
different patterns (together in one block, `x` first, `y` first), some finite input supported on
`{x, y}` gives them different outputs. The hypotheses `e₁ … e₅` and `g₁ … g₅` are facts about five
concrete block evaluations, discharged per GPU by kernel evaluation. -/
theorem complete_pair (hfl : ∀ f ∈ eAlignMin, f ≤ -126) (hK : 2 ≤ K)
    (hz : ∃ z : Decoded, (P).decode 0 = some z ∧ z.significand = 0)
    (ax bx ay by_ : (P).Word)
    (hfin : ((P).decode bx).isSome ∧ ((P).decode by_).isSome ∧ ((P).decode 0).isSome)
    (vx vy vxy vlt vgt : F32)
    (e₁ : blockOut (p := P) ⟨(ax, bx) :: List.replicate (K - 1) (0, 0), 0⟩ = .ok vx)
    (e₂ : blockOut (p := P) ⟨(ay, by_) :: List.replicate (K - 1) (0, 0), 0⟩ = .ok vy)
    (e₃ : blockOut (p := P) ⟨(ax, bx) :: (ay, by_) :: List.replicate (K - 2) (0, 0), 0⟩ = .ok vxy)
    (e₄ : blockOut (p := P) ⟨(ay, by_) :: List.replicate (K - 1) (0, 0), vx⟩ = .ok vlt)
    (e₅ : blockOut (p := P) ⟨(ax, bx) :: List.replicate (K - 1) (0, 0), vy⟩ = .ok vgt)
    (g₁ : Good vx) (g₂ : Good vy) (g₃ : Good vxy) (g₄ : Good vlt) (g₅ : Good vgt)
    (hsep : vlt ≠ vgt ∧ (vxy ≠ vlt ∨ vxy ≠ vgt))
    (σ τ : Sched) (x y : ℕ) (hxy : x ≠ y) (hσ : WF K x y σ) (hτ : WF K x y τ)
    (pσ pτ : List Kind)
    (hpσ : (σ.map (kindOf x y)).filter (· != .e) = pσ)
    (hpτ : (τ.map (kindOf x y)).filter (· != .e) = pτ)
    (hmσ : pσ ∈ pairPatterns) (hmτ : pτ ∈ pairPatterns) (hne : pσ ≠ pτ) :
    ∃ A B : ℕ → (P).Word, (∀ i, ((P).decode (B i)).isSome) ∧ (∀ i, i ≠ x → i ≠ y → A i = 0) ∧
      chainOut (P) A B 0 σ ≠ chainOut (P) A B 0 τ := by
  have e₃' : blockOut (p := P) ⟨(ay, by_) :: (ax, bx) :: List.replicate (K - 2) (0, 0), 0⟩ =
      .ok vxy := by
    rw [evalBlock_bits_perm (List.Perm.swap _ _ _)]; exact e₃
  -- the two assignments: as given, and with x and y exchanged
  have hB : ∀ (u v : (P).Word), ((P).decode u).isSome → ((P).decode v).isSome →
      ∀ i, ((P).decode (wfun K neab eAlignMin x y u v i)).isSome := by
    intro u v hu hv i
    unfold wfun
    split
    · exact hu
    · split
      · exact hv
      · exact hfin.2.2
  have hA : ∀ (u v : (P).Word) i, i ≠ x → i ≠ y → wfun K neab eAlignMin x y u v i = 0 := by
    intro u v i hix hiy
    simp [wfun, hix, hiy]
  -- chain values under an assignment
  have val : ∀ (u v s t : (P).Word) (wx wy wxy wl wg : F32),
      ((P).decode t).isSome → ((P).decode s).isSome →
      blockOut (p := P) ⟨(u, s) :: List.replicate (K - 1) (0, 0), 0⟩ = .ok wx →
      blockOut (p := P) ⟨(v, t) :: List.replicate (K - 1) (0, 0), 0⟩ = .ok wy →
      blockOut (p := P) ⟨(u, s) :: (v, t) :: List.replicate (K - 2) (0, 0), 0⟩ = .ok wxy →
      blockOut (p := P) ⟨(v, t) :: List.replicate (K - 1) (0, 0), wx⟩ = .ok wl →
      blockOut (p := P) ⟨(u, s) :: List.replicate (K - 1) (0, 0), wy⟩ = .ok wg →
      Good wx → Good wy → Good wxy → Good wl → Good wg →
      ∀ (ρ : Sched) (pρ : List Kind), WF K x y ρ →
        (ρ.map (kindOf x y)).filter (· != .e) = pρ → pρ ∈ pairPatterns →
        chainOut (P) (wfun K neab eAlignMin x y u v) (wfun K neab eAlignMin x y s t) 0 ρ =
          .ok (if pρ = [.xy] then wxy else if pρ = [.x, .y] then wl else wg) := by
    intro u v s t wx wy wxy wl wg ht hs f₁ f₂ f₃ f₄ f₅ k₁ k₂ k₃ k₄ k₅ ρ pρ hwf hp hm
    have r₁ := runKinds_single K neab eAlignMin (canon_x K neab eAlignMin x y hxy u v s t) f₁
    have r₂ := runKinds_single K neab eAlignMin (canon_y K neab eAlignMin x y hxy u v s t) f₂
    have r₃ := runKinds_single K neab eAlignMin (canon_xy K neab eAlignMin x y hxy u v s t) f₃
    have r₄ := runKinds_single K neab eAlignMin (canon_y K neab eAlignMin x y hxy u v s t) f₄
    have r₅ := runKinds_single K neab eAlignMin (canon_x K neab eAlignMin x y hxy u v s t) f₅
    rw [chain_value K neab eAlignMin hfl hK _ _ x y hxy (hA u v) (hB s t hs ht) hz ρ hwf pρ hp hm
      wx wy wxy wl wg r₁ r₂ r₃ r₄ r₅ k₁ k₂ k₃ k₄ k₅]
    simp only [pairPatterns, List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl | rfl
    · simpa using r₃
    · simp only [runKinds_step r₁, r₄]; simp
    · simp only [runKinds_step r₂, r₅]; simp
  have V := val ax ay bx by_ vx vy vxy vlt vgt hfin.2.1 hfin.1 e₁ e₂ e₃ e₄ e₅ g₁ g₂ g₃ g₄ g₅
  have W := val ay ax by_ bx vy vx vxy vgt vlt hfin.1 hfin.2.1 e₂ e₁ e₃' e₅ e₄ g₂ g₁ g₃ g₅ g₄
  have hwfun : ∀ (u v : (P).Word), wfun K neab eAlignMin x y u v = wfun K neab eAlignMin x y u v := fun _ _ => rfl
  simp only [pairPatterns, List.mem_cons, List.mem_nil_iff, or_false] at hmσ hmτ
  -- pick the assignment that separates the two patterns
  by_cases hsepO : (if pσ = [.xy] then vxy else if pσ = [.x, .y] then vlt else vgt) ≠
      (if pτ = [.xy] then vxy else if pτ = [.x, .y] then vlt else vgt)
  · refine ⟨wfun K neab eAlignMin x y ax ay, wfun K neab eAlignMin x y bx by_, hB _ _ hfin.1 hfin.2.1,
      hA _ _, ?_⟩
    rw [V σ pσ hσ hpσ (by simp [pairPatterns]; exact hmσ), V τ pτ hτ hpτ (by simp [pairPatterns]; exact hmτ)]
    intro h; exact hsepO (Except.ok.inj h)
  · refine ⟨wfun K neab eAlignMin x y ay ax, wfun K neab eAlignMin x y by_ bx, hB _ _ hfin.2.1 hfin.1,
      hA _ _, ?_⟩
    rw [W σ pσ hσ hpσ (by simp [pairPatterns]; exact hmσ), W τ pτ hτ hpτ (by simp [pairPatterns]; exact hmτ)]
    intro h
    have h' := Except.ok.inj h
    apply hsepO
    rcases hmσ with rfl | rfl | rfl <;> rcases hmτ with rfl | rfl | rfl <;>
      simp_all

end Witness


/-! ## The three Tensor Core generations (fp16) -/

theorem decode_zero (K neab : ℕ) (eAlignMin : Option ℤ) :
    ∃ z : Decoded, (fp16Fp32Model K neab eAlignMin).decode 0 = some z ∧ z.significand = 0 :=
  ⟨⟨0, 0, 0⟩, by show (classify fp16 0).finite = some _; decide +kernel, rfl⟩

/-- V100 (`K = 4`, no extra alignment bits): two chains that hold two products in different
patterns differ on some input. -/
theorem v100_complete_pair (σ τ : Sched) (x y : ℕ) (hxy : x ≠ y) (hσ : WF 4 x y σ)
    (hτ : WF 4 x y τ) (pσ pτ : List Kind)
    (hpσ : (σ.map (kindOf x y)).filter (· != .e) = pσ)
    (hpτ : (τ.map (kindOf x y)).filter (· != .e) = pτ)
    (hmσ : pσ ∈ pairPatterns) (hmτ : pτ ∈ pairPatterns) (hne : pσ ≠ pτ) :
    ∃ A B : ℕ → (fp16Fp32Model 4 0 none).Word,
      (∀ i, ((fp16Fp32Model 4 0 none).decode (B i)).isSome) ∧ (∀ i, i ≠ x → i ≠ y → A i = 0) ∧
      chainOut (fp16Fp32Model 4 0 none) A B 0 σ ≠ chainOut (fp16Fp32Model 4 0 none) A B 0 τ :=
  complete_pair 4 0 none (by simp) (by decide) (decode_zero 4 0 none) 0x1edc 0x1cd3 0x7add 0x69
    (by decide +kernel) 0x38045d50 0x3eb42940 0x3eb42d60 0x3eb42d60 0x3eb42d62
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    σ τ x y hxy hσ hτ pσ pτ hpσ hpτ hmσ hmτ hne

/-- A100 (`K = 8`, one extra alignment bit, minimum alignment exponent `−132`). -/
theorem a100_complete_pair (σ τ : Sched) (x y : ℕ) (hxy : x ≠ y) (hσ : WF 8 x y σ)
    (hτ : WF 8 x y τ) (pσ pτ : List Kind)
    (hpσ : (σ.map (kindOf x y)).filter (· != .e) = pσ)
    (hpτ : (τ.map (kindOf x y)).filter (· != .e) = pτ)
    (hmσ : pσ ∈ pairPatterns) (hmτ : pτ ∈ pairPatterns) (hne : pσ ≠ pτ) :
    ∃ A B : ℕ → (fp16Fp32Model 8 1 (some (-132))).Word,
      (∀ i, ((fp16Fp32Model 8 1 (some (-132))).decode (B i)).isSome) ∧
      (∀ i, i ≠ x → i ≠ y → A i = 0) ∧
      chainOut (fp16Fp32Model 8 1 (some (-132))) A B 0 σ ≠
        chainOut (fp16Fp32Model 8 1 (some (-132))) A B 0 τ :=
  complete_pair 8 1 (some (-132)) (by simp) (by decide) (decode_zero 8 1 (some (-132)))
    0x1edc 0x1cd3 0x7add 0x69
    (by decide +kernel) 0x38045d50 0x3eb42940 0x3eb42d60 0x3eb42d60 0x3eb42d62
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    σ τ x y hxy hσ hτ pσ pτ hpσ hpτ hmσ hmτ hne

/-- H100 (`K = 16`, two extra alignment bits, minimum alignment exponent `−133`). -/
theorem h100_complete_pair (σ τ : Sched) (x y : ℕ) (hxy : x ≠ y) (hσ : WF 16 x y σ)
    (hτ : WF 16 x y τ) (pσ pτ : List Kind)
    (hpσ : (σ.map (kindOf x y)).filter (· != .e) = pσ)
    (hpτ : (τ.map (kindOf x y)).filter (· != .e) = pτ)
    (hmσ : pσ ∈ pairPatterns) (hmτ : pτ ∈ pairPatterns) (hne : pσ ≠ pτ) :
    ∃ A B : ℕ → (fp16Fp32Model 16 2 (some (-133))).Word,
      (∀ i, ((fp16Fp32Model 16 2 (some (-133))).decode (B i)).isSome) ∧
      (∀ i, i ≠ x → i ≠ y → A i = 0) ∧
      chainOut (fp16Fp32Model 16 2 (some (-133))) A B 0 σ ≠
        chainOut (fp16Fp32Model 16 2 (some (-133))) A B 0 τ :=
  complete_pair 16 2 (some (-133)) (by simp) (by decide) (decode_zero 16 2 (some (-133)))
    0x52 0x6587 0xba7 0x3ff9
    (by decide +kernel) 0x3be29f00 0x39f409bc 0x3bf1df98 0x3bf1df9b 0x3bf1df98
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    σ τ x y hxy hσ hτ pσ pτ hpσ hpτ hmσ hmτ hne

end MMAlgebra.TC
