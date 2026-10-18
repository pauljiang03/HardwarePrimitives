import MatrixCore.MC.ProductMonotonicity

/-! # When larger products cannot lower the output

`MatrixCore.MC.ProductMonotonicity` gives, on CDNA 2 and CDNA 3, blocks with the same `c` and
every product at least as large whose output is smaller. Each of these witnesses needs the one
stage of its configuration that is not monotone in the products.

* CDNA 3 (Algorithms 1 and 2). While the alignment exponents stay the same (`e_max`, and with
  odd/even grouping the exponents of both groups), every stage is monotone: the truncation of each
  product onto a fixed grid, the RD of the group sums to a fixed exponent, the late accumulation
  of `c` for a fixed `e_max`, and the final RNE. For the same `c`, larger products then never give
  a smaller output (`aligned_product_monotone`), so a product increase lowers the output only if
  it changes an alignment exponent (`aligned_nonmonotone_alignment_changes`).
* CDNA 2. Every `fl{·}` is monotone, with or without the flushing of subnormal results, and so is
  every pairwise sum and the addition of `c`. When no operand is subnormal (none is flushed to
  zero before the products are formed), larger products never give a smaller output
  (`pairwise_product_monotone`): flushing the operands is the only cause. -/

namespace MatrixCore

/-! ## Lists compared position by position -/

/-- `R` relates the entries at each position of two lists of the same length. -/
inductive ListRel (R : α → β → Prop) : List α → List β → Prop
  | nil : ListRel R [] []
  | cons {a : α} {b : β} {as : List α} {bs : List β} :
      R a b → ListRel R as bs → ListRel R (a :: as) (b :: bs)

namespace ListRel

/-- Related lists have the same length. -/
theorem length_eq {R : α → β → Prop} {l : List α} {l' : List β} (h : ListRel R l l') :
    l.length = l'.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

/-- A relation implied by another relates the lists the other relates. -/
theorem imp {R S : α → β → Prop} (hRS : ∀ a b, R a b → S a b) {l : List α} {l' : List β}
    (h : ListRel R l l') : ListRel S l l' := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact .cons (hRS _ _ hab) ih

/-- A reflexive relation relates every list with itself. -/
theorem refl {R : α → α → Prop} (hR : ∀ a, R a a) : ∀ l : List α, ListRel R l l
  | [] => .nil
  | a :: l => .cons (hR a) (refl hR l)

/-- Relating the entries after `f` and `g` relates the mapped lists. -/
theorem map {R : γ → δ → Prop} {f : α → γ} {g : β → δ} {l : List α} {l' : List β}
    (h : ListRel (fun a b => R (f a) (g b)) l l') : ListRel R (l.map f) (l'.map g) := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact .cons hab ih

/-- Related mapped lists have their entries related after the maps. -/
theorem of_map {R : γ → δ → Prop} {f : α → γ} {g : β → δ} :
    ∀ {l : List α} {l' : List β}, ListRel R (l.map f) (l'.map g) →
      ListRel (fun a b => R (f a) (g b)) l l'
  | [], [], _ => .nil
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | _ :: _, _ :: _, h => by
    simp only [List.map_cons] at h
    cases h with
    | cons hab hs => exact .cons hab (of_map hs)

/-- The first `n` entries of related lists are related. -/
theorem take {R : α → β → Prop} {l : List α} {l' : List β} (h : ListRel R l l') (n : ℕ) :
    ListRel R (l.take n) (l'.take n) := by
  induction h generalizing n with
  | nil => simp only [List.take_nil]; exact .nil
  | cons hab _ ih =>
    cases n with
    | zero => simp only [List.take_zero]; exact .nil
    | succ n => simp only [List.take_succ_cons]; exact .cons hab (ih n)

/-- The entries after the first `n` of related lists are related. -/
theorem drop {R : α → β → Prop} {l : List α} {l' : List β} (h : ListRel R l l') (n : ℕ) :
    ListRel R (l.drop n) (l'.drop n) := by
  induction h generalizing n with
  | nil => simp only [List.drop_nil]; exact .nil
  | cons hab hs ih =>
    cases n with
    | zero => simp only [List.drop_zero]; exact .cons hab hs
    | succ n => simp only [List.drop_succ_cons]; exact ih n

/-- A list with every entry at most the corresponding entry of another has at most its sum. -/
theorem sumQ_le {xs ys : List ℚ} (h : ListRel (· ≤ ·) xs ys) : sumQ xs ≤ sumQ ys := by
  induction h with
  | nil => exact Rat.le_refl
  | cons hab _ ih => simp only [sumQ]; grind

end ListRel

/-- Adding an entry in front makes it the first odd-indexed entry and turns the odd positions
of the rest into the even ones. -/
theorem oddIndexed_evenIndexed_cons : ∀ (a : α) (l : List α),
    oddIndexed (a :: l) = a :: evenIndexed l ∧ evenIndexed (a :: l) = oddIndexed l
  | _, [] => by simp [oddIndexed, evenIndexed]
  | _, [_] => by simp [oddIndexed, evenIndexed]
  | _, _ :: z :: zs => by
    obtain ⟨h1, h2⟩ := oddIndexed_evenIndexed_cons z zs
    simp only [oddIndexed, evenIndexed]
    exact ⟨by rw [h1], by rw [h2]⟩

/-- Odd and even positions of related lists are related. -/
theorem ListRel.oddEven {R : α → β → Prop} {l : List α} {l' : List β} (h : ListRel R l l') :
    ListRel R (oddIndexed l) (oddIndexed l') ∧ ListRel R (evenIndexed l) (evenIndexed l') := by
  induction h with
  | nil => exact ⟨.nil, .nil⟩
  | @cons a b as bs hab _ ih =>
    rw [(oddIndexed_evenIndexed_cons a as).1, (oddIndexed_evenIndexed_cons b bs).1,
      (oddIndexed_evenIndexed_cons a as).2, (oddIndexed_evenIndexed_cons b bs).2]
    exact ⟨.cons hab ih.2, ih.1⟩

/-! ## The products of a block and of its operand words -/

/-- Lists of the same length whose zipped pairs are all ordered are ordered position by
position. -/
theorem listRel_of_all : ∀ (l l' : List ℚ), l.length = l'.length →
    (l.zip l').all (fun q => decide (q.1 ≤ q.2)) = true → ListRel (· ≤ ·) l l'
  | [], [], _, _ => .nil
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | x :: xs, y :: ys, hl, h => by
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .cons h.1 (listRel_of_all xs ys (by simpa using hl) h.2)

/-- `productsLE` compares the exact products position by position. -/
theorem productsLE_listRel {P : Model} {x x' : BlockInput P} (h : productsLE x x' = true) :
    ListRel (· ≤ ·) (productValues P x.a x.b) (productValues P x'.a x'.b) := by
  unfold productsLE at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact listRel_of_all _ _ h.1 h.2

/-- The values of the products of the decoded operands are the products of the operand
words' values. -/
theorem mapM_productValues {P : Model} : ∀ (xa : List P.a.Word) (xb : List P.b.Word)
    (A B : List Unpacked), xa.mapM (fun w => (P.a.read w).toFinite) = some A →
    xb.mapM (fun w => (P.b.read w).toFinite) = some B →
    (List.zipWith Unpacked.mul A B).map Unpacked.value = productValues P xa xb
  | [], xb, A, B, ha, _ => by
    simp at ha; subst ha; simp [productValues]
  | _ :: _, [], A, B, _, hb => by
    simp at hb; subst hb; cases A <;> simp [productValues]
  | x :: xs, y :: ys, A, B, ha, hb => by
    simp only [List.mapM_cons] at ha hb
    cases hx : (P.a.read x).toFinite with
    | none => rw [hx] at ha; simp at ha
    | some u =>
      cases hxs : xs.mapM (fun w => (P.a.read w).toFinite) with
      | none => rw [hx, hxs] at ha; simp at ha
      | some us =>
        cases hy : (P.b.read y).toFinite with
        | none => rw [hy] at hb; simp at hb
        | some v =>
          cases hys : ys.mapM (fun w => (P.b.read w).toFinite) with
          | none => rw [hy, hys] at hb; simp at hb
          | some vs =>
            rw [hx, hxs] at ha; rw [hy, hys] at hb
            simp at ha hb; subst ha; subst hb
            have ih := mapM_productValues xs ys us vs hxs hys
            unfold productValues at ih ⊢
            simp only [List.zipWith_cons_cons, List.map_cons, ih, Unpacked.value_mul,
              InputFormat.wordValue, hx, hy, Option.map_some, Option.getD_some]

/-- The exact products of an accepted block are the products of its operand words. -/
theorem evalBlock_productValues {P : Model} {x : BlockInput P} {t : BlockTrace P}
    (h : evalBlock x = .ok t) : t.prepared.p.map Unpacked.value = productValues P x.a x.b := by
  have hp := (evalBlock_ok h).2.2.1
  unfold prepare at hp
  cases hA : x.a.mapM fun w => (P.a.read w).toFinite <;> rw [hA] at hp <;> simp at hp
  cases hB : x.b.mapM fun w => (P.b.read w).toFinite <;> rw [hB] at hp <;> simp at hp
  cases hC : (fp32.decode x.c).toFinite <;> rw [hC] at hp <;> simp at hp
  rename_i A B _
  rw [← hp]
  exact mapM_productValues x.a x.b A B hA hB

/-- `productsLE` of two accepted blocks compares their products position by position. -/
theorem evalBlock_productsLE {P : Model} {x x' : BlockInput P} {t t' : BlockTrace P}
    (h : evalBlock x = .ok t) (h' : evalBlock x' = .ok t') (hp : productsLE x x' = true) :
    ListRel (fun p q : Unpacked => p.value ≤ q.value) t.prepared.p t'.prepared.p := by
  have := productsLE_listRel hp
  rw [← evalBlock_productValues h, ← evalBlock_productValues h'] at this
  exact ListRel.of_map this

/-- Accepted blocks with the same `c` word decode the same `c`. -/
theorem evalBlock_same_c {P : Model} {x x' : BlockInput P} {t t' : BlockTrace P}
    (h : evalBlock x = .ok t) (h' : evalBlock x' = .ok t') (hc : x.c = x'.c) :
    t.prepared.c = t'.prepared.c := by
  have e1 := prepare_c (evalBlock_ok h).2.2.1
  have e2 := prepare_c (evalBlock_ok h').2.2.1
  rw [hc, e2] at e1
  exact (Option.some.inj e1).symm

/-! ## CDNA 3 -/

/-- Truncation onto a fixed grid is monotone. -/
theorem truncGrid_mono {x y : ℚ} (g : ℤ) (h : x ≤ y) : truncGrid x g ≤ truncGrid y g := by
  have bx := truncGrid_bounds x g
  have byy := truncGrid_bounds y g
  by_cases hx : x < 0
  · by_cases hy : y < 0
    · unfold truncGrid
      simp only [hx, hy, ↓reduceIte]
      have := rdGrid_mono g (show -y ≤ -x by grind)
      unfold rdGrid at this
      grind
    · have h1 := (bx.2.2.2 (Rat.le_of_lt hx)).2
      have h2 := (byy.2.2.1 (by grind)).1
      grind
  · have hy : ¬ y < 0 := by grind
    unfold truncGrid
    simp only [hx, hy, ↓reduceIte]
    exact rdGrid_mono g h

/-- The exponents to which the products are aligned: `e_max` of all products, or with odd/even
grouping (Algorithm 2) the largest exponents of the odd- and of the even-indexed products. -/
def alignmentExponents (P : Model) (ps : List Unpacked) : List (Option ℤ) :=
  match P.accumulation with
  | .oddEvenGrouping => [maxExp (oddIndexed ps), maxExp (evenIndexed ps)]
  | _ => [maxExp ps]

/-- With the same `e_max`, the aligned sum `S_{p_i,sum}` is monotone in the products. -/
theorem alignedSum_mono (padding : ℕ) {ps qs : List Unpacked}
    (h : ListRel (fun p q : Unpacked => p.value ≤ q.value) ps qs) (he : maxExp ps = maxExp qs) :
    (alignedSum padding ps).1 = (alignedSum padding qs).1 ∧
      (alignedSum padding ps).2 ≤ (alignedSum padding qs).2 := by
  unfold alignedSum
  rw [he]
  cases maxExp qs with
  | none => exact ⟨rfl, Rat.le_refl⟩
  | some e =>
    refine ⟨rfl, ?_⟩
    apply ListRel.sumQ_le
    apply ListRel.map
    exact h.imp fun p q hpq => truncGrid_mono _ hpq

/-- With the same alignment exponents, the product sum of Algorithms 1 and 2 keeps its exponent
and is monotone in the products. -/
theorem productSum_mono (P : Model) {ps qs : List Unpacked}
    (h : ListRel (fun p q : Unpacked => p.value ≤ q.value) ps qs)
    (he : alignmentExponents P ps = alignmentExponents P qs) :
    (productSum P ps).1 = (productSum P qs).1 ∧ (productSum P ps).2 ≤ (productSum P qs).2 := by
  unfold productSum
  unfold alignmentExponents at he
  cases hacc : P.accumulation <;> simp only [hacc] at he ⊢
  case oddEvenGrouping =>
    simp only [List.cons.injEq, and_true] at he
    obtain ⟨o1, o2⟩ := alignedSum_mono P.padding h.oddEven.1 he.1
    obtain ⟨e1, e2⟩ := alignedSum_mono P.padding h.oddEven.2 he.2
    rw [o1, e1]
    cases joinExp (alignedSum P.padding (oddIndexed qs)).1 (alignedSum P.padding (evenIndexed qs)).1 with
    | none => exact ⟨rfl, Rat.le_refl⟩
    | some e =>
      refine ⟨rfl, ?_⟩
      have := rdGrid_mono (e - ((23 + P.padding : ℕ) : ℤ)) o2
      have := rdGrid_mono (e - ((23 + P.padding : ℕ) : ℤ)) e2
      show rdGrid _ _ + rdGrid _ _ ≤ rdGrid _ _ + rdGrid _ _
      grind
  all_goals
    simp only [List.cons.injEq, and_true] at he
    exact alignedSum_mono P.padding h he

/-- For a fixed `e_max` and `c`, the late accumulation of `c` is monotone in `S_{p_i,sum}`. -/
theorem lateSum_mono_sum (P : Model) (eMax : Option ℤ) {S S' : ℚ} (c : Unpacked) (h : S ≤ S') :
    lateSum P eMax S c ≤ lateSum P eMax S' c := by
  unfold lateSum shiftedSum
  cases cExp P c with
  | none => exact h
  | some eC =>
    have hsh : normalizeRD P.late.accMantissaBits (rdMantissa S eC P.late.sumMantissaBits + c.value) ≤
        normalizeRD P.late.accMantissaBits (rdMantissa S' eC P.late.sumMantissaBits + c.value) := by
      apply normalizeRD_mono
      have := rdGrid_mono (eC - (P.late.sumMantissaBits : ℤ)) h
      grind
    cases eMax with
    | none => exact hsh
    | some e =>
      simp only
      split
      · grind
      · exact hsh

/-- With the same `c` and the same alignment exponents, `S_acc` of Algorithms 1 and 2 is monotone
in the products. -/
theorem alignedAccumulation_product_mono (P : Model) {x x' : Prepared} (hc : x.c = x'.c)
    (h : ListRel (fun p q : Unpacked => p.value ≤ q.value) x.p x'.p)
    (he : alignmentExponents P x.p = alignmentExponents P x'.p) :
    alignedAccumulation P x ≤ alignedAccumulation P x' := by
  obtain ⟨h1, h2⟩ := productSum_mono P h he
  unfold alignedAccumulation
  simp only
  rw [h1, hc]
  exact lateSum_mono_sum P _ _ h2

/-- On Algorithms 1 and 2, two accepted blocks with the same `c`, every product of the second at
least the corresponding product of the first, and the same alignment exponents have `S_acc` in
the same order. -/
theorem aligned_sAcc_monotone {P : Model}
    (hacc : P.accumulation = .globalAlignment ∨ P.accumulation = .oddEvenGrouping)
    {x x' : BlockInput P} {t t' : BlockTrace P} (h : evalBlock x = .ok t)
    (h' : evalBlock x' = .ok t') (hp : productsLE x x' = true) (hc : x.c = x'.c)
    (he : alignmentExponents P t.prepared.p = alignmentExponents P t'.prepared.p) :
    t.sAcc ≤ t'.sAcc := by
  rw [accumulate_aligned hacc (evalBlock_ok h).2.2.2.1,
    accumulate_aligned hacc (evalBlock_ok h').2.2.2.1]
  exact alignedAccumulation_product_mono P (evalBlock_same_c h h' hc) (evalBlock_productsLE h h' hp) he

/-- **CDNA 3 is monotone in the products while the alignment exponents stay the same.** On
Algorithms 1 and 2, if two accepted blocks have the same `c`, every product of the second is at
least the corresponding product of the first, and the alignment exponents are the same (`e_max`,
or both group exponents with odd/even grouping), then the second output is at least the first. -/
theorem aligned_product_monotone {P : Model}
    (hacc : P.accumulation = .globalAlignment ∨ P.accumulation = .oddEvenGrouping)
    {x x' : BlockInput P} {t t' : BlockTrace P} (h : evalBlock x = .ok t)
    (h' : evalBlock x' = .ok t') (hp : productsLE x x' = true) (hc : x.c = x'.c)
    (he : alignmentExponents P t.prepared.p = alignmentExponents P t'.prepared.p) :
    wordValue t.d ≤ wordValue t'.d :=
  fl32_mono (evalBlock_ok h).2.2.2.2 (evalBlock_ok h').2.2.2.2 (aligned_sAcc_monotone hacc h h' hp hc he)

/-- A block whose `blockBits` returns a word has an accepted trace with that output. -/
theorem blockBits_traces {P : Model} {x : BlockInput P} {d : F32} (h : blockBits x = .ok d) :
    ∃ t, evalBlock x = .ok t ∧ t.d = d := by
  unfold blockBits at h
  cases ht : evalBlock x with
  | error e => rw [ht] at h; simp [Except.map] at h
  | ok t =>
    rw [ht] at h
    simp only [Except.map, Except.ok.injEq] at h
    exact ⟨t, rfl, h⟩

/-- **On CDNA 3 a product increase lowers the output only if it changes an alignment exponent.**
In every pair of blocks with the same `c`, products at least as large, and a smaller output, the
alignment exponents of the two blocks differ (`e_max`, or a group exponent with odd/even
grouping). -/
theorem aligned_nonmonotone_alignment_changes {P : Model}
    (hacc : P.accumulation = .globalAlignment ∨ P.accumulation = .oddEvenGrouping)
    {x x' : BlockInput P} (hn : ProductNonmonotone x x') :
    ∃ t t', evalBlock x = .ok t ∧ evalBlock x' = .ok t' ∧
      alignmentExponents P t.prepared.p ≠ alignmentExponents P t'.prepared.p := by
  obtain ⟨hp, hc, d, d', hd, hd', hlt⟩ := hn
  obtain ⟨t, ht, rfl⟩ := blockBits_traces hd
  obtain ⟨t', ht', rfl⟩ := blockBits_traces hd'
  refine ⟨t, t', ht, ht', fun he => ?_⟩
  exact Rat.not_le.mpr hlt (aligned_product_monotone hacc ht ht' hp hc he)

/-! ### The CDNA 3 models -/

/-- CDNA 3 fp16: with the same `c` and `e_max`, larger products never give a smaller output. -/
theorem cdna3F16_product_monotone {x x' : BlockInput cdna3F16} {t t' : BlockTrace cdna3F16}
    (h : evalBlock x = .ok t) (h' : evalBlock x' = .ok t') (hp : productsLE x x' = true)
    (hc : x.c = x'.c) (he : maxExp t.prepared.p = maxExp t'.prepared.p) :
    wordValue t.d ≤ wordValue t'.d :=
  aligned_product_monotone (Or.inl rfl) h h' hp hc (by
    show [maxExp t.prepared.p] = [maxExp t'.prepared.p]; rw [he])

/-- CDNA 3 bf16: with the same `c` and `e_max`, larger products never give a smaller output. -/
theorem cdna3BF16_product_monotone {x x' : BlockInput cdna3BF16} {t t' : BlockTrace cdna3BF16}
    (h : evalBlock x = .ok t) (h' : evalBlock x' = .ok t') (hp : productsLE x x' = true)
    (hc : x.c = x'.c) (he : maxExp t.prepared.p = maxExp t'.prepared.p) :
    wordValue t.d ≤ wordValue t'.d :=
  aligned_product_monotone (Or.inl rfl) h h' hp hc (by
    show [maxExp t.prepared.p] = [maxExp t'.prepared.p]; rw [he])

/-- CDNA 3 XF32: with the same `c` and `e_max`, larger products never give a smaller output. -/
theorem cdna3XF32_product_monotone {x x' : BlockInput cdna3XF32} {t t' : BlockTrace cdna3XF32}
    (h : evalBlock x = .ok t) (h' : evalBlock x' = .ok t') (hp : productsLE x x' = true)
    (hc : x.c = x'.c) (he : maxExp t.prepared.p = maxExp t'.prepared.p) :
    wordValue t.d ≤ wordValue t'.d :=
  aligned_product_monotone (Or.inl rfl) h h' hp hc (by
    show [maxExp t.prepared.p] = [maxExp t'.prepared.p]; rw [he])

/-- CDNA 3 binary8 (Algorithm 2), every combination of fp8 formats: with the same `c` and the
same exponents of the odd- and of the even-indexed group, larger products never give a smaller
output. -/
theorem cdna3FP8_product_monotone (fa fb : Format) {x x' : BlockInput (cdna3FP8 fa fb)}
    {t t' : BlockTrace (cdna3FP8 fa fb)} (h : evalBlock x = .ok t) (h' : evalBlock x' = .ok t')
    (hp : productsLE x x' = true) (hc : x.c = x'.c)
    (ho : maxExp (oddIndexed t.prepared.p) = maxExp (oddIndexed t'.prepared.p))
    (he : maxExp (evenIndexed t.prepared.p) = maxExp (evenIndexed t'.prepared.p)) :
    wordValue t.d ≤ wordValue t'.d :=
  aligned_product_monotone (Or.inr rfl) h h' hp hc (by
    show [maxExp (oddIndexed t.prepared.p), maxExp (evenIndexed t.prepared.p)] =
      [maxExp (oddIndexed t'.prepared.p), maxExp (evenIndexed t'.prepared.p)]
    rw [ho, he])

/-! ## CDNA 2 -/

/-- Every operand of `a` and `b` is zero or normal: none is subnormal, so flushing changes none. -/
def Prepared.NormalOperands (x : Prepared) : Prop := ∀ u ∈ x.a ++ x.b, u.m = 0 ∨ 2 ^ u.t ≤ u.m

/-- Flushing keeps a zero or normal value. -/
theorem Unpacked.flush_of_normal {u : Unpacked} (h : u.m = 0 ∨ 2 ^ u.t ≤ u.m) : u.flush = u := by
  unfold Unpacked.flush
  split
  · rename_i hlt
    rcases h with h | h
    · cases u; simp_all
    · omega
  · rfl

/-- Flushing keeps a list of zero or normal values. -/
theorem map_flush_of_normal : ∀ l : List Unpacked, (∀ u ∈ l, u.m = 0 ∨ 2 ^ u.t ≤ u.m) →
    l.map Unpacked.flush = l
  | [], _ => rfl
  | u :: l, h => by
    simp only [List.map_cons]
    rw [Unpacked.flush_of_normal (h u (by simp)),
      map_flush_of_normal l (fun v hv => h v (by simp [hv]))]

/-- Without subnormal operands, flushing leaves the products unchanged. -/
theorem Prepared.flushed_p {x : Prepared} (h : x.NormalOperands) : x.flushed.p = x.p := by
  unfold Prepared.flushed Prepared.p
  simp only
  rw [map_flush_of_normal x.a (fun u hu => h u (List.mem_append_left _ hu)),
    map_flush_of_normal x.b (fun u hu => h u (List.mem_append_right _ hu))]

/-- The conversion of the products to binary32 is monotone. -/
theorem mapM_flValue_mono (ftz : Bool) : ∀ {l l' : List Unpacked} {ps ps' : List ℚ},
    ListRel (fun p q : Unpacked => p.value ≤ q.value) l l' →
    l.mapM (fun p => flValue ftz p.value) = some ps →
    l'.mapM (fun p => flValue ftz p.value) = some ps' → ListRel (· ≤ ·) ps ps'
  | [], [], ps, ps', _, h, h' => by
    simp at h h'; subst h; subst h'; exact .nil
  | [], _ :: _, _, _, hr, _, _ => by cases hr
  | _ :: _, [], _, _, hr, _, _ => by cases hr
  | p :: l, q :: l', ps, ps', hr, h, h' => by
    cases hr with
    | cons hpq hl =>
      simp only [List.mapM_cons] at h h'
      cases hp : flValue ftz p.value with
      | none => rw [hp] at h; simp at h
      | some u =>
        cases hq : flValue ftz q.value with
        | none => rw [hq] at h'; simp at h'
        | some v =>
          cases hls : l.mapM (fun p => flValue ftz p.value) with
          | none => rw [hp, hls] at h; simp at h
          | some us =>
            cases hls' : l'.mapM (fun p => flValue ftz p.value) with
            | none => rw [hq, hls'] at h'; simp at h'
            | some vs =>
              rw [hp, hls] at h; rw [hq, hls'] at h'
              simp at h h'; subst h; subst h'
              exact .cons (flValue_mono hp hq hpq) (mapM_flValue_mono ftz hl hls hls')

/-- The pairwise sum of a group is monotone in its terms. -/
theorem pairwiseGroupSum_mono (ftz : Bool) : ∀ (depth : ℕ) {xs ys : List ℚ} {u v : ℚ},
    ListRel (· ≤ ·) xs ys → pairwiseGroupSum ftz depth xs = some u →
    pairwiseGroupSum ftz depth ys = some v → u ≤ v
  | _, [], [], u, v, _, h, h' => by
    simp only [pairwiseGroupSum, Option.some.injEq] at h h'; subst h; subst h'; exact Rat.le_refl
  | _, [], _ :: _, _, _, hr, _, _ => by cases hr
  | _, _ :: _, [], _, _, hr, _, _ => by cases hr
  | _, [x], [y], u, v, hr, h, h' => by
    cases hr with
    | cons hxy _ =>
      simp only [pairwiseGroupSum, Option.some.injEq] at h h'; subst h; subst h'; exact hxy
  | _, [_], _ :: _ :: _, _, _, hr, _, _ => by cases hr with | cons _ hs => cases hs
  | _, _ :: _ :: _, [_], _, _, hr, _, _ => by cases hr with | cons _ hs => cases hs
  | 0, _ :: _ :: _, _ :: _ :: _, _, _, _, h, _ => by simp [pairwiseGroupSum] at h
  | depth + 1, x :: x2 :: xr, y :: y2 :: yr, u, v, hr, h, h' => by
    have hlen := hr.length_eq
    generalize hxs : x :: x2 :: xr = xs at h hr hlen
    generalize hys : y :: y2 :: yr = ys at h' hr hlen
    have hx : pairwiseGroupSum ftz (depth + 1) xs = (do
        let u ← pairwiseGroupSum ftz depth (xs.take (xs.length / 2))
        let v ← pairwiseGroupSum ftz depth (xs.drop (xs.length / 2))
        flValue ftz (u + v)) := by subst hxs; rfl
    have hy : pairwiseGroupSum ftz (depth + 1) ys = (do
        let u ← pairwiseGroupSum ftz depth (ys.take (ys.length / 2))
        let v ← pairwiseGroupSum ftz depth (ys.drop (ys.length / 2))
        flValue ftz (u + v)) := by subst hys; rfl
    rw [hx] at h
    rw [hy, ← hlen] at h'
    cases hu1 : pairwiseGroupSum ftz depth (xs.take (xs.length / 2)) with
    | none => rw [hu1] at h; simp at h
    | some u1 =>
      cases hu2 : pairwiseGroupSum ftz depth (xs.drop (xs.length / 2)) with
      | none => rw [hu1, hu2] at h; simp at h
      | some u2 =>
        cases hv1 : pairwiseGroupSum ftz depth (ys.take (xs.length / 2)) with
        | none => rw [hv1] at h'; simp at h'
        | some v1 =>
          cases hv2 : pairwiseGroupSum ftz depth (ys.drop (xs.length / 2)) with
          | none => rw [hv1, hv2] at h'; simp at h'
          | some v2 =>
            rw [hu1, hu2] at h; rw [hv1, hv2] at h'
            change flValue ftz (u1 + u2) = some u at h
            change flValue ftz (v1 + v2) = some v at h'
            have a1 := pairwiseGroupSum_mono ftz depth (hr.take _) hu1 hv1
            have a2 := pairwiseGroupSum_mono ftz depth (hr.drop _) hu2 hv2
            exact flValue_mono h h' (by grind)

/-- The stages of an accepted CDNA 2 accumulation: the products converted to binary32, their
pairwise sum `u`, and `S_acc = c + u` (with `c` flushed when subnormals are not supported). -/
theorem pairwiseSum_stages {P : Model} {x : Prepared} {s : ℚ} (h : pairwiseSum P x = some s) :
    ∃ ps u, (if P.subnormals then x else x.flushed).p.mapM
        (fun p => flValue (!P.subnormals) p.value) = some ps ∧
      pairwiseGroupSum (!P.subnormals) ps.length ps = some u ∧
      s = (if P.subnormals then x else x.flushed).c.value + u := by
  unfold pairwiseSum at h
  dsimp only at h
  generalize (if P.subnormals then x else x.flushed) = y at h ⊢
  cases hm : y.p.mapM fun p => flValue (!P.subnormals) p.value with
  | none => rw [hm] at h; simp at h
  | some ps =>
    rw [hm] at h
    cases ht : pairwiseGroupSum (!P.subnormals) ps.length ps with
    | none => simp [ht] at h
    | some u =>
      change (pairwiseGroupSum (!P.subnormals) ps.length ps).bind
        (fun t => some (y.c.value + t)) = some s at h
      rw [ht] at h
      simp only [Option.bind_some, Option.some.injEq] at h
      exact ⟨ps, u, rfl, ht, h.symm⟩

/-- **CDNA 2: flushing is the only cause.** On the pairwise-sum configuration, if no operand of
either block is subnormal, two accepted blocks with the same `c` and every product of the second
at least the corresponding product of the first give outputs in the same order. -/
theorem pairwise_product_monotone {P : Model} (hacc : P.accumulation = .pairWiseSum)
    {x x' : BlockInput P} {t t' : BlockTrace P} (h : evalBlock x = .ok t)
    (h' : evalBlock x' = .ok t') (hp : productsLE x x' = true) (hc : x.c = x'.c)
    (hn : t.prepared.NormalOperands) (hn' : t'.prepared.NormalOperands) :
    wordValue t.d ≤ wordValue t'.d := by
  apply fl32_mono (evalBlock_ok h).2.2.2.2 (evalBlock_ok h').2.2.2.2
  obtain ⟨ps, u, hm, hu, hs⟩ := pairwiseSum_stages (accumulate_pairwise hacc (evalBlock_ok h).2.2.2.1)
  obtain ⟨ps', u', hm', hu', hs'⟩ :=
    pairwiseSum_stages (accumulate_pairwise hacc (evalBlock_ok h').2.2.2.1)
  have hcc := evalBlock_same_c h h' hc
  have hrel := evalBlock_productsLE h h' hp
  have hpp : (if P.subnormals then t.prepared else t.prepared.flushed).p = t.prepared.p := by
    split
    · rfl
    · exact Prepared.flushed_p hn
  have hpp' : (if P.subnormals then t'.prepared else t'.prepared.flushed).p = t'.prepared.p := by
    split
    · rfl
    · exact Prepared.flushed_p hn'
  have hcv : (if P.subnormals then t.prepared else t.prepared.flushed).c.value =
      (if P.subnormals then t'.prepared else t'.prepared.flushed).c.value := by
    split <;> simp [Prepared.flushed, hcc]
  rw [hpp] at hm
  rw [hpp'] at hm'
  have hps := mapM_flValue_mono _ hrel hm hm'
  rw [hps.length_eq] at hu
  have := pairwiseGroupSum_mono _ _ hps hu hu'
  rw [hs, hs', hcv]
  grind

/-- CDNA 2 fp16: without subnormal operands, larger products never give a smaller output. -/
theorem cdna2F16_product_monotone {x x' : BlockInput cdna2F16} {t t' : BlockTrace cdna2F16}
    (h : evalBlock x = .ok t) (h' : evalBlock x' = .ok t') (hp : productsLE x x' = true)
    (hc : x.c = x'.c) (hn : t.prepared.NormalOperands) (hn' : t'.prepared.NormalOperands) :
    wordValue t.d ≤ wordValue t'.d :=
  pairwise_product_monotone rfl h h' hp hc hn hn'

/-- CDNA 2 bf16: without subnormal operands, larger products never give a smaller output. -/
theorem cdna2BF16_product_monotone {x x' : BlockInput cdna2BF16} {t t' : BlockTrace cdna2BF16}
    (h : evalBlock x = .ok t) (h' : evalBlock x' = .ok t') (hp : productsLE x x' = true)
    (hc : x.c = x'.c) (hn : t.prepared.NormalOperands) (hn' : t'.prepared.NormalOperands) :
    wordValue t.d ≤ wordValue t'.d :=
  pairwise_product_monotone rfl h h' hp hc hn hn'

/-- CDNA 2 bf16 `_1k`: without subnormal operands, larger products never give a smaller
output. -/
theorem cdna2BF16_1k_product_monotone {x x' : BlockInput cdna2BF16_1k}
    {t t' : BlockTrace cdna2BF16_1k} (h : evalBlock x = .ok t) (h' : evalBlock x' = .ok t')
    (hp : productsLE x x' = true) (hc : x.c = x'.c) (hn : t.prepared.NormalOperands)
    (hn' : t'.prepared.NormalOperands) : wordValue t.d ≤ wordValue t'.d :=
  pairwise_product_monotone rfl h h' hp hc hn hn'

end MatrixCore
