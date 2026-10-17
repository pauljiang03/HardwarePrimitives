import MMAlgebraMC.Bound
import MMAlgebraMC.PairwiseMC

/-! # The error contracts of CDNA 3 and CDNA 2

From the a-priori theorems of the AMD model (`MatrixCore.aligned_apriori`,
`MatrixCore.pairwise_apriori`), in terms of the accumulator bound `A` and the slots of a block:

* **CDNA 3** (`cdna3_block_le`): within `2^-23 (A + Σ|aᵢbᵢ|) + (n + 4)·2^-24·Σ expMag + 2^-149`, where
  `expMag` is 2 to the sum of the operands' exponents (at most `|aᵢbᵢ|` for normal operands), so
  `14u` per unit of input magnitude with normal operands;
* **CDNA 2** (`cdna2_block_le`): within `Σ subMag + 2^-126 + 2^-21 (A + Σ|aᵢbᵢ|) + 2^-120`, where
  `subMag` is the magnitude of a product with a subnormal operand (which CDNA 2 flushes), so `8u`
  per unit of input magnitude with normal operands, plus the flushed terms.

With binary32 addition these are `MMAlgebra.Contract`s (`cdna3Contract`, `cdna2Contract`), so the
structural bound and the divergence theorems hold on CDNA 3 and CDNA 2 (`cdna3_divergence`,
`cdna2_divergence`) as on SFMA and CDNA 1 (`cdna1_divergence`). -/

open MatrixCore Ozaki.MC

namespace MMAlgebra.MC

/-- 2 to the exponent of a nonzero product of two operand words (`0` otherwise). -/
def expMagMC (P : Model) (q : P.a.Word × P.b.Word) : ℚ :=
  match (P.a.read q.1).toFinite, (P.b.read q.2).toFinite with
  | some u, some v => if u.m * v.m = 0 then 0 else pow2 (u.e + v.e)
  | _, _ => 0

theorem expMagMC_nonneg (P : Model) (q : P.a.Word × P.b.Word) : 0 ≤ expMagMC P q := by
  unfold expMagMC
  split
  · split
    · exact Rat.le_refl
    · exact Rat.le_of_lt (pow2_pos _)
  · exact Rat.le_refl

theorem le_sum_mem {l : List ℚ} (hl : ∀ x ∈ l, 0 ≤ x) {y : ℚ} (hy : y ∈ l) : y ≤ l.sum := by
  induction l with
  | nil => simp at hy
  | cons x l ih =>
    simp only [List.sum_cons]
    have hnn : ∀ (l : List ℚ), (∀ x ∈ l, 0 ≤ x) → 0 ≤ l.sum := by
      intro l h
      induction l with
      | nil => simp
      | cons z l ihz =>
        simp only [List.sum_cons]
        have := h z (by simp); have := ihz (fun w hw => h w (by simp [hw])); grind
    have h1 := hl x (by simp)
    have h2 := hnn l (fun w hw => hl w (by simp [hw]))
    rcases List.mem_cons.mp hy with rfl | hy
    · grind
    · have := ih (fun w hw => hl w (by simp [hw])) hy; grind

theorem foldl_maxExpStep_mem : ∀ (ps : List Unpacked) (acc : Option ℤ) (e : ℤ),
    ps.foldl maxExpStep acc = some e → acc = some e ∨ ∃ p ∈ ps, p.m ≠ 0 ∧ p.e = e
  | [], acc, e, h => Or.inl h
  | p :: ps, acc, e, h => by
    simp only [List.foldl_cons] at h
    rcases foldl_maxExpStep_mem ps _ e h with h1 | ⟨q, hq, hm, he⟩
    · unfold maxExpStep at h1
      split at h1
      · left; exact h1
      · rename_i hm
        cases acc with
        | none => simp at h1; subst h1; right; exact ⟨p, by simp, hm, rfl⟩
        | some v =>
          simp only [Option.some.injEq] at h1
          rcases Int.le_total v p.e with hv | hv
          · rw [Int.max_eq_right hv] at h1; subst h1; right; exact ⟨p, by simp, hm, rfl⟩
          · rw [Int.max_eq_left hv] at h1; subst h1; left; rfl
    · right; exact ⟨q, List.mem_cons_of_mem _ hq, hm, he⟩

theorem maxExp_attained {ps : List Unpacked} {e : ℤ} (h : maxExp ps = some e) :
    ∃ p ∈ ps, p.m ≠ 0 ∧ p.e = e := by
  rcases foldl_maxExpStep_mem ps none e h with h1 | h1
  · cases h1
  · exact h1

theorem sumAbs_decPair {P : Model} :
    ∀ (qs : List (P.a.Word × P.b.Word)) (L : List (Unpacked × Unpacked)), qs.mapM (decPair P) = some L →
      (L.map fun q => absQ (q.1.mul q.2).value).sum = (qs.map fun q => Rat.abs ((mcMachine P).pval q)).sum
  | [], L, h => by simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h; subst h; rfl
  | q :: qs, L, h => by
    simp only [List.mapM_cons] at h
    cases hq : decPair P q with
    | none => simp [hq] at h
    | some uv =>
      cases hqs : qs.mapM (decPair P) with
      | none => simp [hq, hqs] at h
      | some L' =>
        simp only [hq, hqs, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        subst h
        simp only [List.map_cons, List.sum_cons, sumAbs_decPair qs L' hqs]
        congr 1
        obtain ⟨u, v⟩ := uv
        simp only [decPair] at hq
        cases hu : (P.a.read q.1).toFinite with
        | none => rw [hu] at hq; cases hq
        | some u' =>
          cases hv : (P.b.read q.2).toFinite with
          | none => rw [hu, hv] at hq; cases hq
          | some v' =>
            rw [hu, hv] at hq
            simp only [Option.bind_some, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hq
            obtain ⟨rfl, rfl⟩ := hq
            show absQ (u'.mul v').value = Rat.abs (P.a.wordValue q.1 * P.b.wordValue q.2)
            simp [InputFormat.wordValue, hu, hv, Unpacked.value_mul, absQ_eq]

theorem slotAbs_pairs {P : Model} (hz : (mcMachine P).pval (0, 0) = 0) :
    ∀ ps : List (Option (P.a.Word × P.b.Word)),
      (mcMachine P).slotAbs ps = ((slotPairs P ps).map fun q => Rat.abs ((mcMachine P).pval q)).sum
  | [] => rfl
  | o :: ps => by
    rw [(mcMachine P).slotAbs_cons, slotAbs_pairs hz ps]
    cases o with
    | none =>
      show Rat.abs 0 + ((slotPairs P ps).map fun q => Rat.abs ((mcMachine P).pval q)).sum =
        Rat.abs ((mcMachine P).pval (0, 0)) + ((slotPairs P ps).map fun q => Rat.abs ((mcMachine P).pval q)).sum
      rw [hz]
    | some q => rfl

theorem cdna3_pval_zero : (mcMachine cdna3F16).pval (0, 0) = 0 := by decide +kernel

/-- The decoded operands of an evaluated block, from its slot pairs. -/
theorem evalBlock_pairs {P : Model} {qs : List (P.a.Word × P.b.Word)} {d : F32} {t : BlockTrace P}
    (h : evalBlock (P := P) ⟨qs.map Prod.fst, qs.map Prod.snd, d⟩ = .ok t) :
    ∃ L C, qs.mapM (decPair P) = some L ∧ (binary32.decode d).toFinite = some C ∧
      t.prepared = ⟨L.map Prod.fst, L.map Prod.snd, C⟩ := by
  obtain ⟨_, _, hp, _, _⟩ := evalBlock_ok h
  rw [prepare_pairs] at hp
  cases hL : qs.mapM (decPair P) with
  | none => rw [hL] at hp; cases hp
  | some L =>
    rw [hL] at hp
    cases hC : (binary32.decode d).toFinite with
    | none => rw [hC] at hp; cases hp
    | some C =>
      rw [hC] at hp
      simp only [Option.bind_some, Option.map_some, Option.some.injEq] at hp
      exact ⟨L, C, rfl, rfl, hp.symm⟩

/-! ## CDNA 3 -/

theorem cdna3_late : LateModel cdna3F16 :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun n h => by simp [cdna3F16] at h, by decide⟩

/-- **The CDNA 3 block contract.** -/
theorem cdna3_block_le (d : F32) (ps : List (Option (cdna3F16.a.Word × cdna3F16.b.Word))) (o : F32)
    (A : ℚ) (hA : Rat.abs ((mcMachine cdna3F16).val d) ≤ A)
    (h : (mcMachine cdna3F16).block d ps = some o) :
    Rat.abs ((mcMachine cdna3F16).val o - ((mcMachine cdna3F16).val d + (mcMachine cdna3F16).slotVal ps)) ≤
      pow2 (-23) * (A + (mcMachine cdna3F16).slotAbs ps) +
        ((ps.length : ℚ) + 4) * (pow2 (-24) * ((slotPairs cdna3F16 ps).map (expMagMC cdna3F16)).sum) +
          pow2 (-149) := by
  have h' : (blockBits (P := cdna3F16) ⟨(slotPairs cdna3F16 ps).map Prod.fst,
      (slotPairs cdna3F16 ps).map Prod.snd, d⟩).toOption = some o := h
  unfold blockBits at h'
  cases ht : evalBlock (P := cdna3F16) ⟨(slotPairs cdna3F16 ps).map Prod.fst,
      (slotPairs cdna3F16 ps).map Prod.snd, d⟩ with
  | error e => rw [ht] at h'; simp [Except.map, Except.toOption] at h'
  | ok t =>
    rw [ht] at h'
    simp only [Except.map, Except.toOption, Option.some.injEq] at h'
    subst h'
    have hap := aligned_apriori cdna3_late (Or.inl rfl) rfl ht
    obtain ⟨L, C, hL, hC, hpr⟩ := evalBlock_pairs ht
    have hval : (mcMachine cdna3F16).val d = C.value := by
      show (value32 d).getD 0 = _; unfold value32; rw [hC]; rfl
    have hp : t.prepared.p = L.map fun q => q.1.mul q.2 := by rw [hpr, products_pairs]
    have hexact : t.prepared.exact = (mcMachine cdna3F16).val d + (mcMachine cdna3F16).slotVal ps := by
      unfold Prepared.exact
      rw [hp, sumQ_eq, List.map_map, hval, slotVal_pairs cdna3_pval_zero, ← sum_decPair _ L hL]
      rw [show t.prepared.c = C by rw [hpr]]
      simp only [Function.comp_def, Unpacked.value_mul]
      rw [Rat.add_comm]
    have habs : t.prepared.absSum = (mcMachine cdna3F16).slotAbs ps + absQ C.value := by
      unfold Prepared.absSum
      rw [hp, sumQ_eq, List.map_map, slotAbs_pairs cdna3_pval_zero, ← sumAbs_decPair _ L hL]
      rw [show t.prepared.c = C by rw [hpr]]
      rfl
    have hlen : (t.prepared.p.length : ℚ) = (ps.length : ℚ) := by
      rw [hp, List.length_map, mapM_length_option hL]; simp [slotPairs]
    have hgrid : gridTerm (productSum cdna3F16 t.prepared.p).1 ≤
        pow2 (-24) * ((slotPairs cdna3F16 ps).map (expMagMC cdna3F16)).sum := by
      have hps : productSum cdna3F16 t.prepared.p = alignedSum cdna3F16.padding t.prepared.p := rfl
      rw [hps]
      unfold alignedSum
      have hsum0 : 0 ≤ ((slotPairs cdna3F16 ps).map (expMagMC cdna3F16)).sum := by
        have : ∀ l : List (cdna3F16.a.Word × cdna3F16.b.Word), 0 ≤ (l.map (expMagMC cdna3F16)).sum := by
          intro l; induction l with
          | nil => simp
          | cons q l ih => simp only [List.map_cons, List.sum_cons]; have := expMagMC_nonneg cdna3F16 q; grind
        exact this _
      split
      · simp only [gridTerm]; exact Rat.mul_nonneg (Rat.le_of_lt (pow2_pos _)) hsum0
      · rename_i e he
        simp only [gridTerm]
        obtain ⟨pr, hpr', hm, hpe⟩ := maxExp_attained he
        rw [hp] at hpr'
        obtain ⟨⟨u, v⟩, huv, rfl⟩ := List.mem_map.mp hpr'
        obtain ⟨q, hq, hdq⟩ := mapM_mem _ hL _ huv
        simp only [decPair] at hdq
        cases hu : (cdna3F16.a.read q.1).toFinite with
        | none => rw [hu] at hdq; cases hdq
        | some u' =>
          cases hv : (cdna3F16.b.read q.2).toFinite with
          | none => rw [hu, hv] at hdq; cases hdq
          | some v' =>
            rw [hu, hv] at hdq
            simp only [Option.bind_some, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hdq
            obtain ⟨rfl, rfl⟩ := hdq
            have hem : expMagMC cdna3F16 q = pow2 e := by
              unfold expMagMC
              rw [hu, hv]
              simp only [Unpacked.mul] at hm hpe
              simp only [if_neg hm, hpe]
            have hle := le_sum_mem (fun x hx => by
              obtain ⟨q', _, rfl⟩ := List.mem_map.mp hx; exact expMagMC_nonneg cdna3F16 q')
              (List.mem_map.mpr ⟨q, hq, rfl⟩)
            rw [hem] at hle
            rw [show e - 24 = -24 + e by omega, pow2_add]
            exact Rat.mul_le_mul_of_nonneg_left hle (Rat.le_of_lt (pow2_pos _))
    have hwd : MatrixCore.wordValue t.d = (mcMachine cdna3F16).val t.d := rfl
    rw [← hwd, ← hexact, Ozaki.abs_sub_comm, ← absQ_eq]
    have hcA : absQ C.value ≤ A := by rw [← hval, absQ_eq]; exact hA
    have hn : (0 : ℚ) ≤ (t.prepared.p.length : ℚ) + 4 := by
      have : (0 : ℚ) ≤ (t.prepared.p.length : ℚ) := by exact_mod_cast Nat.zero_le _
      grind
    have h1 := Rat.mul_le_mul_of_nonneg_left hgrid hn
    rw [hlen] at h1
    have h2 : pow2 (-23) * t.prepared.absSum ≤ pow2 (-23) * (A + (mcMachine cdna3F16).slotAbs ps) := by
      rw [habs]; exact Rat.mul_le_mul_of_nonneg_left (by grind) (Rat.le_of_lt (pow2_pos _))
    rw [hlen] at hap
    grind

/-- The error contract of CDNA 3 fp16. -/
def cdna3Contract : MMAlgebra.Contract (mcMachine cdna3F16) where
  blockErr A ps := pow2 (-23) * (A + (mcMachine cdna3F16).slotAbs ps) +
    ((ps.length : ℚ) + 4) * (pow2 (-24) * ((slotPairs cdna3F16 ps).map (expMagMC cdna3F16)).sum) +
      pow2 (-149)
  block_le d ps o A hA h := cdna3_block_le d ps o A hA h
  addRel := 2 ^ (-24 : ℤ)
  addRel_nonneg := Rat.le_of_lt (Ozaki.two_pow_pos _)
  addAbs := 2 ^ (-150 : ℤ)
  add_le x y o h := add_le cdna3F16 x y o h

/-- **Divergence on CDNA 3.** -/
theorem cdna3_divergence (q : ℕ → cdna3F16.a.Word × cdna3F16.b.Word) (c : F32)
    (t₁ t₂ : MMAlgebra.Term) {o₁ o₂ : F32}
    (he₁ : MMAlgebra.eval (mcMachine cdna3F16) q c c t₁ = some o₁)
    (he₂ : MMAlgebra.eval (mcMachine cdna3F16) q c c t₂ = some o₂)
    (hex : MMAlgebra.exact (mcMachine cdna3F16) q ((mcMachine cdna3F16).val c) ((mcMachine cdna3F16).val c) t₁ =
      MMAlgebra.exact (mcMachine cdna3F16) q ((mcMachine cdna3F16).val c) ((mcMachine cdna3F16).val c) t₂) :
    Rat.abs ((mcMachine cdna3F16).val o₁ - (mcMachine cdna3F16).val o₂) ≤
      MMAlgebra.err cdna3Contract q (Rat.abs ((mcMachine cdna3F16).val c))
          (Rat.abs ((mcMachine cdna3F16).val c)) t₁ +
        MMAlgebra.err cdna3Contract q (Rat.abs ((mcMachine cdna3F16).val c))
          (Rat.abs ((mcMachine cdna3F16).val c)) t₂ :=
  MMAlgebra.divergence _ _ q q c c c c t₁ t₂ he₁ he₂ hex

/-! ## CDNA 2 -/

/-- What flushing the subnormal operands of a pair loses: `|aᵢbᵢ − a'ᵢb'ᵢ|`, zero unless an operand
is subnormal. -/
def subMag (q : cdna2F16.a.Word × cdna2F16.b.Word) : ℚ :=
  Rat.abs ((mcMachine cdna2F16).pval q - fpval q)

theorem cdna2_pval_zero : (mcMachine cdna2F16).pval (0, 0) = 0 := by decide +kernel

theorem sum_decPair_le {P : Model} {F : Unpacked × Unpacked → ℚ} {G : P.a.Word × P.b.Word → ℚ}
    (hFG : ∀ q uv, decPair P q = some uv → F uv ≤ G q) :
    ∀ (qs : List (P.a.Word × P.b.Word)) (L : List (Unpacked × Unpacked)), qs.mapM (decPair P) = some L →
      (L.map F).sum ≤ (qs.map G).sum
  | [], L, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h; subst h; exact Rat.le_refl
  | q :: qs, L, h => by
    simp only [List.mapM_cons] at h
    cases hq : decPair P q with
    | none => simp [hq] at h
    | some uv =>
      cases hqs : qs.mapM (decPair P) with
      | none => simp [hq, hqs] at h
      | some L' =>
        simp only [hq, hqs, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        subst h
        simp only [List.map_cons, List.sum_cons]
        have := hFG q uv hq
        have := sum_decPair_le hFG qs L' hqs
        grind

theorem abs_sum_sub_le {γ : Type} (f g : γ → ℚ) :
    ∀ l : List γ, Rat.abs ((l.map f).sum - (l.map g).sum) ≤ (l.map fun x => Rat.abs (f x - g x)).sum
  | [] => by
    show Rat.abs ((0 : ℚ) - 0) ≤ 0
    rw [Rat.sub_self, Ozaki.abs_zero]; exact Rat.le_refl
  | x :: l => by
    simp only [List.map_cons, List.sum_cons]
    have := abs_sum_sub_le f g l
    have := Ozaki.abs_add_le (f x - g x) ((l.map f).sum - (l.map g).sum)
    rw [show f x - g x + ((l.map f).sum - (l.map g).sum) =
      f x + (l.map f).sum - (g x + (l.map g).sum) by grind] at this
    grind

theorem flush_value_cases (u : Unpacked) : u.flush.value = u.value ∨ u.flush.value = 0 := by
  unfold Unpacked.flush
  split
  · right; exact (Unpacked.value_eq_zero_iff _).mpr rfl
  · left; rfl

theorem abs_flush_le (u : Unpacked) : Rat.abs u.flush.value ≤ Rat.abs u.value := by
  rcases flush_value_cases u with h | h
  · rw [h]; exact Rat.le_refl
  · rw [h, Ozaki.abs_zero]; exact Ozaki.abs_nonneg _

theorem decPair_reads {P : Model} {q : P.a.Word × P.b.Word} {u v : Unpacked}
    (h : decPair P q = some (u, v)) :
    (P.a.read q.1).toFinite = some u ∧ (P.b.read q.2).toFinite = some v := by
  simp only [decPair] at h
  cases hu : (P.a.read q.1).toFinite with
  | none => rw [hu] at h; cases h
  | some u' =>
    cases hv : (P.b.read q.2).toFinite with
    | none => rw [hu, hv] at h; cases h
    | some v' =>
      rw [hu, hv] at h
      simp only [Option.bind_some, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, rfl⟩

theorem pval_decPair {P : Model} {q : P.a.Word × P.b.Word} {u v : Unpacked}
    (h : decPair P q = some (u, v)) : (mcMachine P).pval q = (u.mul v).value := by
  obtain ⟨hu, hv⟩ := decPair_reads h
  show P.a.wordValue q.1 * P.b.wordValue q.2 = _
  simp [InputFormat.wordValue, hu, hv, Unpacked.value_mul]

/-- **The CDNA 2 block contract.** -/
theorem cdna2_block_le (d : F32) (ps : List (Option (cdna2F16.a.Word × cdna2F16.b.Word))) (o : F32)
    (A : ℚ) (hA : Rat.abs ((mcMachine cdna2F16).val d) ≤ A)
    (h : (mcMachine cdna2F16).block d ps = some o) :
    Rat.abs ((mcMachine cdna2F16).val o - ((mcMachine cdna2F16).val d + (mcMachine cdna2F16).slotVal ps)) ≤
      ((slotPairs cdna2F16 ps).map subMag).sum + pow2 (-126) +
        pow2 (-21) * (A + (mcMachine cdna2F16).slotAbs ps) + pow2 (-120) := by
  have h' : (blockBits (P := cdna2F16) ⟨(slotPairs cdna2F16 ps).map Prod.fst,
      (slotPairs cdna2F16 ps).map Prod.snd, d⟩).toOption = some o := h
  unfold blockBits at h'
  cases ht : evalBlock (P := cdna2F16) ⟨(slotPairs cdna2F16 ps).map Prod.fst,
      (slotPairs cdna2F16 ps).map Prod.snd, d⟩ with
  | error e => rw [ht] at h'; simp [Except.map, Except.toOption] at h'
  | ok t =>
    rw [ht] at h'
    simp only [Except.map, Except.toOption, Option.some.injEq] at h'
    subst h'
    have hap := pairwise_apriori (P := cdna2F16) rfl (by decide) ht
    simp only [show cdna2F16.subnormals = false from rfl, Bool.false_eq_true, if_false] at hap
    obtain ⟨L, C, hL, hC, hpr⟩ := evalBlock_pairs ht
    have hval : (mcMachine cdna2F16).val d = C.value := by
      show (value32 d).getD 0 = _; unfold value32; rw [hC]; rfl
    have hp : t.prepared.p = L.map fun q => q.1.mul q.2 := by rw [hpr, products_pairs]
    have hfp : t.prepared.flushed.p = L.map fun q => q.1.flush.mul q.2.flush := by
      rw [hpr, flushed_products_pairs]
    have hfc : t.prepared.flushed.c = C.flush := by rw [hpr]; rfl
    have hcc : t.prepared.c = C := by rw [hpr]
    have hexact : t.prepared.exact = (mcMachine cdna2F16).val d + (mcMachine cdna2F16).slotVal ps := by
      unfold Prepared.exact
      rw [hp, sumQ_eq, List.map_map, hval, slotVal_pairs cdna2_pval_zero, ← sum_decPair _ L hL, hcc]
      simp only [Function.comp_def]
      rw [Rat.add_comm]
    -- the flush loss
    have hloss : absQ (t.prepared.exact - t.prepared.flushed.exact) ≤
        ((slotPairs cdna2F16 ps).map subMag).sum + pow2 (-126) := by
      unfold Prepared.exact
      rw [hp, hfp, hfc, hcc, sumQ_eq, sumQ_eq, List.map_map, List.map_map, absQ_eq]
      have h1 := abs_sum_sub_le (Unpacked.value ∘ fun q : Unpacked × Unpacked => q.1.mul q.2)
        (Unpacked.value ∘ fun q : Unpacked × Unpacked => q.1.flush.mul q.2.flush) L
      have h2 := sum_decPair_le (P := cdna2F16)
        (F := fun x : Unpacked × Unpacked => Rat.abs ((Unpacked.value ∘ fun q : Unpacked × Unpacked =>
          q.1.mul q.2) x - (Unpacked.value ∘ fun q : Unpacked × Unpacked => q.1.flush.mul q.2.flush) x))
        (G := subMag) (fun q uv huv => by
          obtain ⟨u, v⟩ := uv
          obtain ⟨hu, hv⟩ := decPair_reads huv
          unfold subMag
          rw [pval_decPair huv, fpval_eq hu hv]
          exact Rat.le_refl) _ L hL
      have hcf : Rat.abs (C.value - C.flush.value) ≤ pow2 (-126) := by
        rw [flush_value32 hC]
        unfold flushValue
        split
        · rename_i hs
          rw [show C.value - 0 = C.value by grind, ← absQ_eq]; exact Rat.le_of_lt hs
        · rw [Rat.sub_self, Ozaki.abs_zero]; exact Rat.le_of_lt (pow2_pos _)
      have h3 := Ozaki.abs_add_le
        ((L.map (Unpacked.value ∘ fun q : Unpacked × Unpacked => q.1.mul q.2)).sum -
          (L.map (Unpacked.value ∘ fun q : Unpacked × Unpacked => q.1.flush.mul q.2.flush)).sum)
        (C.value - C.flush.value)
      rw [show (L.map (Unpacked.value ∘ fun q : Unpacked × Unpacked => q.1.mul q.2)).sum -
          (L.map (Unpacked.value ∘ fun q : Unpacked × Unpacked => q.1.flush.mul q.2.flush)).sum +
          (C.value - C.flush.value) =
        (L.map (Unpacked.value ∘ fun q : Unpacked × Unpacked => q.1.mul q.2)).sum + C.value -
          ((L.map (Unpacked.value ∘ fun q : Unpacked × Unpacked => q.1.flush.mul q.2.flush)).sum +
            C.flush.value) by grind] at h3
      grind
    -- the flushed magnitudes
    have habs : t.prepared.flushed.absSum ≤ A + (mcMachine cdna2F16).slotAbs ps := by
      unfold Prepared.absSum
      rw [hfp, hfc, sumQ_eq, List.map_map, slotAbs_pairs cdna2_pval_zero]
      have h2 := sum_decPair_le (P := cdna2F16)
        (F := (fun p : Unpacked => absQ p.value) ∘ fun q : Unpacked × Unpacked => q.1.flush.mul q.2.flush)
        (G := fun q => Rat.abs ((mcMachine cdna2F16).pval q)) (fun q uv huv => by
          obtain ⟨u, v⟩ := uv
          rw [pval_decPair huv]
          simp only [Function.comp_def, absQ_eq, Unpacked.value_mul, Ozaki.abs_mul]
          exact Rat.le_trans
            (Rat.mul_le_mul_of_nonneg_right (abs_flush_le u) (Ozaki.abs_nonneg _))
            (Rat.mul_le_mul_of_nonneg_left (abs_flush_le v) (Ozaki.abs_nonneg _))) _ L hL
      have hcA : absQ C.flush.value ≤ A := by
        rw [absQ_eq]; exact Rat.le_trans (abs_flush_le C) (by rw [← hval]; exact hA)
      grind
    have hwd : MatrixCore.wordValue t.d = (mcMachine cdna2F16).val t.d := rfl
    rw [← hwd, ← hexact, Ozaki.abs_sub_comm, ← absQ_eq]
    have := Rat.mul_le_mul_of_nonneg_left habs (Rat.le_of_lt (pow2_pos (-21)))
    grind

/-- The error contract of CDNA 2 fp16. -/
def cdna2Contract : MMAlgebra.Contract (mcMachine cdna2F16) where
  blockErr A ps := ((slotPairs cdna2F16 ps).map subMag).sum + pow2 (-126) +
    pow2 (-21) * (A + (mcMachine cdna2F16).slotAbs ps) + pow2 (-120)
  block_le d ps o A hA h := cdna2_block_le d ps o A hA h
  addRel := 2 ^ (-24 : ℤ)
  addRel_nonneg := Rat.le_of_lt (Ozaki.two_pow_pos _)
  addAbs := 2 ^ (-150 : ℤ)
  add_le x y o h := add_le cdna2F16 x y o h

/-- **Divergence on CDNA 2.** -/
theorem cdna2_divergence (q : ℕ → cdna2F16.a.Word × cdna2F16.b.Word) (c : F32)
    (t₁ t₂ : MMAlgebra.Term) {o₁ o₂ : F32}
    (he₁ : MMAlgebra.eval (mcMachine cdna2F16) q c c t₁ = some o₁)
    (he₂ : MMAlgebra.eval (mcMachine cdna2F16) q c c t₂ = some o₂)
    (hex : MMAlgebra.exact (mcMachine cdna2F16) q ((mcMachine cdna2F16).val c) ((mcMachine cdna2F16).val c) t₁ =
      MMAlgebra.exact (mcMachine cdna2F16) q ((mcMachine cdna2F16).val c) ((mcMachine cdna2F16).val c) t₂) :
    Rat.abs ((mcMachine cdna2F16).val o₁ - (mcMachine cdna2F16).val o₂) ≤
      MMAlgebra.err cdna2Contract q (Rat.abs ((mcMachine cdna2F16).val c))
          (Rat.abs ((mcMachine cdna2F16).val c)) t₁ +
        MMAlgebra.err cdna2Contract q (Rat.abs ((mcMachine cdna2F16).val c))
          (Rat.abs ((mcMachine cdna2F16).val c)) t₂ :=
  MMAlgebra.divergence _ _ q q c c c c t₁ t₂ he₁ he₂ hex

end MMAlgebra.MC
