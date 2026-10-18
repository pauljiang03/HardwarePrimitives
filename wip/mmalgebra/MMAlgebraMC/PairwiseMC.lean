import MMAlgebra.Pairwise
import MMAlgebraMC.RoundedMC

/-! # Completeness for terms on CDNA 2

A CDNA 2 fp16 block flushes subnormal inputs, converts each product to binary32, adds the products
in the balanced tree `fl{fl{p₁ + p₂} + fl{p₃ + p₄}}` and then adds `c`, every `fl{·}` rounding to
nearest and flushing subnormal results. With fp16 operands every value involved is a multiple of
`2^-48`, so it is zero or at least `2^-48` and never subnormal: no flush happens after the inputs,
and the block rounds the exact sum of `c` and the value of the pairwise tree of its slots
(`cdna2_block`). These are the laws of binary summation trees (`cdna2Alg`, on the machine whose
products are the flushed ones). With a kernel-checked table, two terms are equivalent on finite
inputs exactly when their binary summation trees agree (`cdna2_term_equiv_iff`), and the `c`-split
law `blk(t, I) = t ⊕ blk(0, I)` holds with binary32 round-to-nearest addition (`cdna2_csplit`). -/

open MatrixCore Ozaki.MC

namespace MMAlgebra.MC

/-- The product of an operand pair as CDNA 2 forms it, from the flushed operands. -/
def fpval (q : cdna2F16.a.Word × cdna2F16.b.Word) : ℚ :=
  (((cdna2F16.a.read q.1).toFinite.map fun u => u.flush.value).getD 0) *
    (((cdna2F16.b.read q.2).toFinite.map fun u => u.flush.value).getD 0)

/-- The CDNA 2 machine, with the flushed products as the values of the operand pairs. -/
def cdna2M : MMAlgebra.Machine (cdna2F16.a.Word × cdna2F16.b.Word) F32 :=
  { mcMachine cdna2F16 with pval := fpval }

/-- A good CDNA 2 word: finite, not `−0`, and a multiple of `2^-48`. -/
def Good2 (w : F32) : Prop := GoodW w ∧ OnGrid ((value32 w).getD 0) (-48)

/-! ## Rounding multiples of `2^-48` -/

theorem rneMagnitude_onGrid {a : ℚ} {g : ℤ} (ha : OnGrid a g) : OnGrid (rneMagnitude a) g := by
  unfold rneMagnitude
  generalize normExp a - 23 = e
  by_cases h : g ≤ e
  · exact onGrid_intCast_mul _ _ _ h
  · obtain ⟨k, hk⟩ := ha.mono (show e ≤ g by omega)
    have : a / pow2 e = (k : ℚ) := by rw [hk]; exact Rat.mul_div_cancel (pow2_ne_zero _)
    rw [this, rneInt_intCast, ← hk]; exact ha

theorem rneValue_onGrid {x : ℚ} {g : ℤ} (hx : OnGrid x g) : OnGrid (rneValue x) g := by
  unfold rneValue
  have ha : OnGrid (absQ x) g := by
    unfold absQ; split
    · exact hx.neg
    · exact hx
  split
  · exact (rneMagnitude_onGrid ha).neg
  · exact rneMagnitude_onGrid ha

/-- No flush happens on a multiple of `2^-48`. -/
theorem fl32_true_eq {x : ℚ} (hx : OnGrid x (-48)) : fl32 true x = fl32 false x := by
  unfold fl32
  cases hr : rne32 x with
  | none => rfl
  | some w =>
    simp only [Bool.true_and, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    split
    · rename_i hs
      exfalso
      have hv := rne32_value hr
      obtain ⟨hne, hlt⟩ := (value32_subnormal hv).1 hs
      obtain ⟨k, hk⟩ := rneValue_onGrid hx
      rw [hk] at hne hlt
      have hk0 : k ≠ 0 := by intro h; subst h; simp at hne
      have hp := pow2_pos (-48)
      have h1 : pow2 (-48) ≤ absQ ((k : ℚ) * pow2 (-48)) := by
        rw [absQ_mul_pos _ _ hp, absQ_intCast]
        have h1 : (1 : ℚ) ≤ (k.natAbs : ℚ) := by exact_mod_cast (show 1 ≤ k.natAbs by omega)
        have := Rat.mul_le_mul_of_nonneg_right h1 (Rat.le_of_lt hp)
        rw [Rat.one_mul] at this
        exact this
      have h2 : pow2 (-126) ≤ pow2 (-48) := pow2_le_of_le (by omega)
      grind
    · rfl

theorem flValue_true_eq {x : ℚ} (hx : OnGrid x (-48)) :
    flValue true x = (fl32 false x).map fun w => (value32 w).getD 0 := by
  unfold flValue
  rw [fl32_true_eq hx]
  cases h : fl32 false x with
  | none => rfl
  | some w =>
    rw [fl32_false] at h
    simp [rne32_value h]

theorem fl32_good2 {x : ℚ} (hx : OnGrid x (-48)) {w : F32} (h : fl32 false x = some w) : Good2 w := by
  refine ⟨fl32_good (hx.mono (by omega)) h, ?_⟩
  rw [fl32_false] at h
  rw [rne32_value h]
  exact rneValue_onGrid hx

/-! ## Products -/

theorem flush_bounds {u : Unpacked} (h : -14 ≤ u.e ∧ u.e ≤ 15 ∧ u.t = 10 ∧ u.m < 2048) :
    -14 ≤ u.flush.e ∧ u.flush.e ≤ 15 ∧ u.flush.t = 10 ∧ u.flush.m < 2048 := by
  unfold Unpacked.flush
  split
  · exact ⟨h.1, h.2.1, h.2.2.1, show 0 < 2048 by decide⟩
  · exact h

theorem binary16_bounds {i : InputFormat} (hi : i = .packed fp16) {w : i.Word} {x : Unpacked}
    (hx : (i.read w).toFinite = some x) : -14 ≤ x.e ∧ x.e ≤ 15 ∧ x.t = 10 ∧ x.m < 2048 := by
  subst hi
  simp only [InputFormat.read, Format.decode] at hx
  cases hd : fp16.decodeNat w.toNat <;> rw [hd] at hx <;> simp [Datum.toFinite] at hx
  subst hx
  obtain ⟨he, ht⟩ := decodeNat_e hd
  have hle := decode16_e_le hd
  obtain ⟨_, hm⟩ := decodeNat_bounded hd
  simp [fp16, Format.emin] at he ht hm
  exact ⟨by omega, by omega, ht, by omega⟩

theorem fpval_eq {q : cdna2F16.a.Word × cdna2F16.b.Word} {u v : Unpacked}
    (hu : (cdna2F16.a.read q.1).toFinite = some u) (hv : (cdna2F16.b.read q.2).toFinite = some v) :
    fpval q = (u.flush.mul v.flush).value := by
  simp [fpval, hu, hv, Unpacked.value_mul]

theorem prod_finite {u v : Unpacked} (hu : -14 ≤ u.e ∧ u.e ≤ 15 ∧ u.t = 10 ∧ u.m < 2048)
    (hv : -14 ≤ v.e ∧ v.e ≤ 15 ∧ v.t = 10 ∧ v.m < 2048) : FiniteValue32 (u.mul v).value := by
  obtain ⟨hu1, hu2, hut, hum⟩ := hu
  obtain ⟨hv1, hv2, hvt, hvm⟩ := hv
  refine ⟨if u.negative != v.negative then -((u.m * v.m : ℕ) : ℤ) else ((u.m * v.m : ℕ) : ℤ),
    u.e + v.e + 3, by omega, by omega, ?_, ?_⟩
  · have : u.m * v.m < 2048 * 2048 := Nat.mul_lt_mul'' hum hvm
    split <;> simp <;> omega
  · unfold Unpacked.value Unpacked.mul
    simp only [hut, hvt]
    have he : u.e + v.e + 3 - 23 = u.e + v.e - ((10 + 10 : ℕ) : ℤ) := by omega
    rw [he]
    split <;> simp [Rat.intCast_natCast]

theorem fpval_finite (q : cdna2F16.a.Word × cdna2F16.b.Word)
    (hq : ((cdna2F16.a.read q.1).toFinite).isSome ∧ ((cdna2F16.b.read q.2).toFinite).isSome) :
    FiniteValue32 (fpval q) ∧ OnGrid (fpval q) (-48) := by
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hq.1
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hq.2
  rw [fpval_eq hu hv]
  have bu := flush_bounds (binary16_bounds rfl hu)
  have bv := flush_bounds (binary16_bounds rfl hv)
  refine ⟨prod_finite bu bv, ?_⟩
  rw [Unpacked.value_mul]
  have gu : OnGrid u.flush.value (-24) := (unpacked_onGrid _).mono (by omega)
  have gv : OnGrid v.flush.value (-24) := (unpacked_onGrid _).mono (by omega)
  exact onGrid_mul gu gv

/-! ## The rounding laws -/

theorem fpval_zero : fpval (0, 0) = 0 := by decide +kernel

/-- The rounding laws on CDNA 2 fp16, with the flushed products. -/
def cdna2Rounds : MMAlgebra.RoundLaws cdna2M where
  z := (0, 0)
  slot := fun d ps qs h => by
    show (blockBits (P := cdna2F16) ⟨(slotPairs cdna2F16 ps).map Prod.fst,
      (slotPairs cdna2F16 ps).map Prod.snd, d⟩).toOption =
      (blockBits (P := cdna2F16) ⟨(slotPairs cdna2F16 qs).map Prod.fst,
      (slotPairs cdna2F16 qs).map Prod.snd, d⟩).toOption
    unfold slotPairs; rw [h]
  rnd := fl32 false
  good := Good2
  G := fun x => OnGrid x (-48)
  Adm := FiniteIn cdna2F16
  add := fun _ _ => rfl
  rnd_val := fun w hw => by
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hw.1.1
    show fl32 false ((value32 w).getD 0) = some w
    rw [hv]; exact fl32_value_self hv hw.1.2
  rnd_good := fun _ _ hg h => fl32_good2 hg h
  rnd_zero := by decide +kernel
  zero_good := ⟨mc_zero_good, by
    show OnGrid ((value32 (0 : F32)).getD 0) (-48)
    rw [value32_zero]; exact OnGrid.zero _⟩
  G_add := fun _ _ hx hy => OnGrid.add hx hy
  G_zero := OnGrid.zero _
  G_good := fun _ hw => hw.2
  G_pval := fun p hp i => (fpval_finite (p i) (hp i)).2
  prod_exact := fun p hp i => by
    have hf := (fpval_finite (p i) (hp i)).1
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp ((rne32_isSome_iff _).mpr (finiteValue32_lt hf))
    refine ⟨w, by rw [fl32_false]; exact hw, ?_⟩
    show (value32 w).getD 0 = fpval (p i)
    rw [rne32_value hw, rneValue_of_finite hf]; rfl

/-! ## The pairwise sum is the value of the pairwise tree -/

/-- The value of a slot: its flushed product, or zero. -/
def sv (p : ℕ → cdna2F16.a.Word × cdna2F16.b.Word) : Option ℕ → ℚ
  | none => 0
  | some i => fpval (p i)

theorem pgs_succ (ftz : Bool) (d : ℕ) (xs : List ℚ) (h : 2 ≤ xs.length) :
    pairwiseGroupSum ftz (d + 1) xs = (pairwiseGroupSum ftz d (xs.take (xs.length / 2))).bind fun u =>
      (pairwiseGroupSum ftz d (xs.drop (xs.length / 2))).bind fun v => flValue ftz (u + v) := by
  match xs, h with
  | _ :: _ :: _, _ => rfl

theorem good2_value {w : F32} (hw : Good2 w) :
    flValue true ((value32 w).getD 0) = some ((value32 w).getD 0) := by
  rw [flValue_true_eq hw.2]
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hw.1.1
  rw [hv]
  simp only [Option.getD_some]
  rw [fl32_value_self hv hw.1.2]
  simp [hv]

theorem pgs_eq (p : ℕ → cdna2F16.a.Word × cdna2F16.b.Word) (hp : FiniteIn cdna2F16 p) :
    ∀ (d : ℕ) (l : List (Option ℕ)), l.length ≤ d + 1 →
      pairwiseGroupSum true d (l.map (sv p)) =
        (MMAlgebra.evCRO cdna2M (fl32 false) p 0 (MMAlgebra.pairTree d l)).map fun w => (value32 w).getD 0
  | d, [], _ => by
    cases d <;> simp [pairwiseGroupSum, MMAlgebra.pairTree, MMAlgebra.evCRO] <;> decide +kernel
  | d, [o], _ => by
    cases o with
    | none =>
      cases d <;> simp [pairwiseGroupSum, MMAlgebra.pairTree, MMAlgebra.evCRO, sv] <;> decide +kernel
    | some i =>
      obtain ⟨w, hw, hv⟩ := cdna2Rounds.prod_exact p hp i
      have hw' : fl32 false (cdna2M.pval (p i)) = some w := hw
      have hv' : (value32 w).getD 0 = fpval (p i) := hv
      cases d <;> simp [pairwiseGroupSum, MMAlgebra.pairTree, MMAlgebra.evCRO, MMAlgebra.evCR, sv,
        hw', hv']
  | 0, _ :: _ :: _, h => by simp at h
  | d + 1, a :: b :: r, h => by
    rw [pgs_succ true d _ (by simp), MMAlgebra.pairTree_succ d (a :: b :: r) (by simp)]
    have h2 : 2 ≤ (a :: b :: r).length := by simp
    generalize a :: b :: r = l at h h2 ⊢
    rw [List.length_map, ← List.map_take, ← List.map_drop,
      pgs_eq p hp d _ (by simp; omega), pgs_eq p hp d _ (by simp; omega)]
    have hg := MMAlgebra.evCR_good cdna2Rounds p hp
    generalize MMAlgebra.pairTree d (l.take (l.length / 2)) = T₁
    generalize MMAlgebra.pairTree d (l.drop (l.length / 2)) = T₂
    cases T₁ with
    | none =>
      cases T₂ with
      | none =>
        simp [MMAlgebra.evCRO, MMAlgebra.optKid, MMAlgebra.LTree.mk]
        decide +kernel
      | some V =>
        simp only [MMAlgebra.evCRO, MMAlgebra.optKid, List.nil_append, MMAlgebra.LTree.mk,
          Option.map_some, Option.bind_some, value32_zero, Option.getD_some]
        cases hV : MMAlgebra.evCR cdna2M (fl32 false) p V with
        | none => rfl
        | some w =>
          simp only [Option.map_some, Option.bind_some, Rat.zero_add]
          exact good2_value (hg V w hV)
    | some U =>
      cases T₂ with
      | none =>
        simp only [MMAlgebra.evCRO, MMAlgebra.optKid, List.append_nil, MMAlgebra.LTree.mk,
          Option.map_some, value32_zero, Option.getD_some]
        cases hU : MMAlgebra.evCR cdna2M (fl32 false) p U with
        | none => rfl
        | some w =>
          simp only [Option.map_some, Option.bind_some, Rat.add_zero]
          exact good2_value (hg U w hU)
      | some V =>
        simp only [MMAlgebra.evCRO, MMAlgebra.optKid, List.singleton_append, MMAlgebra.LTree.mk,
          MMAlgebra.evCR]
        rw [MMAlgebra.sumCR_perm (fl32 false) p (MMAlgebra.LTree.sortKids_perm _)]
        simp only [MMAlgebra.sumCR]
        cases hU : MMAlgebra.evCR cdna2M (fl32 false) p U with
        | none => rfl
        | some x =>
          cases hV : MMAlgebra.evCR cdna2M (fl32 false) p V with
          | none => rfl
          | some y =>
            simp only [Option.map_some, Option.bind_some, Rat.add_zero]
            rw [flValue_true_eq (OnGrid.add (hg U x hU).2 (hg V y hV).2)]
            rfl

/-! ## The block law -/

theorem flushed_products_pairs (L : List (Unpacked × Unpacked)) (C : Unpacked) :
    (Prepared.mk (L.map Prod.fst) (L.map Prod.snd) C).flushed.p =
      L.map fun q => q.1.flush.mul q.2.flush := by
  unfold Prepared.flushed Prepared.p
  induction L with
  | nil => rfl
  | cons q L ih => simp

theorem decPair_fpval :
    ∀ (qs : List (cdna2F16.a.Word × cdna2F16.b.Word)) (L : List (Unpacked × Unpacked)),
      qs.mapM (decPair cdna2F16) = some L →
        (L.map fun q => (q.1.flush.mul q.2.flush).value) = qs.map fpval
  | [], L, h => by simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h; subst h; rfl
  | q :: qs, L, h => by
    simp only [List.mapM_cons] at h
    cases hq : decPair cdna2F16 q with
    | none => simp [hq] at h
    | some uv =>
      cases hqs : qs.mapM (decPair cdna2F16) with
      | none => simp [hq, hqs] at h
      | some L' =>
        simp only [hq, hqs, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        subst h
        simp only [List.map_cons, decPair_fpval qs L' hqs]
        congr 1
        obtain ⟨u, v⟩ := uv
        simp only [decPair] at hq
        cases hu : (cdna2F16.a.read q.1).toFinite with
        | none => rw [hu] at hq; cases hq
        | some u' =>
          cases hv : (cdna2F16.b.read q.2).toFinite with
          | none => rw [hu, hv] at hq; cases hq
          | some v' =>
            rw [hu, hv] at hq
            simp only [Option.bind_some, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hq
            obtain ⟨rfl, rfl⟩ := hq
            exact (fpval_eq hu hv).symm

theorem slots_sv (p : ℕ → cdna2F16.a.Word × cdna2F16.b.Word) (I : List (Option ℕ)) :
    (slotPairs cdna2F16 (I.map (Option.map p))).map fpval = I.map (sv p) := by
  induction I with
  | nil => rfl
  | cons o I ih =>
    show fpval ((o.map p).getD (0, 0)) :: (slotPairs cdna2F16 (I.map (Option.map p))).map fpval =
      sv p o :: I.map (sv p)
    rw [ih]
    cases o with
    | none => show fpval (0, 0) :: _ = 0 :: _; rw [fpval_zero]
    | some i => rfl

theorem mapM_map_eq {γ δ ε : Type} (f : γ → δ) (g : δ → Option ε) :
    ∀ l : List γ, (l.map f).mapM g = l.mapM (g ∘ f)
  | [] => rfl
  | x :: l => by simp [List.mapM_cons, mapM_map_eq f g l]

theorem flValue_products (p : ℕ → cdna2F16.a.Word × cdna2F16.b.Word) (hp : FiniteIn cdna2F16 p) :
    ∀ I : List (Option ℕ), (I.map (sv p)).mapM (flValue true) = some (I.map (sv p))
  | [] => rfl
  | o :: I => by
    simp only [List.map_cons, List.mapM_cons, flValue_products p hp I]
    have : flValue true (sv p o) = some (sv p o) := by
      cases o with
      | none => show flValue true 0 = some 0; decide +kernel
      | some i =>
        obtain ⟨hf, hg⟩ := fpval_finite (p i) (hp i)
        show flValue true (fpval (p i)) = some (fpval (p i))
        rw [flValue_true_eq hg]
        obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp ((rne32_isSome_iff _).mpr (finiteValue32_lt hf))
        rw [fl32_false, hw]
        simp [rne32_value hw, rneValue_of_finite hf]
    simp [this]

theorem flush_value_good {d : F32} (hd : Good2 d) {C : Unpacked}
    (hC : (fp32.decode d).toFinite = some C) : C.flush.value = C.value := by
  unfold Unpacked.flush
  split
  · rename_i hm
    have hu := decode32_val d hC
    have hv : (value32 d).getD 0 = C.value := by unfold value32; rw [hC]; rfl
    have hg := hd.2
    rw [hv] at hg
    have hsmall : absQ C.value < pow2 (-126) := by
      split at hu
      · subst hu
        rw [Unpacked.absQ_value]
        have h1 : ((d.toNat % 8388608 : ℕ) : ℚ) < 8388608 := by
          exact_mod_cast (Nat.mod_lt _ (by decide) : d.toNat % 8388608 < 8388608)
        have hp := pow2_pos (-126 - ((23 : ℕ) : ℤ))
        have := Rat.mul_lt_mul_of_pos_right h1 hp
        have e : (8388608 : ℚ) * pow2 (-126 - ((23 : ℕ) : ℤ)) = pow2 (-126) := by decide +kernel
        rw [e] at this; exact this
      · subst hu; exact absurd hm (by simp only; omega)
    obtain ⟨k, hk⟩ := hg
    have hk0 : k = 0 := by
      apply Classical.byContradiction; intro hk0
      have hp := pow2_pos (-48)
      have h1 : pow2 (-48) ≤ absQ ((k : ℚ) * pow2 (-48)) := by
        rw [absQ_mul_pos _ _ hp, absQ_intCast]
        have h1 : (1 : ℚ) ≤ (k.natAbs : ℚ) := by exact_mod_cast (show 1 ≤ k.natAbs by omega)
        have := Rat.mul_le_mul_of_nonneg_right h1 (Rat.le_of_lt hp)
        rw [Rat.one_mul] at this; exact this
      have h2 : pow2 (-126) ≤ pow2 (-48) := pow2_le_of_le (by omega)
      rw [hk] at hsmall
      grind
    rw [hk, hk0]
    unfold Unpacked.value; simp
  · rfl

/-- **A CDNA 2 block rounds the sum of `c` and the value of the pairwise tree of its slots.** -/
theorem cdna2_block (p : ℕ → cdna2F16.a.Word × cdna2F16.b.Word) (hp : FiniteIn cdna2F16 p) (d : F32)
    (I : List (Option ℕ)) (hI : I.length = 4) (hd : Good2 d) :
    cdna2M.block d (I.map (Option.map p)) =
      (MMAlgebra.evCRO cdna2M (fl32 false) p 0 (MMAlgebra.pairTree I.length I)).bind
        fun w => fl32 false ((value32 d).getD 0 + (value32 w).getD 0) := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hd.1.1
  obtain ⟨C, hC, hCv⟩ : ∃ C, (fp32.decode d).toFinite = some C ∧ C.value = v := by
    unfold value32 at hv
    cases hc : (fp32.decode d).toFinite with
    | none => rw [hc] at hv; cases hv
    | some C => rw [hc] at hv; exact ⟨C, rfl, Option.some.inj hv⟩
  have hfin : ∀ q ∈ slotPairs cdna2F16 (I.map (Option.map p)), (decPair cdna2F16 q).isSome := by
    intro q hq
    simp only [slotPairs, List.map_map, List.mem_map] at hq
    obtain ⟨o, _, rfl⟩ := hq
    cases o with
    | none => show (decPair cdna2F16 (0, 0)).isSome = true; decide +kernel
    | some i =>
      obtain ⟨h1, h2⟩ := hp i
      obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp h1
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp h2
      simp [decPair, hu, hw]
  obtain ⟨L, hL⟩ := mapM_isSome _ _ hfin
  have hprep : prepare (P := cdna2F16) ⟨(slotPairs cdna2F16 (I.map (Option.map p))).map Prod.fst,
      (slotPairs cdna2F16 (I.map (Option.map p))).map Prod.snd, d⟩ =
      some ⟨L.map Prod.fst, L.map Prod.snd, C⟩ := by
    rw [prepare_pairs, hL, Option.bind_some, hC]; rfl
  have hvals : (L.map fun q => (q.1.flush.mul q.2.flush).value) = I.map (sv p) := by
    rw [decPair_fpval _ L hL, slots_sv]
  have hpgs := pgs_eq p hp I.length I (by omega)
  have hsum : pairwiseSum cdna2F16 ⟨L.map Prod.fst, L.map Prod.snd, C⟩ =
      ((MMAlgebra.evCRO cdna2M (fl32 false) p 0 (MMAlgebra.pairTree I.length I)).map
        fun w => (value32 w).getD 0).map fun t => C.value + t := by
    unfold pairwiseSum
    simp only [show cdna2F16.subnormals = false from rfl, Bool.false_eq_true, ↓reduceIte,
      Bool.not_false]
    rw [flushed_products_pairs]
    have hc : (Prepared.mk (L.map Prod.fst) (L.map Prod.snd) C).flushed.c.value = C.value :=
      flush_value_good hd hC
    rw [hc]
    have hm : (L.map fun q => q.1.flush.mul q.2.flush).mapM (fun p => flValue true p.value) =
        some (I.map (sv p)) := by
      have h := flValue_products p hp I
      rw [← hvals, mapM_map_eq] at h
      rw [mapM_map_eq, ← hvals]
      exact h
    simp only [Option.bind_eq_bind, Option.pure_def]
    rw [hm, Option.bind_some, List.length_map, hpgs]
    cases MMAlgebra.evCRO cdna2M (fl32 false) p 0 (MMAlgebra.pairTree I.length I) <;> rfl
  show (blockBits (P := cdna2F16) ⟨(slotPairs cdna2F16 (I.map (Option.map p))).map Prod.fst,
    (slotPairs cdna2F16 (I.map (Option.map p))).map Prod.snd, d⟩).toOption = _
  unfold blockBits evalBlock
  have hlen : (slotPairs cdna2F16 (I.map (Option.map p))).length = 4 := by simp [slotPairs, hI]
  simp only [List.length_map, hlen]
  rw [if_neg (by decide), hprep]
  simp only
  unfold accumulate
  simp only [show cdna2F16.productOverflow = false from rfl, Bool.false_and, Bool.false_eq_true,
    ↓reduceIte, show cdna2F16.accumulation = .pairWiseSum from rfl]
  rw [hsum]
  have hg := MMAlgebra.evCRO_good cdna2Rounds p hp (MMAlgebra.pairTree I.length I)
  have hval : cdna2M.val d = C.value := by
    show (value32 d).getD 0 = C.value; rw [hv, hCv]; rfl
  have hval' : (value32 d).getD 0 = C.value := by rw [hv, hCv]; rfl
  cases hw : MMAlgebra.evCRO cdna2M (fl32 false) p 0 (MMAlgebra.pairTree I.length I) with
  | none => simp [Except.map, Except.toOption]
  | some w =>
    have hgw := hg w hw
    simp only [Option.map_some, Option.bind_some]
    have hgrid : OnGrid (C.value + (value32 w).getD 0) (-48) := by
      rw [← hval']; exact OnGrid.add hd.2 hgw.2
    rw [show (!cdna2F16.subnormals) = true from rfl, fl32_true_eq hgrid, hval']
    cases fl32 false (C.value + (value32 w).getD 0) <;> rfl

/-- The laws of binary summation trees, for CDNA 2 fp16. -/
def cdna2Alg : MMAlgebra.PairAlg cdna2M 4 :=
  { cdna2Rounds with block := fun p hp d I hI hd => cdna2_block p hp d I hI hd }

/-! ## Completeness and the `c`-split law -/

/-- The CDNA 2 machine with flushed products evaluates terms as the Matrix Core model does. -/
theorem eval_cdna2M (p : ℕ → cdna2F16.a.Word × cdna2F16.b.Word) (c h : F32) :
    ∀ t : MMAlgebra.Term, MMAlgebra.eval cdna2M p c h t = MMAlgebra.eval (mcMachine cdna2F16) p c h t
  | .zero => rfl
  | .init => rfl
  | .hole => rfl
  | .blk t I => by simp only [MMAlgebra.eval, eval_cdna2M p c h t]; rfl
  | .add t u => by simp only [MMAlgebra.eval, eval_cdna2M p c h t, eval_cdna2M p c h u]; rfl

/-- An input with the operand pairs of a list at `0, 1, 2, …` and zero pairs elsewhere. -/
def wordsInput2 (ws : List (cdna2F16.a.Word × cdna2F16.b.Word)) : ℕ → cdna2F16.a.Word × cdna2F16.b.Word :=
  fun j => ws.getD j (0, 0)

/-- CDNA 2: inputs on three products (normal fp16 operands) that separate the trees `x + y + z`,
`(x + y) + z`, `(x + z) + y` and `x + (y + z)`. -/
def cdna2In3 : List (ℕ → cdna2F16.a.Word × cdna2F16.b.Word) :=
  [wordsInput2 [(0x0812, 0x1f19), (0xf27b, 0x2a78), (0x3bee, 0xb7d5)],
   wordsInput2 [(0xf844, 0x9e8c), (0xc9b0, 0xb7d0), (0x054e, 0x2e2a)],
   wordsInput2 [(0x8953, 0x57b5), (0x0506, 0x33cc), (0x478a, 0xe540)]]

theorem cdna2_table3 : (MMAlgebra.codes3Unit.map fun κ => cdna2In3.map fun q =>
    MMAlgebra.evCR cdna2M (fl32 false) q (κ.realize 0 1 2)).Nodup := by
  decide +kernel

theorem finiteIn_words2 (ws : List (cdna2F16.a.Word × cdna2F16.b.Word))
    (h : ∀ q ∈ ws, ((cdna2F16.a.read q.1).toFinite).isSome ∧ ((cdna2F16.b.read q.2).toFinite).isSome)
    (g : ℕ → ℕ) : FiniteIn cdna2F16 (fun x => wordsInput2 ws (g x)) := by
  intro i
  show ((cdna2F16.a.read (ws.getD (g i) (0, 0)).1).toFinite).isSome ∧
    ((cdna2F16.b.read (ws.getD (g i) (0, 0)).2).toFinite).isSome
  rcases getD_mem_or (0, 0) ws (g i) with hm | hz
  · exact h _ hm
  · rw [hz]; decide +kernel

theorem cdna2_adm : ∀ q ∈ cdna2In3, ∀ g : ℕ → ℕ, FiniteIn cdna2F16 (fun x => q (g x)) := by
  intro q hq g
  simp only [cdna2In3, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl <;> exact finiteIn_words2 _ (by decide +kernel) g

/-- **CDNA 2 (fp16), completeness for terms.** Two terms from `+0` with blocks of 4 slots over
the same products, each once, with different binary summation trees differ on an input of finite
operands that is zero outside at most three of the products. -/
theorem cdna2_term_complete (t₁ t₂ : MMAlgebra.Term) (hw₁ : MMAlgebra.TermWF 4 t₁)
    (hw₂ : MMAlgebra.TermWF 4 t₂) (n₁ : t₁.leaves.Nodup) (n₂ : t₂.leaves.Nodup)
    (hl : ∀ i, i ∈ t₁.leaves ↔ i ∈ t₂.leaves) (hne : MMAlgebra.nfP t₁ ≠ MMAlgebra.nfP t₂) :
    ∃ (s : List ℕ) (q : ℕ → cdna2F16.a.Word × cdna2F16.b.Word), s.length ≤ 3 ∧
      (∀ i, i ∉ s → q i = (0, 0)) ∧ FiniteIn cdna2F16 q ∧
      MMAlgebra.eval (mcMachine cdna2F16) q 0 0 t₁ ≠ MMAlgebra.eval (mcMachine cdna2F16) q 0 0 t₂ := by
  obtain ⟨s, q, hs, hz, ⟨p, hp, hq⟩, hne'⟩ :=
    MMAlgebra.pair_term_complete cdna2Alg cdna2In3 cdna2_adm cdna2_table3 t₁ t₂ hw₁ hw₂ n₁ n₂ hl hne
  refine ⟨s, q, hs, hz, ?_, by rw [← eval_cdna2M, ← eval_cdna2M]; exact hne'⟩
  intro i
  rcases hq i with h | h
  · rw [h]; decide +kernel
  · rw [h]; exact hp i

/-- **CDNA 2 (fp16): terms are equivalent on finite inputs exactly when their binary summation
trees agree.** -/
theorem cdna2_term_equiv_iff (t₁ t₂ : MMAlgebra.Term) (hw₁ : MMAlgebra.TermWF 4 t₁)
    (hw₂ : MMAlgebra.TermWF 4 t₂) (n₁ : t₁.leaves.Nodup) (n₂ : t₂.leaves.Nodup)
    (hl : ∀ i, i ∈ t₁.leaves ↔ i ∈ t₂.leaves) :
    (∀ q, FiniteIn cdna2F16 q →
        MMAlgebra.eval (mcMachine cdna2F16) q 0 0 t₁ = MMAlgebra.eval (mcMachine cdna2F16) q 0 0 t₂) ↔
      MMAlgebra.nfP t₁ = MMAlgebra.nfP t₂ := by
  constructor
  · intro h
    apply Classical.byContradiction; intro hne
    obtain ⟨_, q, _, _, hq, hd⟩ := cdna2_term_complete t₁ t₂ hw₁ hw₂ n₁ n₂ hl hne
    exact hd (h q hq)
  · intro h q hq
    have e₁ := MMAlgebra.pair_sound cdna2Alg q hq t₁ hw₁ n₁
    have e₂ := MMAlgebra.pair_sound cdna2Alg q hq t₂ hw₂ n₂
    rw [h] at e₁
    rw [← eval_cdna2M, ← eval_cdna2M]
    exact e₁.trans e₂.symm

/-- **The `c`-split law of CDNA 2.** A block's accumulator can be moved into a separate binary32
round-to-nearest addition, `blk(t, I) = t ⊕ blk(0, I)`, on every input of finite operands. -/
theorem cdna2_csplit (t : MMAlgebra.Term) (I : List (Option ℕ)) (hw : MMAlgebra.TermWF 4 t)
    (hI : I.length = 4) (hn : (MMAlgebra.Term.blk t I).leaves.Nodup)
    (q : ℕ → cdna2F16.a.Word × cdna2F16.b.Word) (hq : FiniteIn cdna2F16 q) :
    MMAlgebra.eval (mcMachine cdna2F16) q 0 0 (.blk t I) =
      MMAlgebra.eval (mcMachine cdna2F16) q 0 0 (.add t (.blk .zero I)) := by
  have hn' : (MMAlgebra.Term.add t (.blk .zero I)).leaves.Nodup := by
    show (t.leaves ++ ([] ++ MMAlgebra.blockLeaves I)).Nodup
    rw [List.nil_append]; exact hn
  have e₁ := MMAlgebra.pair_sound cdna2Alg q hq (.blk t I) ⟨hw, hI⟩ hn
  have e₂ := MMAlgebra.pair_sound cdna2Alg q hq (.add t (.blk .zero I)) ⟨hw, ⟨trivial, hI⟩⟩ hn'
  rw [MMAlgebra.nfP_csplit] at e₁
  rw [← eval_cdna2M, ← eval_cdna2M]
  exact e₁.trans e₂.symm

end MMAlgebra.MC
