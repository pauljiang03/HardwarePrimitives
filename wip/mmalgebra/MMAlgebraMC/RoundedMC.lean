import MMAlgebra.Rounded
import MMAlgebraMC.RigidMC

/-! # Completeness for terms on CDNA 1

On CDNA 1 fp16 a block returns the binary32 value nearest to the exact sum of `c` and its products
(`cdna1_block`), and a binary32 addition the value nearest to the exact sum of its operands; an fp16
product is a binary32 value (`fp16_prod_exact`), and every exact sum is a multiple of `2^-149`, so
no result is `−0`. These are the laws of correctly rounded nodes (`cdna1Alg`). With a
kernel-checked table that separates the four trees on three products, two terms are equivalent on
finite inputs exactly when their correctly rounded normal forms agree (`cdna1_term_equiv_iff`); in
particular the merge law `[x] [J] = [x J]` and `[x] ⊕ [y] = [x y]` hold (`cdna1_merge`,
`cdna1_add_merge`). -/

open MatrixCore Ozaki.MC

namespace MMAlgebra.MC

/-- Inputs whose operand words are all finite. -/
def FiniteIn (P : Model) (p : ℕ → P.a.Word × P.b.Word) : Prop :=
  ∀ i, ((P.a.read (p i).1).toFinite).isSome ∧ ((P.b.read (p i).2).toFinite).isSome

theorem mapM_isSome {γ δ : Type} (f : γ → Option δ) :
    ∀ xs : List γ, (∀ x ∈ xs, (f x).isSome) → ∃ L, xs.mapM f = some L
  | [], _ => ⟨[], rfl⟩
  | x :: xs, h => by
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (h x (by simp))
    obtain ⟨L, hL⟩ := mapM_isSome f xs (fun x' hx' => h x' (by simp [hx']))
    exact ⟨y :: L, by simp [List.mapM_cons, hy, hL]⟩

theorem sum_decPair {P : Model} :
    ∀ (qs : List (P.a.Word × P.b.Word)) (L : List (Unpacked × Unpacked)), qs.mapM (decPair P) = some L →
      (L.map fun q => (q.1.mul q.2).value).sum = (qs.map (mcMachine P).pval).sum
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
        simp only [List.map_cons, List.sum_cons, sum_decPair qs L' hqs]
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
            show (u'.mul v').value = P.a.wordValue q.1 * P.b.wordValue q.2
            simp [InputFormat.wordValue, hu, hv, Unpacked.value_mul]

theorem slotVal_pairs {P : Model} (hz : (mcMachine P).pval (0, 0) = 0) :
    ∀ ps : List (Option (P.a.Word × P.b.Word)),
      (mcMachine P).slotVal ps = ((slotPairs P ps).map (mcMachine P).pval).sum
  | [] => rfl
  | o :: ps => by
    rw [(mcMachine P).slotVal_cons, slotVal_pairs hz ps]
    cases o with
    | none =>
      show 0 + ((slotPairs P ps).map (mcMachine P).pval).sum =
        (mcMachine P).pval (0, 0) + ((slotPairs P ps).map (mcMachine P).pval).sum
      rw [hz]
    | some q => rfl

theorem cdna1_pval_zero : (mcMachine cdna1F16).pval (0, 0) = 0 := by decide +kernel

/-- **A CDNA 1 block rounds the exact sum of `c` and its products.** -/
theorem cdna1_block (p : ℕ → cdna1F16.a.Word × cdna1F16.b.Word) (hp : FiniteIn cdna1F16 p) (d : F32)
    (I : List (Option ℕ)) (hI : I.length = 4) (hd : GoodW d) :
    (mcMachine cdna1F16).block d (I.map (Option.map p)) =
      fl32 false ((mcMachine cdna1F16).val d + (mcMachine cdna1F16).slotVal (I.map (Option.map p))) := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hd.1
  obtain ⟨C, hC, hCv⟩ : ∃ C, (fp32.decode d).toFinite = some C ∧ C.value = v := by
    unfold value32 at hv
    cases hc : (fp32.decode d).toFinite with
    | none => rw [hc] at hv; cases hv
    | some C => rw [hc] at hv; exact ⟨C, rfl, Option.some.inj hv⟩
  have hfin : ∀ q ∈ slotPairs cdna1F16 (I.map (Option.map p)), (decPair cdna1F16 q).isSome := by
    intro q hq
    simp only [slotPairs, List.map_map, List.mem_map] at hq
    obtain ⟨o, _, rfl⟩ := hq
    cases o with
    | none => show (decPair cdna1F16 (0, 0)).isSome = true; decide +kernel
    | some i =>
      obtain ⟨h1, h2⟩ := hp i
      obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp h1
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp h2
      simp [decPair, hu, hw]
  obtain ⟨L, hL⟩ := mapM_isSome _ _ hfin
  have hprep : prepare (P := cdna1F16) ⟨(slotPairs cdna1F16 (I.map (Option.map p))).map Prod.fst,
      (slotPairs cdna1F16 (I.map (Option.map p))).map Prod.snd, d⟩ =
      some ⟨L.map Prod.fst, L.map Prod.snd, C⟩ := by
    rw [prepare_pairs, hL, Option.bind_some, hC]; rfl
  have hexact : (Prepared.mk (L.map Prod.fst) (L.map Prod.snd) C).exact =
      (mcMachine cdna1F16).val d + (mcMachine cdna1F16).slotVal (I.map (Option.map p)) := by
    unfold Prepared.exact
    rw [products_pairs, sumQ_eq, List.map_map]
    rw [slotVal_pairs cdna1_pval_zero, ← sum_decPair _ L hL]
    show _ + C.value = (value32 d).getD 0 + _
    rw [hv, hCv, Option.getD_some, Rat.add_comm]
    rfl
  show (blockBits (P := cdna1F16) ⟨(slotPairs cdna1F16 (I.map (Option.map p))).map Prod.fst,
    (slotPairs cdna1F16 (I.map (Option.map p))).map Prod.snd, d⟩).toOption = _
  unfold blockBits evalBlock
  have hlen : (slotPairs cdna1F16 (I.map (Option.map p))).length = 4 := by simp [slotPairs, hI]
  simp only [List.length_map, hlen]
  rw [if_neg (by decide), hprep]
  simp only
  rw [accumulate_correctRounding rfl rfl, hexact]
  simp only
  rw [show (!cdna1F16.subnormals) = false from rfl]
  cases fl32 false ((mcMachine cdna1F16).val d + (mcMachine cdna1F16).slotVal (I.map (Option.map p))) <;>
    rfl

/-! ## fp16 products are binary32 values -/

theorem decode16_e_le {n : ℕ} {u : Unpacked} (h : fp16.decodeNat n = .finite u) : u.e ≤ 15 := by
  unfold Format.decodeNat at h
  simp only [fp16] at h
  have hE : n / 2 ^ 10 % 2 ^ 5 < 32 := Nat.mod_lt _ (by decide)
  split at h
  · split at h <;> simp at h
  · rename_i hne
    simp only [Datum.finite.injEq] at h
    subst h
    unfold Format.unpackFields
    split
    · simp [Format.emin]
    · simp only; omega

/-- **An fp16 product is a binary32 value.** -/
theorem fp16_prod_exact {P : Model} (ha : P.a = .packed fp16) (hb : P.b = .packed fp16)
    (q : P.a.Word × P.b.Word) (hq : ((P.a.read q.1).toFinite).isSome ∧ ((P.b.read q.2).toFinite).isSome) :
    FiniteValue32 ((mcMachine P).pval q) := by
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hq.1
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hq.2
  have hval : (mcMachine P).pval q = u.value * v.value := by
    show P.a.wordValue q.1 * P.b.wordValue q.2 = _
    simp [InputFormat.wordValue, hu, hv]
  have bnd : ∀ {i : InputFormat} (hi : i = .packed fp16) {w : i.Word} {x : Unpacked},
      (i.read w).toFinite = some x → -14 ≤ x.e ∧ x.e ≤ 15 ∧ x.t = 10 ∧ x.m < 2048 := by
    intro i hi w x hx
    subst hi
    simp only [InputFormat.read, Format.decode] at hx
    cases hd : fp16.decodeNat w.toNat <;> rw [hd] at hx <;> simp [Datum.toFinite] at hx
    subst hx
    obtain ⟨he, ht⟩ := decodeNat_e hd
    have hle := decode16_e_le hd
    obtain ⟨_, hm⟩ := decodeNat_bounded hd
    simp [fp16, Format.emin] at he hle ht hm
    exact ⟨by omega, by omega, ht, by omega⟩
  obtain ⟨hu1, hu2, hut, hum⟩ := bnd ha hu
  obtain ⟨hv1, hv2, hvt, hvm⟩ := bnd hb hv
  rw [hval, ← Unpacked.value_mul]
  refine ⟨if u.negative != v.negative then -((u.m * v.m : ℕ) : ℤ) else ((u.m * v.m : ℕ) : ℤ),
    u.e + v.e + 3, by omega, by omega, ?_, ?_⟩
  · have : u.m * v.m < 2048 * 2048 := Nat.mul_lt_mul'' hum hvm
    split <;> simp <;> omega
  · unfold Unpacked.value Unpacked.mul
    simp only [hut, hvt]
    have he : u.e + v.e + 3 - 23 = u.e + v.e - ((10 + 10 : ℕ) : ℤ) := by omega
    rw [he]
    split <;> simp [Rat.intCast_natCast]

/-! ## The correctly rounded laws on CDNA 1 -/

theorem cdna1_prod_exact (p : ℕ → cdna1F16.a.Word × cdna1F16.b.Word) (hp : FiniteIn cdna1F16 p)
    (i : ℕ) : ∃ w, fl32 false ((mcMachine cdna1F16).pval (p i)) = some w ∧
      (mcMachine cdna1F16).val w = (mcMachine cdna1F16).pval (p i) := by
  have hf := fp16_prod_exact rfl rfl (p i) (hp i)
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp ((rne32_isSome_iff _).mpr (finiteValue32_lt hf))
  refine ⟨w, by rw [fl32_false]; exact hw, ?_⟩
  show (value32 w).getD 0 = _
  rw [rne32_value hw, rneValue_of_finite hf]; rfl

/-- The laws of correctly rounded nodes, for CDNA 1 fp16. -/
def cdna1Alg : MMAlgebra.CRAlg (mcMachine cdna1F16) 4 where
  z := (0, 0)
  slot := fun d ps qs h => by
    show (blockBits (P := cdna1F16) ⟨(slotPairs cdna1F16 ps).map Prod.fst,
      (slotPairs cdna1F16 ps).map Prod.snd, d⟩).toOption =
      (blockBits (P := cdna1F16) ⟨(slotPairs cdna1F16 qs).map Prod.fst,
      (slotPairs cdna1F16 qs).map Prod.snd, d⟩).toOption
    unfold slotPairs; rw [h]
  rnd := fl32 false
  good := GoodW
  G := fun x => OnGrid x (-149)
  Adm := FiniteIn cdna1F16
  block := fun p hp d I hI hd => cdna1_block p hp d I hI hd
  add := fun _ _ => rfl
  rnd_val := fun w hw => by
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hw.1
    show fl32 false ((value32 w).getD 0) = some w
    rw [hv]; exact fl32_value_self hv hw.2
  rnd_good := fun _ _ hg h => fl32_good hg h
  rnd_zero := by decide +kernel
  zero_good := mc_zero_good
  G_add := fun _ _ hx hy => OnGrid.add hx hy
  G_zero := OnGrid.zero _
  G_good := fun w _ => val_onGrid _ w
  G_pval := fun p hp i => by
    obtain ⟨k, e, h1, _, _, he⟩ := fp16_prod_exact rfl rfl (p i) (hp i)
    rw [he]; exact onGrid_intCast_mul k (e - 23) _ (by omega)
  prod_exact := cdna1_prod_exact

/-! ## Completeness and the merge laws -/

/-- An input with the operand pairs of a list at `0, 1, 2, …` and zero pairs elsewhere. -/
def wordsInput1 (ws : List (cdna1F16.a.Word × cdna1F16.b.Word)) : ℕ → cdna1F16.a.Word × cdna1F16.b.Word :=
  fun j => ws.getD j (0, 0)

/-- CDNA 1: inputs on three products that separate the four trees `x + y + z`, `(x + y) + z`,
`(x + z) + y` and `x + (y + z)`. -/
def cdna1In3 : List (ℕ → cdna1F16.a.Word × cdna1F16.b.Word) :=
  [wordsInput1 [(0x4e67, 0x2140), (0xd10e, 0x1b16), (0x853d, 0xacf4)],
   wordsInput1 [(0x7a30, 0xefb6), (0xeb75, 0xc96f), (0x79c0, 0xc7c2)],
   wordsInput1 [(0xfbcc, 0x22d7), (0xbc5e, 0xd863), (0xdc39, 0x81cc)]]

theorem cdna1_table3 : (MMAlgebra.codes3Unit.map fun κ => cdna1In3.map fun q =>
    MMAlgebra.evCR (mcMachine cdna1F16) (fl32 false) q (κ.realize 0 1 2)).Nodup := by
  decide +kernel

theorem getD_mem_or {γ : Type} (d : γ) : ∀ (ws : List γ) (j : ℕ), ws.getD j d ∈ ws ∨ ws.getD j d = d
  | [], j => Or.inr (by simp)
  | w :: ws, 0 => Or.inl (by simp)
  | w :: ws, j + 1 => by
    simp only [List.getD_cons_succ]
    rcases getD_mem_or d ws j with h | h
    · exact Or.inl (List.mem_cons_of_mem _ h)
    · exact Or.inr h

theorem finiteIn_words (ws : List (cdna1F16.a.Word × cdna1F16.b.Word))
    (h : ∀ q ∈ ws, ((cdna1F16.a.read q.1).toFinite).isSome ∧ ((cdna1F16.b.read q.2).toFinite).isSome)
    (g : ℕ → ℕ) : FiniteIn cdna1F16 (fun x => wordsInput1 ws (g x)) := by
  intro i
  show ((cdna1F16.a.read (ws.getD (g i) (0, 0)).1).toFinite).isSome ∧
    ((cdna1F16.b.read (ws.getD (g i) (0, 0)).2).toFinite).isSome
  rcases getD_mem_or (0, 0) ws (g i) with hm | hz
  · exact h _ hm
  · rw [hz]; decide +kernel

theorem cdna1_adm : ∀ q ∈ cdna1In3, ∀ g : ℕ → ℕ, FiniteIn cdna1F16 (fun x => q (g x)) := by
  intro q hq g
  simp only [cdna1In3, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl <;> exact finiteIn_words _ (by decide +kernel) g

/-- **CDNA 1 (fp16), completeness for terms.** Two terms from `+0` with blocks of 4 slots over
the same products, each once, with different correctly rounded normal forms differ on an input of
finite operands that is zero outside at most three of the products. -/
theorem cdna1_term_complete (t₁ t₂ : MMAlgebra.Term) (hw₁ : MMAlgebra.TermWF 4 t₁)
    (hw₂ : MMAlgebra.TermWF 4 t₂) (n₁ : t₁.leaves.Nodup) (n₂ : t₂.leaves.Nodup)
    (hl : ∀ i, i ∈ t₁.leaves ↔ i ∈ t₂.leaves) (hne : MMAlgebra.nfC t₁ ≠ MMAlgebra.nfC t₂) :
    ∃ (s : List ℕ) (q : ℕ → cdna1F16.a.Word × cdna1F16.b.Word), s.length ≤ 3 ∧
      (∀ i, i ∉ s → q i = (0, 0)) ∧ FiniteIn cdna1F16 q ∧
      MMAlgebra.eval (mcMachine cdna1F16) q 0 0 t₁ ≠ MMAlgebra.eval (mcMachine cdna1F16) q 0 0 t₂ := by
  obtain ⟨s, q, hs, hz, ⟨p, hp, hq⟩, hne'⟩ :=
    MMAlgebra.cr_term_complete cdna1Alg cdna1In3 cdna1_adm cdna1_table3 t₁ t₂ hw₁ hw₂ n₁ n₂ hl hne
  refine ⟨s, q, hs, hz, ?_, hne'⟩
  intro i
  rcases hq i with h | h
  · rw [h]; decide +kernel
  · rw [h]; exact hp i

/-- **CDNA 1 (fp16): terms are equivalent on finite inputs exactly when their correctly rounded
normal forms agree.** -/
theorem cdna1_term_equiv_iff (t₁ t₂ : MMAlgebra.Term) (hw₁ : MMAlgebra.TermWF 4 t₁)
    (hw₂ : MMAlgebra.TermWF 4 t₂) (n₁ : t₁.leaves.Nodup) (n₂ : t₂.leaves.Nodup)
    (hl : ∀ i, i ∈ t₁.leaves ↔ i ∈ t₂.leaves) :
    (∀ q, FiniteIn cdna1F16 q →
        MMAlgebra.eval (mcMachine cdna1F16) q 0 0 t₁ = MMAlgebra.eval (mcMachine cdna1F16) q 0 0 t₂) ↔
      MMAlgebra.nfC t₁ = MMAlgebra.nfC t₂ := by
  constructor
  · intro h
    apply Classical.byContradiction; intro hne
    obtain ⟨_, q, _, _, hq, hd⟩ := cdna1_term_complete t₁ t₂ hw₁ hw₂ n₁ n₂ hl hne
    exact hd (h q hq)
  · intro h q hq
    have e₁ := MMAlgebra.cr_sound cdna1Alg q hq t₁ hw₁ n₁
    have e₂ := MMAlgebra.cr_sound cdna1Alg q hq t₂ hw₂ n₂
    rw [h] at e₁
    exact e₁.trans e₂.symm

/-- **The merge law of CDNA 1.** A first block holding one product `x` merges into the next block:
`[x] [J] = [x J]` on every input of finite operands. -/
theorem cdna1_merge {x : ℕ} (B₁ B₂ B : List (Option ℕ)) (h₁ : MMAlgebra.blockLeaves B₁ = [x])
    (hB : (MMAlgebra.blockLeaves B).Perm (x :: MMAlgebra.blockLeaves B₂))
    (l₁ : B₁.length = 4) (l₂ : B₂.length = 4) (l : B.length = 4)
    (hn : (x :: MMAlgebra.blockLeaves B₂).Nodup) (q : ℕ → cdna1F16.a.Word × cdna1F16.b.Word)
    (hq : FiniteIn cdna1F16 q) :
    MMAlgebra.eval (mcMachine cdna1F16) q 0 0 (.blk (.blk .zero B₁) B₂) =
      MMAlgebra.eval (mcMachine cdna1F16) q 0 0 (.blk .zero B) := by
  have hl₁ : (MMAlgebra.Term.blk (.blk .zero B₁) B₂).leaves = x :: MMAlgebra.blockLeaves B₂ := by
    show ([] ++ MMAlgebra.blockLeaves B₁) ++ MMAlgebra.blockLeaves B₂ = _
    rw [h₁]; rfl
  have hl : (MMAlgebra.Term.blk .zero B).leaves = MMAlgebra.blockLeaves B := by
    show [] ++ MMAlgebra.blockLeaves B = _
    rw [List.nil_append]
  have e₁ := MMAlgebra.cr_sound cdna1Alg q hq (.blk (.blk .zero B₁) B₂) ⟨⟨trivial, l₁⟩, l₂⟩
    (by rw [hl₁]; exact hn)
  have e₂ := MMAlgebra.cr_sound cdna1Alg q hq (.blk .zero B) ⟨trivial, l⟩
    (by rw [hl]; exact hB.nodup_iff.mpr hn)
  have hnf : MMAlgebra.nfC (.blk (.blk .zero B₁) B₂) = MMAlgebra.nfC (.blk .zero B) := by
    show MMAlgebra.LTree.mk () (MMAlgebra.optKid () (MMAlgebra.LTree.mk ()
        ([] ++ (MMAlgebra.blockLeaves B₁).map fun i => (((), MMAlgebra.LTree.leaf i) : Unit × _))) ++
        (MMAlgebra.blockLeaves B₂).map fun i => (((), MMAlgebra.LTree.leaf i) : Unit × _)) =
      MMAlgebra.LTree.mk () ([] ++ (MMAlgebra.blockLeaves B).map fun i => (((), MMAlgebra.LTree.leaf i) : Unit × _))
    rw [h₁]
    simp only [List.nil_append, List.map_cons, List.map_nil]
    show MMAlgebra.LTree.mk () ((((), MMAlgebra.LTree.leaf x) : Unit × _) ::
        (MMAlgebra.blockLeaves B₂).map fun i => (((), MMAlgebra.LTree.leaf i) : Unit × _)) = _
    apply MMAlgebra.mk_perm
    · have := hB.symm.map (fun i => (((), MMAlgebra.LTree.leaf i) : Unit × MMAlgebra.LTree Unit Unit))
      simpa using this
    · refine ⟨?_, ?_⟩
      · have := MMAlgebra.kidsLeaves_leafs (N := Unit) () (x :: MMAlgebra.blockLeaves B₂)
        simp only [List.map_cons] at this
        rw [this]; exact hn
      · intro c hc
        simp only [List.mem_cons, List.mem_map] at hc
        rcases hc with rfl | ⟨i, _, rfl⟩ <;> simp [MMAlgebra.LTree.leaves]
  exact e₁.trans (by rw [hnf]; exact e₂.symm)

/-- **Two one-product blocks added: `[x] ⊕ [y] = [x y]` on CDNA 1**, on every input of finite
operands. -/
theorem cdna1_add_merge {x y : ℕ} (B₁ B₂ B : List (Option ℕ)) (h₁ : MMAlgebra.blockLeaves B₁ = [x])
    (h₂ : MMAlgebra.blockLeaves B₂ = [y]) (hB : (MMAlgebra.blockLeaves B).Perm [x, y])
    (l₁ : B₁.length = 4) (l₂ : B₂.length = 4) (l : B.length = 4) (hxy : x ≠ y)
    (q : ℕ → cdna1F16.a.Word × cdna1F16.b.Word) (hq : FiniteIn cdna1F16 q) :
    MMAlgebra.eval (mcMachine cdna1F16) q 0 0 (.add (.blk .zero B₁) (.blk .zero B₂)) =
      MMAlgebra.eval (mcMachine cdna1F16) q 0 0 (.blk .zero B) := by
  have hn : [x, y].Nodup := by simp [hxy]
  have e₁ := MMAlgebra.cr_sound cdna1Alg q hq (.add (.blk .zero B₁) (.blk .zero B₂))
    ⟨⟨trivial, l₁⟩, ⟨trivial, l₂⟩⟩ (by
      show ([] ++ MMAlgebra.blockLeaves B₁) ++ ([] ++ MMAlgebra.blockLeaves B₂) |>.Nodup
      rw [h₁, h₂]; exact hn)
  have e₂ := MMAlgebra.cr_sound cdna1Alg q hq (.blk .zero B) ⟨trivial, l⟩
    (by show ([] ++ MMAlgebra.blockLeaves B).Nodup; rw [List.nil_append]; exact hB.nodup_iff.mpr hn)
  have hnf : MMAlgebra.nfC (.add (.blk .zero B₁) (.blk .zero B₂)) = MMAlgebra.nfC (.blk .zero B) := by
    show MMAlgebra.LTree.mk () (MMAlgebra.optKid () (MMAlgebra.LTree.mk ()
        ([] ++ (MMAlgebra.blockLeaves B₁).map fun i => (((), MMAlgebra.LTree.leaf i) : Unit × _))) ++
        MMAlgebra.optKid () (MMAlgebra.LTree.mk ()
        ([] ++ (MMAlgebra.blockLeaves B₂).map fun i => (((), MMAlgebra.LTree.leaf i) : Unit × _)))) =
      MMAlgebra.LTree.mk () ([] ++ (MMAlgebra.blockLeaves B).map fun i => (((), MMAlgebra.LTree.leaf i) : Unit × _))
    rw [h₁, h₂]
    simp only [List.nil_append, List.map_cons, List.map_nil]
    show MMAlgebra.LTree.mk () [((), MMAlgebra.LTree.leaf x), ((), MMAlgebra.LTree.leaf y)] = _
    apply MMAlgebra.mk_perm
    · have := hB.symm.map (fun i => (((), MMAlgebra.LTree.leaf i) : Unit × MMAlgebra.LTree Unit Unit))
      simpa using this
    · refine ⟨by simp [MMAlgebra.LTree.kidsLeaves, MMAlgebra.LTree.leaves, hxy], ?_⟩
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> simp [MMAlgebra.LTree.leaves]
  exact e₁.trans (by rw [hnf]; exact e₂.symm)

end MMAlgebra.MC
