import MatrixCore.MC.LossCondition

/-! # A non-monotone family with an exact threshold (CDNA 3 FP16)

Raising the lead product of `cdna3F16LeadBlock wa wb n` to `2^-9` lowers the output exactly when
`2^21 − m_a m_b < 64 n`. -/

namespace MatrixCore

/-- The lead operand `w`, then `n` operands `0x0C00 = 2^-12`, then `7 − n` zeros. -/
def leadOperands (w : BitVec 16) (n : ℕ) : List (BitVec 16) :=
  w :: (List.replicate n 0x0C00 ++ List.replicate (7 - n) 0)

/-- CDNA 3 FP16 block: the lead product `wa · wb`, `n` products `2^-24`, zeros, and `c = 0`. -/
def cdna3F16LeadBlock (wa wb : BitVec 16) (n : ℕ) : BlockInput cdna3F16 :=
  ⟨leadOperands wa n, leadOperands wb n, 0⟩

/-- The decoded operands after the lead: `n` copies of `2^-12` and `7 − n` zeros. -/
def leadTail (n : ℕ) : List Unpacked :=
  List.replicate n ⟨false, 1024, -12, 10⟩ ++ List.replicate (7 - n) ⟨false, 0, -14, 10⟩

/-- The products after the lead: `n` copies of `2^-24` and `7 − n` zeros. -/
def leadTailProducts (n : ℕ) : List Unpacked :=
  List.replicate n ⟨false, 1048576, -24, 20⟩ ++ List.replicate (7 - n) ⟨false, 0, -28, 20⟩

/-! ## Evaluating the family -/

theorem mapM_replicate_some {f : α → Option β} {a : α} {b : β} (h : f a = some b) :
    ∀ n : ℕ, (List.replicate n a).mapM f = some (List.replicate n b)
  | 0 => rfl
  | n + 1 => by
    simp [List.replicate_succ, List.mapM_cons, h, mapM_replicate_some h n]

theorem mapM_lead {f : α → Option β} {w a z : α} {u b c : β} (hw : f w = some u)
    (ha : f a = some b) (hz : f z = some c) (n k : ℕ) :
    (w :: (List.replicate n a ++ List.replicate k z)).mapM f =
      some (u :: (List.replicate n b ++ List.replicate k c)) := by
  rw [List.mapM_cons, mapM_append_option, mapM_replicate_some ha n, mapM_replicate_some hz k]
  simp [hw]

theorem leadOperands_mapM {w : BitVec 16} {u : Unpacked} (hw : fp16.decode w = .finite u)
    (n : ℕ) :
    (leadOperands w n).mapM (fun w => (fp16.decode w).toFinite) = some (u :: leadTail n) :=
  mapM_lead (f := fun w : BitVec 16 => (fp16.decode w).toFinite) (by simp only [hw]; rfl)
    (by decide) (by decide) n (7 - n)

theorem prepare_of_mapM {P : Model} {x : BlockInput P} {A B : List Unpacked} {c : Unpacked}
    (ha : x.a.mapM (fun w => (P.a.read w).toFinite) = some A)
    (hb : x.b.mapM (fun w => (P.b.read w).toFinite) = some B)
    (hc : (fp32.decode x.c).toFinite = some c) : prepare x = some ⟨A, B, c⟩ := by
  unfold prepare
  rw [ha, hb, hc]
  rfl

theorem prepare_cdna3F16LeadBlock {wa wb : BitVec 16} {ua ub : Unpacked}
    (ha : fp16.decode wa = .finite ua) (hb : fp16.decode wb = .finite ub) (n : ℕ) :
    prepare (cdna3F16LeadBlock wa wb n) =
      some ⟨ua :: leadTail n, ub :: leadTail n, ⟨false, 0, -126, 23⟩⟩ :=
  prepare_of_mapM (leadOperands_mapM ha n) (leadOperands_mapM hb n)
    (show (fp32.decode (0 : F32)).toFinite = some ⟨false, 0, -126, 23⟩ by decide)

theorem cdna3F16LeadBlock_products (ua ub c : Unpacked) (n : ℕ) :
    Prepared.p ⟨ua :: leadTail n, ub :: leadTail n, c⟩ = ua.mul ub :: leadTailProducts n := by
  have hq : Unpacked.mul ⟨false, 1024, -12, 10⟩ ⟨false, 1024, -12, 10⟩ =
      ⟨false, 1048576, -24, 20⟩ := by decide
  have hz : Unpacked.mul ⟨false, 0, -14, 10⟩ ⟨false, 0, -14, 10⟩ = ⟨false, 0, -28, 20⟩ := by
    decide
  unfold Prepared.p leadTail leadTailProducts
  simp only [List.zipWith_cons_cons, List.zipWith_self, List.map_append, List.map_replicate, hq, hz]

theorem foldl_maxExpStep_replicate {e : ℤ} {q : Unpacked} (hq : q.m = 0 ∨ q.e ≤ e) :
    ∀ n, (List.replicate n q).foldl maxExpStep (some e) = some e
  | 0 => rfl
  | n + 1 => by
    rw [List.replicate_succ, List.foldl_cons]
    have : maxExpStep (some e) q = some e := by
      unfold maxExpStep
      rcases hq with h | h
      · simp [h]
      · split
        · rfl
        · simp only [Option.some.injEq]; omega
    rw [this]
    exact foldl_maxExpStep_replicate hq n

theorem sumQ_replicate (v : ℚ) : ∀ n : ℕ, sumQ (List.replicate n v) = n * v
  | 0 => by simp [sumQ]
  | n + 1 => by
    rw [List.replicate_succ, sumQ, sumQ_replicate v n]
    have : ((n + 1 : ℕ) : ℚ) * v = (n : ℚ) * v + v := by rw [Rat.natCast_add, Rat.add_mul]; simp
    rw [this]
    grind

theorem cdna3F16LeadBlock_sAcc (L : Unpacked) (hL : L.m ≠ 0) (he : -24 ≤ L.e) (n : ℕ)
    (a b : List Unpacked) (hp : Prepared.p ⟨a, b, ⟨false, 0, -126, 23⟩⟩ = L :: leadTailProducts n) :
    alignedAccumulation cdna3F16 ⟨a, b, ⟨false, 0, -126, 23⟩⟩ =
      truncGrid L.value (L.e - 24) + n * truncGrid (pow2 (-24)) (L.e - 24) := by
  have hmax : maxExp (L :: leadTailProducts n) = some L.e := by
    unfold maxExp leadTailProducts
    rw [List.foldl_cons, List.foldl_append]
    have : maxExpStep none L = some L.e := by unfold maxExpStep; simp [hL]
    rw [this, foldl_maxExpStep_replicate (Or.inr (by show (-24 : ℤ) ≤ L.e; exact he)) n,
      foldl_maxExpStep_replicate (Or.inl rfl) (7 - n)]
  have hps : productSum cdna3F16 (L :: leadTailProducts n) =
      (some L.e, sumQ ((L :: leadTailProducts n).map fun p => truncMantissa p.value L.e 24)) := by
    show alignedSum 1 _ = _
    unfold alignedSum
    rw [hmax]
  have hq : (⟨false, 1048576, -24, 20⟩ : Unpacked).value = pow2 (-24) := by decide +kernel
  have hz : (⟨false, 0, -28, 20⟩ : Unpacked).value = 0 := by decide +kernel
  have hsum : sumQ ((L :: leadTailProducts n).map fun p => truncMantissa p.value L.e 24) =
      truncGrid L.value (L.e - 24) + n * truncGrid (pow2 (-24)) (L.e - 24) := by
    unfold leadTailProducts
    simp only [List.map_cons, List.map_append, List.map_replicate, sumQ, sumQ_append,
      sumQ_replicate, hq, hz, truncMantissa, truncGrid_zero]
    have : (L.e - ((24 : ℕ) : ℤ)) = L.e - 24 := rfl
    rw [this]
    grind
  have hc : cExp cdna3F16 ⟨false, 0, -126, 23⟩ = some (-126) := rfl
  have hsc : shiftedC cdna3F16 L.e (-126) ⟨false, 0, -126, 23⟩ = 0 := by
    show rdGrid (Unpacked.value ⟨false, 0, -126, 23⟩) (L.e - 24) = 0
    rw [(Unpacked.value_eq_zero_iff _).mpr rfl, rdGrid_zero]
  unfold alignedAccumulation
  simp only
  rw [hp, hps]
  unfold lateSum
  rw [hc]
  simp only [show (-126 : ℤ) ≤ L.e by omega, ↓reduceIte, hsc, Rat.add_zero]
  exact hsum

theorem evalBlock_of_stages {P : Model} {x : BlockInput P} {px : Prepared} {s : ℚ} {d : F32}
    (hla : x.a.length = P.nfma) (hlb : x.b.length = P.nfma) (hp : prepare x = some px)
    (hs : accumulate P px = .ok s) (hd : fl32 (!P.subnormals) s = some d) :
    evalBlock x = .ok ⟨px, s, d⟩ := by
  have hl : ¬ (x.a.length ≠ P.nfma ∨ x.b.length ≠ P.nfma) := by omega
  unfold evalBlock
  simp only [hl, ↓reduceIte, hp, hs, hd]

theorem cdna3F16LeadBlock_eval {wa wb : BitVec 16} {ua ub : Unpacked}
    (ha : fp16.decode wa = .finite ua) (hb : fp16.decode wb = .finite ub)
    (hL : (ua.mul ub).m ≠ 0) (he : -24 ≤ (ua.mul ub).e)
    (hov : absQ (ua.mul ub).value < pow2 128) {n : ℕ} (hn : n ≤ 7) {S : ℚ}
    (hS : truncGrid (ua.mul ub).value ((ua.mul ub).e - 24) +
      n * truncGrid (pow2 (-24)) ((ua.mul ub).e - 24) = S)
    (hfin : FiniteValue32 S) (hlt : absQ S < overflowThreshold32) :
    ∃ d, blockBits (cdna3F16LeadBlock wa wb n) = .ok d ∧ wordValue d = S := by
  have hp := prepare_cdna3F16LeadBlock ha hb n
  have hprod := cdna3F16LeadBlock_products ua ub ⟨false, 0, -126, 23⟩ n
  have hacc := cdna3F16LeadBlock_sAcc (ua.mul ub) hL he n _ _ hprod
  rw [hS] at hacc
  have hnov : Prepared.productOverflows ⟨ua :: leadTail n, ub :: leadTail n,
      ⟨false, 0, -126, 23⟩⟩ = false := by
    unfold Prepared.productOverflows
    rw [hprod, List.any_eq_false]
    intro p hp' hge
    simp only [decide_eq_true_eq] at hge
    simp only [leadTailProducts, List.mem_cons, List.mem_append, List.mem_replicate] at hp'
    rcases hp' with rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact Rat.not_le.mpr hov hge
    · exact absurd hge (by decide +kernel)
    · exact absurd hge (by decide +kernel)
  have hacc' : accumulate cdna3F16 ⟨ua :: leadTail n, ub :: leadTail n, ⟨false, 0, -126, 23⟩⟩ =
      .ok S := by
    unfold accumulate
    rw [hnov, hacc.symm]
    rfl
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp ((rne32_isSome_iff S).mpr hlt)
  have hd' : fl32 (!cdna3F16.subnormals) S = some d := by
    show fl32 false S = some d
    rw [fl32_false]; exact hd
  have hlen : (leadOperands wa n).length = 8 ∧ (leadOperands wb n).length = 8 := by
    simp [leadOperands]; omega
  have hev := evalBlock_of_stages (x := cdna3F16LeadBlock wa wb n) hlen.1 hlen.2 hp hacc' hd'
  refine ⟨d, ?_, ?_⟩
  · unfold blockBits; rw [hev]; rfl
  · rw [wordValue_of_fl32_false (by rw [fl32_false]; exact hd), rneValue_of_finiteValue32 hfin]

theorem finiteValue32_mul_pow2_neg30 {N : ℕ} (hN : N < 16777216) :
    FiniteValue32 ((N : ℚ) * pow2 (-30)) ∧ absQ ((N : ℚ) * pow2 (-30)) < overflowThreshold32 := by
  have hq := pow2_pos (-30)
  have hN0 : (0 : ℚ) ≤ N := Rat.natCast_nonneg
  refine ⟨⟨N, -7, by decide, by decide, by omega, ?_⟩, ?_⟩
  · rw [Rat.intCast_natCast]; rfl
  · rw [absQ_of_nonneg (Rat.mul_nonneg hN0 (Rat.le_of_lt hq))]
    have h1 : (N : ℚ) < 16777216 := by exact_mod_cast hN
    have h2 := Rat.mul_lt_mul_of_pos_right h1 hq
    have h3 : (16777216 : ℚ) * pow2 (-30) < overflowThreshold32 := by decide +kernel
    grind

/-! ## The family theorem -/

theorem lead_value {ua ub : Unpacked} (hs : ua.negative = ub.negative) (ht : ua.t = 10)
    (ht' : ub.t = 10) (he : ua.e + ub.e = -10) :
    (ua.mul ub).value = ((ua.m * ub.m : ℕ) : ℚ) * pow2 (-30) := by
  unfold Unpacked.mul Unpacked.value
  simp only [hs, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  congr 2
  rw [ht, ht']; omega

/-- Lead `a₁ b₁` gives `d = (m_a m_b + 64 n)·2^-30`; lead `0x0001 · 0x7800 = 2^-9` gives `2^-9`. -/
theorem cdna3F16LeadBlock_outputs {wa wb : BitVec 16} {ua ub : Unpacked}
    (ha : fp16.decode wa = .finite ua) (hb : fp16.decode wb = .finite ub)
    (hs : ua.negative = ub.negative) (hm : 0 < ua.m * ub.m) (he : ua.e + ub.e = -10)
    {n : ℕ} (hn : n ≤ 7) :
    ∃ d d', blockBits (cdna3F16LeadBlock wa wb n) = .ok d ∧
      blockBits (cdna3F16LeadBlock 0x0001 0x7800 n) = .ok d' ∧
      wordValue d = ((ua.m * ub.m + 64 * n : ℕ) : ℚ) * pow2 (-30) ∧ wordValue d' = pow2 (-9) := by
  obtain ⟨hta, hma⟩ := decodeNat_bounded (f := fp16) ha
  obtain ⟨htb, hmb⟩ := decodeNat_bounded (f := fp16) hb
  have ht : ua.t = 10 := hta
  have ht' : ub.t = 10 := htb
  have hma' : ua.m < 2048 := hma
  have hmb' : ub.m < 2048 := hmb
  have hprod : ua.m * ub.m < 4194304 := by
    have := Nat.mul_lt_mul'' hma' hmb'; omega
  have hval := lead_value hs ht ht' he
  have hq30 := pow2_pos (-30)
  have hLe : (ua.mul ub).e = -10 := he
  have hLm : (ua.mul ub).m ≠ 0 := by show ua.m * ub.m ≠ 0; omega
  have hgrid : OnGrid (ua.mul ub).value (-34) := by
    have := Unpacked.value_onGrid (ua.mul ub)
    refine this.mono ?_
    show (-34 : ℤ) ≤ (ua.e + ub.e) - ((ua.t + ub.t : ℕ) : ℤ)
    rw [ht, ht']; omega
  have h24 : OnGrid (pow2 (-24)) (-34) := by
    have := onGrid_pow2 (-24) 10
    exact this
  have hS : truncGrid (ua.mul ub).value ((ua.mul ub).e - 24) +
      n * truncGrid (pow2 (-24)) ((ua.mul ub).e - 24) =
      ((ua.m * ub.m + 64 * n : ℕ) : ℚ) * pow2 (-30) := by
    rw [hLe, show (-10 : ℤ) - 24 = -34 by decide, truncGrid_of_onGrid hgrid,
      truncGrid_of_onGrid h24, hval]
    have c24 : pow2 (-24) = 64 * pow2 (-30) := by decide +kernel
    rw [c24, Rat.natCast_add, Rat.natCast_mul]
    grind
  have hov : absQ (ua.mul ub).value < pow2 128 := by
    rw [hval, absQ_of_nonneg (Rat.mul_nonneg Rat.natCast_nonneg (Rat.le_of_lt hq30))]
    have h1 : ((ua.m * ub.m : ℕ) : ℚ) < 4194304 := by exact_mod_cast hprod
    have h2 := Rat.mul_lt_mul_of_pos_right h1 hq30
    have h3 : (4194304 : ℚ) * pow2 (-30) < pow2 128 := by decide +kernel
    grind
  obtain ⟨hfin, hlt⟩ := finiteValue32_mul_pow2_neg30 (N := ua.m * ub.m + 64 * n) (by omega)
  obtain ⟨d, hd, hdv⟩ := cdna3F16LeadBlock_eval ha hb hLm (by omega) hov hn hS hfin hlt
  have ha' : fp16.decode 0x0001 = .finite ⟨false, 1, -14, 10⟩ := by decide
  have hb' : fp16.decode 0x7800 = .finite ⟨false, 1024, 15, 10⟩ := by decide
  have hS' : truncGrid (Unpacked.mul ⟨false, 1, -14, 10⟩ ⟨false, 1024, 15, 10⟩).value
      ((Unpacked.mul ⟨false, 1, -14, 10⟩ ⟨false, 1024, 15, 10⟩).e - 24) +
      n * truncGrid (pow2 (-24))
        ((Unpacked.mul ⟨false, 1, -14, 10⟩ ⟨false, 1024, 15, 10⟩).e - 24) =
      ((2097152 : ℕ) : ℚ) * pow2 (-30) := by
    have e1 : truncGrid (Unpacked.mul ⟨false, 1, -14, 10⟩ ⟨false, 1024, 15, 10⟩).value
        ((Unpacked.mul ⟨false, 1, -14, 10⟩ ⟨false, 1024, 15, 10⟩).e - 24) =
        ((2097152 : ℕ) : ℚ) * pow2 (-30) := by decide +kernel
    have e2 : truncGrid (pow2 (-24))
        ((Unpacked.mul ⟨false, 1, -14, 10⟩ ⟨false, 1024, 15, 10⟩).e - 24) = 0 := by
      decide +kernel
    rw [e1, e2]; grind
  obtain ⟨hfin', hlt'⟩ := finiteValue32_mul_pow2_neg30 (N := 2097152) (by decide)
  obtain ⟨d', hd', hdv'⟩ := cdna3F16LeadBlock_eval ha' hb' (by decide) (by decide)
    (by decide +kernel) hn hS' hfin' hlt'
  have c9 : ((2097152 : ℕ) : ℚ) * pow2 (-30) = pow2 (-9) := by decide +kernel
  exact ⟨d, d', hd, hd', hdv, by rw [hdv', c9]⟩

/-- Raising the lead `a₁ b₁` to `2^-9` lowers the output exactly when `2^21 − m_a m_b < 64 n`. -/
theorem cdna3F16LeadBlock_decrease_iff {wa wb : BitVec 16} {ua ub : Unpacked}
    (ha : fp16.decode wa = .finite ua) (hb : fp16.decode wb = .finite ub)
    (hs : ua.negative = ub.negative) (hm : 0 < ua.m * ub.m) (he : ua.e + ub.e = -10)
    {n : ℕ} (hn : n ≤ 7) :
    ∃ d d', blockBits (cdna3F16LeadBlock wa wb n) = .ok d ∧
      blockBits (cdna3F16LeadBlock 0x0001 0x7800 n) = .ok d' ∧
      (wordValue d' < wordValue d ↔ (2 ^ 21 : ℤ) - (ua.m * ub.m : ℕ) < 64 * n) := by
  obtain ⟨d, d', hd, hd', hv, hv'⟩ := cdna3F16LeadBlock_outputs ha hb hs hm he hn
  refine ⟨d, d', hd, hd', ?_⟩
  rw [hv, hv']
  have c9 : pow2 (-9) = ((2097152 : ℕ) : ℚ) * pow2 (-30) := by decide +kernel
  rw [c9, Rat.mul_lt_mul_right (pow2_pos (-30)), Rat.natCast_lt_natCast]
  omega

theorem productValues_leadOperands (wa wb : BitVec 16) (n : ℕ) :
    productValues cdna3F16 (leadOperands wa n) (leadOperands wb n) =
      cdna3F16.a.wordValue wa * cdna3F16.b.wordValue wb ::
        productValues cdna3F16 (List.replicate n 0x0C00 ++ List.replicate (7 - n) 0)
          (List.replicate n 0x0C00 ++ List.replicate (7 - n) 0) := rfl

theorem zip_self_all_le : ∀ l : List ℚ, (l.zip l).all (fun q => decide (q.1 ≤ q.2)) = true
  | [] => rfl
  | a :: l => by
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨Rat.le_refl, zip_self_all_le l⟩

theorem wordValue_of_decode16 {w : BitVec 16} {u : Unpacked} (h : fp16.decode w = .finite u) :
    cdna3F16.a.wordValue w = u.value := by
  unfold InputFormat.wordValue
  show ((fp16.decode w).toFinite.map Unpacked.value).getD 0 = u.value
  rw [h]; rfl

theorem cdna3F16LeadBlock_productsLE_iff {wa wb : BitVec 16} {ua ub : Unpacked}
    (ha : fp16.decode wa = .finite ua) (hb : fp16.decode wb = .finite ub)
    (hs : ua.negative = ub.negative) (he : ua.e + ub.e = -10) (n : ℕ) :
    productsLE (cdna3F16LeadBlock wa wb n) (cdna3F16LeadBlock 0x0001 0x7800 n) = true ↔
      ua.m * ub.m ≤ 2 ^ 21 := by
  obtain ⟨hta, _⟩ := decodeNat_bounded (f := fp16) ha
  obtain ⟨htb, _⟩ := decodeNat_bounded (f := fp16) hb
  have hval := lead_value hs hta htb he
  have hwa := wordValue_of_decode16 ha
  have hwb : cdna3F16.b.wordValue wb = ub.value := wordValue_of_decode16 hb
  generalize hw1 : (0x0001 : BitVec 16) = w1
  generalize hw2 : (0x7800 : BitVec 16) = w2
  have hv1 : cdna3F16.a.wordValue w1 = (⟨false, 1, -14, 10⟩ : Unpacked).value :=
    wordValue_of_decode16 (by rw [← hw1]; decide)
  have hv2 : cdna3F16.b.wordValue w2 = (⟨false, 1024, 15, 10⟩ : Unpacked).value :=
    wordValue_of_decode16 (by rw [← hw2]; decide)
  have h1 : (⟨false, 1, -14, 10⟩ : Unpacked).value * (⟨false, 1024, 15, 10⟩ : Unpacked).value =
      ((2097152 : ℕ) : ℚ) * pow2 (-30) := by decide +kernel
  unfold productsLE cdna3F16LeadBlock
  simp only
  rw [productValues_leadOperands, productValues_leadOperands, hwa, hwb, hv1, hv2, h1]
  simp only [List.length_cons, beq_self_eq_true, List.zip_cons_cons, List.all_cons,
    zip_self_all_le, Bool.true_and, Bool.and_true, decide_eq_true_eq]
  rw [← Unpacked.value_mul, hval, ← Rat.not_lt, Rat.mul_lt_mul_right (pow2_pos (-30)),
    Rat.natCast_lt_natCast]
  omega

/-- Raising the lead to `2^-9` is non-monotone exactly when `m_a m_b ≤ 2^21` and `2^21 − m_a m_b < 64 n`. -/
theorem cdna3F16LeadBlock_nonmonotone_iff {wa wb : BitVec 16} {ua ub : Unpacked}
    (ha : fp16.decode wa = .finite ua) (hb : fp16.decode wb = .finite ub)
    (hs : ua.negative = ub.negative) (hm : 0 < ua.m * ub.m) (he : ua.e + ub.e = -10)
    {n : ℕ} (hn : n ≤ 7) :
    ProductNonmonotone (cdna3F16LeadBlock wa wb n) (cdna3F16LeadBlock 0x0001 0x7800 n) ↔
      ua.m * ub.m ≤ 2 ^ 21 ∧ (2 ^ 21 : ℤ) - (ua.m * ub.m : ℕ) < 64 * n := by
  obtain ⟨d, d', hd, hd', hiff⟩ := cdna3F16LeadBlock_decrease_iff ha hb hs hm he hn
  rw [← cdna3F16LeadBlock_productsLE_iff ha hb hs he n, ← hiff]
  unfold ProductNonmonotone
  constructor
  · rintro ⟨hp, _, e, e', he1, he2, hlt⟩
    rw [hd] at he1; rw [hd'] at he2
    cases he1; cases he2
    exact ⟨hp, hlt⟩
  · rintro ⟨hp, hlt⟩
    exact ⟨hp, rfl, d, d', hd, hd', hlt⟩

end MatrixCore
