import MMAlgebra.Divergence
import MMAlgebraMC.Chain
import OzakiMC.Cancellation
import OzakiMC.Models

/-! # Inside the exact region every schedule agrees (matrix-core model)

`mcMachine P` is the matrix-core model as a `MMAlgebra.Machine`: binary32 accumulator words,
operand pairs, `blockBits` for a block (an empty slot is the zero pair), and binary32
round-to-nearest-even addition. On an exact configuration (SFMA, CDNA 1, CDNA 2, and CDNA 3 fp16
and bf16) with integer operands, an integer `c` and `|c| + Σ|aᵢbᵢ| < 2^24`, every block and every
addition of every term is exact (Ozaki's exactness theorem with cancellation,
`Ozaki.MC.evalBlock_cancel`), so any two terms over the same products return the same value
(`eval_agree`). -/

open MatrixCore Ozaki.MC

namespace MMAlgebra.MC

/-- The operand pairs of a block's slots: an empty slot is the zero pair. -/
def slotPairs (P : Model) (ps : List (Option (P.a.Word × P.b.Word))) : List (P.a.Word × P.b.Word) :=
  ps.map fun o => o.getD (0, 0)

/-- The matrix-core model as a machine for reduction terms. -/
def mcMachine (P : Model) : MMAlgebra.Machine (P.a.Word × P.b.Word) F32 where
  val w := (value32 w).getD 0
  pval q := P.a.wordValue q.1 * P.b.wordValue q.2
  zero := 0
  val_zero := by decide +kernel
  block d ps := (blockBits (P := P) ⟨(slotPairs P ps).map Prod.fst, (slotPairs P ps).map Prod.snd, d⟩).toOption
  add x y := fl32 false ((value32 x).getD 0 + (value32 y).getD 0)

/-- A term without holes whose blocks all have `K` slots. -/
def TermWF (K : ℕ) : MMAlgebra.Term → Prop
  | .zero => True
  | .init => True
  | .hole => False
  | .blk t I => TermWF K t ∧ I.length = K
  | .add t u => TermWF K t ∧ TermWF K u

theorem wordValue_zero {i : InputFormat} {b : ℕ} (h : EncodesInts i b) : i.wordValue 0 = 0 := by
  obtain ⟨w, hw, _, hv⟩ := h 0 (by simp)
  rw [encodeExact_zero] at hw
  cases hw
  simpa using hv

/-- The block's exact products are the slots' products. -/
theorem exactProducts_slots {P : Model} {b : ℕ} (hE : ExactMultiplier P b) :
    ∀ ps : List (Option (P.a.Word × P.b.Word)),
      exactProducts P ((slotPairs P ps).map Prod.fst) ((slotPairs P ps).map Prod.snd) =
        (mcMachine P).slotVal ps
  | [] => by simp [exactProducts, slotPairs, sumQ, MMAlgebra.Machine.slotVal]
  | o :: ps => by
    have ih := exactProducts_slots hE ps
    rw [(mcMachine P).slotVal_cons, ← ih]
    simp only [exactProducts, slotPairs, List.map_cons, List.zipWith_cons_cons, sumQ]
    cases o with
    | none =>
      show P.a.wordValue (0 : P.a.Word) * P.b.wordValue (0 : P.b.Word) + _ = _
      rw [wordValue_zero hE.encA, wordValue_zero hE.encB]; simp
    | some q => rfl

/-- The products of a list of slots, with their integer values and magnitudes. -/
theorem slot_ints {P : Model} {b : ℕ} (hE : ExactMultiplier P b) (q : ℕ → P.a.Word × P.b.Word)
    (hq : ∀ i, IntWord P.a (q i).1 ∧ IntWord P.b (q i).2) :
    ∀ I : List (Option ℕ), ∃ zs : List ℤ,
      List.zipWith (fun w w' => P.a.wordValue w * P.b.wordValue w')
          ((slotPairs P (I.map (Option.map q))).map Prod.fst)
          ((slotPairs P (I.map (Option.map q))).map Prod.snd) = zs.map (fun z : ℤ => (z : ℚ)) ∧
        (((zs.map Int.natAbs).sum : ℕ) : ℚ) = (mcMachine P).slotAbs (I.map (Option.map q))
  | [] => ⟨[], by simp [slotPairs], by simp [MMAlgebra.Machine.slotAbs]⟩
  | o :: I => by
    obtain ⟨zs, hzs, habs⟩ := slot_ints hE q hq I
    obtain ⟨z, hz⟩ : ∃ z : ℤ, P.a.wordValue ((o.map q).getD (0, 0)).1 *
        P.b.wordValue ((o.map q).getD (0, 0)).2 = z := by
      cases o with
      | none =>
        refine ⟨0, ?_⟩
        show P.a.wordValue (0 : P.a.Word) * P.b.wordValue (0 : P.b.Word) = _
        rw [wordValue_zero hE.encA, wordValue_zero hE.encB]; simp
      | some i =>
        obtain ⟨⟨ua, hua, za, hza⟩, ⟨ub, hub, zb, hzb⟩⟩ := hq i
        refine ⟨za * zb, ?_⟩
        simp only [Option.map_some, Option.getD_some, InputFormat.wordValue, hua, hub,
          Option.map_some, Option.getD_some, hza, hzb, Rat.intCast_mul]
    refine ⟨z :: zs, ?_, ?_⟩
    · simp only [slotPairs, List.map_cons, List.zipWith_cons_cons] at hzs ⊢
      rw [hz, hzs]
    · rw [show List.map (Option.map q) (o :: I) = Option.map q o :: List.map (Option.map q) I from rfl,
        (mcMachine P).slotAbs_cons, ← habs]
      simp only [List.map_cons, List.sum_cons, Rat.natCast_add]
      have hz' : ((o.map q).map (mcMachine P).pval).getD 0 = (z : ℚ) := by
        cases o with
        | none => simp only [Option.map_none, Option.getD_none]; rw [← hz]; show (0 : ℚ) = _
                  show (0 : ℚ) = P.a.wordValue (0 : P.a.Word) * P.b.wordValue (0 : P.b.Word)
                  rw [wordValue_zero hE.encA, wordValue_zero hE.encB]; simp
        | some i => simp only [Option.map_some, Option.getD_some] at hz ⊢; rw [← hz]; rfl
      rw [hz', Ozaki.abs_intCast]

theorem natAbs_le_sum {z : ℤ} : ∀ {zs : List ℤ}, z ∈ zs → z.natAbs ≤ (zs.map Int.natAbs).sum
  | [], h => by simp at h
  | y :: ys, h => by
    simp only [List.mem_cons] at h
    simp only [List.map_cons, List.sum_cons]
    rcases h with rfl | h
    · omega
    · have := natAbs_le_sum h; omega

theorem map_intCast_inj : ∀ {xs ys : List ℤ},
    xs.map (fun z : ℤ => (z : ℚ)) = ys.map (fun z : ℤ => (z : ℚ)) → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: xs, y :: ys, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [Rat.intCast_inj.mp h.1, map_intCast_inj h.2]

theorem val_of {w : F32} {v : ℚ} (h : value32 w = some v) : (mcMachine P).val w = v := by
  simp [mcMachine, h]

/-- One block inside the exact region returns the exact sum of its inputs. -/
theorem block_int {P : Model} {b : ℕ} (hE : ExactMultiplier P b) (q : ℕ → P.a.Word × P.b.Word)
    (hq : ∀ i, IntWord P.a (q i).1 ∧ IntWord P.b (q i).2)
    {d : F32} {zd : ℤ} (hvd : value32 d = some (zd : ℚ)) (I : List (Option ℕ))
    (hlen : I.length = P.nfma) (hzd : Rat.abs (zd : ℚ) < 2 ^ (24 : ℤ))
    (habs : (mcMachine P).slotAbs (I.map (Option.map q)) < 2 ^ (24 : ℤ))
    (hsum : Rat.abs ((zd : ℚ) + (mcMachine P).slotVal (I.map (Option.map q))) ≤ 2 ^ (24 : ℤ)) :
    ∃ (o : F32) (z : ℤ), (mcMachine P).block d (I.map (Option.map q)) = some o ∧
      value32 o = some (z : ℚ) ∧ (z : ℚ) = zd + (mcMachine P).slotVal (I.map (Option.map q)) := by
  have hslots := exactProducts_slots hE (I.map (Option.map q))
  obtain ⟨zs, hzs, hzabs⟩ := slot_ints hE q hq I
  have hA : ∀ w ∈ (slotPairs P (I.map (Option.map q))).map Prod.fst, IntWord P.a w := by
    intro w hw
    simp only [slotPairs, List.map_map, List.mem_map] at hw
    obtain ⟨o, _, rfl⟩ := hw
    cases o with
    | none => exact intWord_zero hE.encA
    | some i => exact (hq i).1
  have hB : ∀ w ∈ (slotPairs P (I.map (Option.map q))).map Prod.snd, IntWord P.b w := by
    intro w hw
    simp only [slotPairs, List.map_map, List.mem_map] at hw
    obtain ⟨o, _, rfl⟩ := hw
    cases o with
    | none => exact intWord_zero hE.encB
    | some i => exact (hq i).2
  have hla : ((slotPairs P (I.map (Option.map q))).map Prod.fst).length = P.nfma := by
    simp only [slotPairs, List.length_map]; exact hlen
  have hlb : ((slotPairs P (I.map (Option.map q))).map Prod.snd).length = P.nfma := by
    simp only [slotPairs, List.length_map]; exact hlen
  -- every product, and the sum of their magnitudes, is within 2^24
  have hnat : (zs.map Int.natAbs).sum ≤ 2 ^ 24 := by
    have h24 : (2 : ℚ) ^ (24 : ℤ) = ((2 ^ 24 : ℕ) : ℚ) := by decide
    rw [← hzabs, h24] at habs
    have := Rat.natCast_lt_natCast.mp habs
    omega
  have hprod : ∀ v ∈ List.zipWith (fun w w' => P.a.wordValue w * P.b.wordValue w')
      ((slotPairs P (I.map (Option.map q))).map Prod.fst)
      ((slotPairs P (I.map (Option.map q))).map Prod.snd), absQ v ≤ pow2 24 := by
    rw [hzs]
    intro v hv
    simp only [List.mem_map] at hv
    obtain ⟨z, hz, rfl⟩ := hv
    rw [absQ_eq, Ozaki.abs_intCast, pow2_eq]
    have hle : z.natAbs ≤ (zs.map Int.natAbs).sum := natAbs_le_sum hz
    have h24 : (2 : ℚ) ^ (24 : ℤ) = ((2 ^ 24 : ℕ) : ℚ) := by decide
    rw [h24]; exact Rat.natCast_le_natCast.mpr (by omega)
  have htree : P.accumulation = .pairWiseSum → ∀ zs' : List ℤ,
      List.zipWith (fun w w' => P.a.wordValue w * P.b.wordValue w')
        ((slotPairs P (I.map (Option.map q))).map Prod.fst)
        ((slotPairs P (I.map (Option.map q))).map Prod.snd) = zs'.map (fun z : ℤ => (z : ℚ)) →
      PairwiseSumsBounded zs'.length zs' := by
    intro _ zs' hzs'
    rw [hzs] at hzs'
    have : zs' = zs := (map_intCast_inj hzs').symm
    subst this
    exact pairwiseSumsBounded_of_bound zs'.length zs' (by omega) hnat
  have hc24 : absQ (zd : ℚ) ≤ pow2 24 := by rw [absQ_eq, pow2_eq]; grind
  have hsum' : absQ ((zd : ℚ) + exactProducts P ((slotPairs P (I.map (Option.map q))).map Prod.fst)
      ((slotPairs P (I.map (Option.map q))).map Prod.snd)) ≤ pow2 24 := by
    rw [hslots, absQ_eq, pow2_eq]; exact hsum
  obtain ⟨tr, htr, hval⟩ := evalBlock_cancel
    (x := (⟨(slotPairs P (I.map (Option.map q))).map Prod.fst,
      (slotPairs P (I.map (Option.map q))).map Prod.snd, d⟩ : BlockInput P))
    hE.config hE.subA hE.subB hla hlb hA hB hvd hc24 hprod hsum' htree
  obtain ⟨Z, hZ⟩ : ∃ Z : ℤ, (mcMachine P).slotVal (I.map (Option.map q)) = Z := by
    refine ⟨zs.sum, ?_⟩
    rw [← hslots, exactProducts, hzs, sumQ_cast]
  refine ⟨tr.d, zd + Z, ?_, ?_, ?_⟩
  · show (blockBits (P := P) ⟨_, _, d⟩).toOption = _
    unfold blockBits; rw [htr]; rfl
  · rw [hval, hslots, hZ, Rat.intCast_add]
  · rw [Rat.intCast_add, ← hZ]

theorem natAbs_le_of_abs_lt {z : ℤ} (h : Rat.abs (z : ℚ) < 2 ^ (24 : ℤ)) : z.natAbs ≤ 2 ^ 24 := by
  rw [Ozaki.abs_intCast] at h
  have h24 : (2 : ℚ) ^ (24 : ℤ) = ((2 ^ 24 : ℕ) : ℚ) := by decide
  rw [h24] at h
  have := Rat.natCast_lt_natCast.mp h
  omega

/-- **Exact region.** On an exact configuration, integer operands, an integer `c`, and a term whose
products and `c` have total magnitude below `2^24`: the term evaluates to its exact value. -/
theorem eval_int {P : Model} {b : ℕ} (hE : ExactMultiplier P b) (q : ℕ → P.a.Word × P.b.Word)
    (hq : ∀ i, IntWord P.a (q i).1 ∧ IntWord P.b (q i).2) (c : F32) {zc : ℤ}
    (hc : value32 c = some (zc : ℚ)) :
    ∀ t : MMAlgebra.Term, TermWF P.nfma t →
      MMAlgebra.mag (mcMachine P) q (Rat.abs (zc : ℚ)) 0 t < 2 ^ (24 : ℤ) →
      ∃ (o : F32) (z : ℤ), MMAlgebra.eval (mcMachine P) q c c t = some o ∧
        value32 o = some (z : ℚ) ∧ (z : ℚ) = MMAlgebra.exact (mcMachine P) q (zc : ℚ) 0 t
  | .zero, _, _ => ⟨0, 0, rfl, by decide +kernel, by simp [MMAlgebra.exact]⟩
  | .init, _, _ => ⟨c, zc, rfl, hc, by simp [MMAlgebra.exact]⟩
  | .hole, hwf, _ => absurd hwf (by simp [TermWF])
  | .blk t I, hwf, hm => by
    obtain ⟨hwt, hlen⟩ := hwf
    have hsa := (mcMachine P).slotAbs_nonneg (I.map (Option.map q))
    have hm' : MMAlgebra.mag (mcMachine P) q (Rat.abs (zc : ℚ)) 0 t +
        (mcMachine P).slotAbs (I.map (Option.map q)) < 2 ^ (24 : ℤ) := hm
    have hmt := MMAlgebra.mag_nonneg (mcMachine P) q (Ozaki.abs_nonneg (zc : ℚ)) Rat.le_refl t
    obtain ⟨d, zd, hd, hvd, hzd⟩ := eval_int hE q hq c hc t hwt (by grind)
    have hex := MMAlgebra.abs_exact_le (mcMachine P) q (zc : ℚ) 0 (.blk t I)
    have hext := MMAlgebra.abs_exact_le (mcMachine P) q (zc : ℚ) 0 t
    rw [Ozaki.abs_zero] at hex hext
    have hex' : Rat.abs (MMAlgebra.exact (mcMachine P) q (zc : ℚ) 0 t +
        (mcMachine P).slotVal (I.map (Option.map q))) ≤
        MMAlgebra.mag (mcMachine P) q (Rat.abs (zc : ℚ)) 0 t +
          (mcMachine P).slotAbs (I.map (Option.map q)) := hex
    obtain ⟨o, z, ho, hvo, hz⟩ := block_int hE q hq hvd I hlen
      (by rw [hzd]; grind) (by grind) (by rw [hzd]; grind)
    refine ⟨o, z, ?_, hvo, ?_⟩
    · show (MMAlgebra.eval (mcMachine P) q c c t).bind _ = _
      rw [hd]; exact ho
    · rw [hz, hzd]; rfl
  | .add t u, hwf, hm => by
    obtain ⟨hwt, hwu⟩ := hwf
    have h1 := MMAlgebra.mag_nonneg (mcMachine P) q (Ozaki.abs_nonneg (zc : ℚ)) Rat.le_refl t
    have h2 := MMAlgebra.mag_nonneg (mcMachine P) q (Ozaki.abs_nonneg (zc : ℚ)) Rat.le_refl u
    have hm' : MMAlgebra.mag (mcMachine P) q (Rat.abs (zc : ℚ)) 0 t +
        MMAlgebra.mag (mcMachine P) q (Rat.abs (zc : ℚ)) 0 u < 2 ^ (24 : ℤ) := hm
    obtain ⟨x, zx, hx, hvx, hzx⟩ := eval_int hE q hq c hc t hwt (by grind)
    obtain ⟨y, zy, hy, hvy, hzy⟩ := eval_int hE q hq c hc u hwu (by grind)
    have hex := MMAlgebra.abs_exact_le (mcMachine P) q (zc : ℚ) 0 (.add t u)
    rw [Ozaki.abs_zero] at hex
    have hex' : Rat.abs (MMAlgebra.exact (mcMachine P) q (zc : ℚ) 0 t +
        MMAlgebra.exact (mcMachine P) q (zc : ℚ) 0 u) ≤
        MMAlgebra.mag (mcMachine P) q (Rat.abs (zc : ℚ)) 0 t +
          MMAlgebra.mag (mcMachine P) q (Rat.abs (zc : ℚ)) 0 u := hex
    have hle : (zx + zy).natAbs ≤ 2 ^ 24 :=
      natAbs_le_of_abs_lt (by rw [Rat.intCast_add, hzx, hzy]; grind)
    obtain ⟨w, hw, hvw⟩ := fl32_int false (zx + zy) hle
    refine ⟨w, zx + zy, ?_, hvw, ?_⟩
    · show (MMAlgebra.eval (mcMachine P) q c c t).bind _ = _
      rw [hx]; show (MMAlgebra.eval (mcMachine P) q c c u).bind _ = _
      rw [hy]
      show fl32 false ((value32 x).getD 0 + (value32 y).getD 0) = some w
      rw [hvx, hvy]; simp only [Option.getD_some]; rw [← Rat.intCast_add]; exact hw
    · rw [Rat.intCast_add, hzx, hzy]; rfl

/-- **Every schedule agrees inside the exact region.** Two terms over the same products and `c`,
each with total magnitude below `2^24`, on integer operands of an exact configuration: both
return the same binary32 value. -/
theorem eval_agree {P : Model} {b : ℕ} (hE : ExactMultiplier P b) (q : ℕ → P.a.Word × P.b.Word)
    (hq : ∀ i, IntWord P.a (q i).1 ∧ IntWord P.b (q i).2) (c : F32) {zc : ℤ}
    (hc : value32 c = some (zc : ℚ)) (t₁ t₂ : MMAlgebra.Term)
    (hw₁ : TermWF P.nfma t₁) (hw₂ : TermWF P.nfma t₂)
    (hm₁ : MMAlgebra.mag (mcMachine P) q (Rat.abs (zc : ℚ)) 0 t₁ < 2 ^ (24 : ℤ))
    (hm₂ : MMAlgebra.mag (mcMachine P) q (Rat.abs (zc : ℚ)) 0 t₂ < 2 ^ (24 : ℤ))
    (hex : MMAlgebra.exact (mcMachine P) q (zc : ℚ) 0 t₁ =
      MMAlgebra.exact (mcMachine P) q (zc : ℚ) 0 t₂) :
    ∃ o₁ o₂ : F32, MMAlgebra.eval (mcMachine P) q c c t₁ = some o₁ ∧
      MMAlgebra.eval (mcMachine P) q c c t₂ = some o₂ ∧ value32 o₁ = value32 o₂ := by
  obtain ⟨o₁, z₁, h₁, hv₁, hz₁⟩ := eval_int hE q hq c hc t₁ hw₁ hm₁
  obtain ⟨o₂, z₂, h₂, hv₂, hz₂⟩ := eval_int hE q hq c hc t₂ hw₂ hm₂
  exact ⟨o₁, o₂, h₁, h₂, by rw [hv₁, hv₂, hz₁, hz₂, hex]⟩

/-- CDNA 1, CDNA 2 and CDNA 3 with fp16 operands of at most 11-bit integers are exact configurations,
so `eval_agree` applies to them. -/
theorem cdna_fp16_exactMultiplier (P : Model)
    (hP : P = cdna1F16 ∨ P = cdna2F16 ∨ P = cdna3F16) {b : ℕ} (hb : b ≤ 11) :
    ExactMultiplier P b := by
  rcases hP with rfl | rfl | rfl
  · exact cdna1F16_exactMultiplier hb
  · exact cdna2F16_exactMultiplier hb
  · exact cdna3F16_exactMultiplier hb

end MMAlgebra.MC
