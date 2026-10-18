import MMAlgebraMC.Exact

/-! # A concrete error contract: correctly rounded blocks (SFMA, CDNA 1)

On SFMA and CDNA 1 a block returns the binary32 value nearest to the exact sum of `c` and its
products, so it is within `2^-24 (|c| + Σ|aᵢbᵢ|) + 2^-150` of that sum
(`MatrixCore.correctRounding_apriori`); a binary32 addition is within `2^-24 (|x| + |y|) + 2^-150`.
`crContract` packages both as a `MMAlgebra.Contract`, so `MMAlgebra.eval_error`,
`MMAlgebra.divergence` and `MMAlgebra.divergence_shared` give machine-checked bounds for every
reduction term on these models (`cdna1_divergence`). -/

open MatrixCore Ozaki.MC

namespace MMAlgebra.MC

/-- `Σ |aᵢbᵢ|` of two operand vectors. -/
def absProducts (P : Model) (a : List P.a.Word) (b : List P.b.Word) : ℚ :=
  sumQ (List.zipWith (fun x y => absQ (P.a.wordValue x * P.b.wordValue y)) a b)

theorem mapM_absProducts {P : Model} : ∀ (xa : List P.a.Word) (xb : List P.b.Word)
    (A B : List Unpacked), xa.mapM (fun w => (P.a.read w).toFinite) = some A →
    xb.mapM (fun w => (P.b.read w).toFinite) = some B →
    sumQ ((List.zipWith Unpacked.mul A B).map fun p => absQ p.value) = absProducts P xa xb
  | [], xb, A, B, ha, _ => by
    simp at ha; subst ha; simp [absProducts, sumQ]
  | _ :: _, [], A, B, _, hb => by
    simp at hb; subst hb; cases A <;> simp [absProducts, sumQ]
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
            have ih := mapM_absProducts xs ys us vs hxs hys
            unfold absProducts at ih ⊢
            simp only [List.zipWith_cons_cons, List.map_cons, sumQ, ih, InputFormat.wordValue, hx,
              hy, Option.map_some, Option.getD_some, Unpacked.value_mul]

/-- The block's product magnitudes are the slots' product magnitudes. -/
theorem absProducts_slots {P : Model} {b : ℕ} (hE : ExactMultiplier P b) :
    ∀ ps : List (Option (P.a.Word × P.b.Word)),
      absProducts P ((slotPairs P ps).map Prod.fst) ((slotPairs P ps).map Prod.snd) =
        (mcMachine P).slotAbs ps
  | [] => by simp [absProducts, slotPairs, sumQ, MMAlgebra.Machine.slotAbs]
  | o :: ps => by
    have ih := absProducts_slots hE ps
    rw [(mcMachine P).slotAbs_cons, ← ih]
    simp only [absProducts, slotPairs, List.map_cons, List.zipWith_cons_cons, sumQ, absQ_eq]
    cases o with
    | none =>
      show Rat.abs (P.a.wordValue (0 : P.a.Word) * P.b.wordValue (0 : P.b.Word)) + _ = _
      rw [wordValue_zero hE.encA, wordValue_zero hE.encB]; simp
    | some q => rfl

/-- **Correctly rounded block contract.** On SFMA and CDNA 1, a block whose accumulator has
magnitude at most `A` is within `2^-24 (A + Σ|aᵢbᵢ|) + 2^-150` of the exact sum of its inputs. -/
theorem block_le_cr {P : Model} {b : ℕ} (hE : ExactMultiplier P b)
    (hacc : P.accumulation = .correctRounding) (hov : P.productOverflow = false)
    (hs : P.subnormals = true) (d : F32) (ps : List (Option (P.a.Word × P.b.Word))) (o : F32)
    (A : ℚ) (hA : Rat.abs ((mcMachine P).val d) ≤ A) (h : (mcMachine P).block d ps = some o) :
    Rat.abs ((mcMachine P).val o - ((mcMachine P).val d + (mcMachine P).slotVal ps)) ≤
      2 ^ (-24 : ℤ) * (A + (mcMachine P).slotAbs ps) + 2 ^ (-150 : ℤ) := by
  generalize hx : (⟨(slotPairs P ps).map Prod.fst, (slotPairs P ps).map Prod.snd, d⟩ :
    BlockInput P) = x
  have hblk : (blockBits x).toOption = some o := by rw [← hx]; exact h
  unfold blockBits at hblk
  cases ht : evalBlock x with
  | error e => rw [ht] at hblk; simp [Except.map, Except.toOption] at hblk
  | ok t =>
    rw [ht] at hblk
    simp only [Except.map, Except.toOption, Option.some.injEq] at hblk
    obtain ⟨_, _, hp, _, _⟩ := evalBlock_ok ht
    have e := correctRounding_apriori hacc hov hs ht
    unfold prepare at hp
    cases ha : x.a.mapM (fun w => (P.a.read w).toFinite) with
    | none => simp [ha] at hp
    | some A' =>
      cases hb : x.b.mapM (fun w => (P.b.read w).toFinite) with
      | none => simp [ha, hb] at hp
      | some B' =>
        cases hc : (fp32.decode x.c).toFinite with
        | none => simp [ha, hb, hc] at hp
        | some C =>
          have hp' : t.prepared = ⟨A', B', C⟩ := by
            simp [ha, hb, hc] at hp; first | exact hp.symm | exact hp
          have hexact : t.prepared.exact = (mcMachine P).slotVal ps + (mcMachine P).val d := by
            rw [hp', Prepared.exact_eq]
            simp only
            rw [mapM_products x.a x.b A' B' ha hb, ← hx, exactProducts_slots hE]
            congr 1
            show C.value = (value32 d).getD 0
            rw [← hx] at hc; unfold value32; rw [hc]; rfl
          have habs : t.prepared.absSum = (mcMachine P).slotAbs ps + Rat.abs ((mcMachine P).val d) := by
            rw [hp']
            show sumQ ((List.zipWith Unpacked.mul A' B').map fun p => absQ p.value) + absQ C.value = _
            rw [mapM_absProducts x.a x.b A' B' ha hb, ← hx, absProducts_slots hE, absQ_eq]
            congr 2
            show C.value = (value32 d).getD 0
            rw [← hx] at hc; unfold value32; rw [hc]; rfl
          have hwo : MatrixCore.wordValue t.d = (mcMachine P).val o := by rw [hblk]; rfl
          rw [hexact, habs, hwo, absQ_eq, pow2_eq, pow2_eq] at e
          rw [Ozaki.abs_sub_comm]
          have hmono : (2 : ℚ) ^ (-24 : ℤ) * ((mcMachine P).slotAbs ps + Rat.abs ((mcMachine P).val d)) ≤
              2 ^ (-24 : ℤ) * (A + (mcMachine P).slotAbs ps) :=
            Rat.mul_le_mul_of_nonneg_left (by grind) (Rat.le_of_lt (Ozaki.two_pow_pos _))
          have e2 : (mcMachine P).slotVal ps + (mcMachine P).val d - (mcMachine P).val o =
              (mcMachine P).val d + (mcMachine P).slotVal ps - (mcMachine P).val o := by grind
          rw [e2] at e; grind

/-- **Binary32 addition contract.** Round to nearest even is within `2^-24 (|x| + |y|) + 2^-150`
of the exact sum. -/
theorem add_le (P : Model) (x y o : F32) (h : (mcMachine P).add x y = some o) :
    Rat.abs ((mcMachine P).val o - ((mcMachine P).val x + (mcMachine P).val y)) ≤
      2 ^ (-24 : ℤ) * (Rat.abs ((mcMachine P).val x) + Rat.abs ((mcMachine P).val y)) +
        2 ^ (-150 : ℤ) := by
  have e := fl32_error (ftz := false) h
  have eb := flBound_le false ((value32 x).getD 0 + (value32 y).getD 0)
  simp only [Bool.false_eq_true, ↓reduceIte, Rat.add_zero] at eb
  rw [absQ_eq, pow2_eq, pow2_eq] at eb
  rw [absQ_eq] at e
  have tri := Ozaki.abs_add_le ((value32 x).getD 0) ((value32 y).getD 0)
  have hmono : (2 : ℚ) ^ (-24 : ℤ) * Rat.abs ((value32 x).getD 0 + (value32 y).getD 0) ≤
      2 ^ (-24 : ℤ) * (Rat.abs ((value32 x).getD 0) + Rat.abs ((value32 y).getD 0)) :=
    Rat.mul_le_mul_of_nonneg_left tri (Rat.le_of_lt (Ozaki.two_pow_pos _))
  show Rat.abs (MatrixCore.wordValue o - ((value32 x).getD 0 + (value32 y).getD 0)) ≤
    2 ^ (-24 : ℤ) * (Rat.abs ((value32 x).getD 0) + Rat.abs ((value32 y).getD 0)) + 2 ^ (-150 : ℤ)
  rw [Ozaki.abs_sub_comm]
  grind

/-- The contract of a correctly rounded model (SFMA, CDNA 1). -/
def crContract {P : Model} {b : ℕ} (hE : ExactMultiplier P b)
    (hacc : P.accumulation = .correctRounding) (hov : P.productOverflow = false)
    (hs : P.subnormals = true) : MMAlgebra.Contract (mcMachine P) where
  blockErr A ps := 2 ^ (-24 : ℤ) * (A + (mcMachine P).slotAbs ps) + 2 ^ (-150 : ℤ)
  block_le d ps o A hA h := block_le_cr hE hacc hov hs d ps o A hA h
  addRel := 2 ^ (-24 : ℤ)
  addRel_nonneg := Rat.le_of_lt (Ozaki.two_pow_pos _)
  addAbs := 2 ^ (-150 : ℤ)
  add_le x y o h := add_le P x y o h

/-- **Divergence on CDNA 1.** Any two reduction terms over the same products and `c` on the
CDNA 1 fp16 model differ by at most the sum of their structural bounds. -/
theorem cdna1_divergence (q : ℕ → cdna1F16.a.Word × cdna1F16.b.Word) (c : F32)
    (t₁ t₂ : MMAlgebra.Term) {o₁ o₂ : F32}
    (he₁ : MMAlgebra.eval (mcMachine cdna1F16) q c c t₁ = some o₁)
    (he₂ : MMAlgebra.eval (mcMachine cdna1F16) q c c t₂ = some o₂)
    (hex : MMAlgebra.exact (mcMachine cdna1F16) q ((mcMachine cdna1F16).val c) ((mcMachine cdna1F16).val c) t₁ =
      MMAlgebra.exact (mcMachine cdna1F16) q ((mcMachine cdna1F16).val c) ((mcMachine cdna1F16).val c) t₂) :
    Rat.abs ((mcMachine cdna1F16).val o₁ - (mcMachine cdna1F16).val o₂) ≤
      MMAlgebra.err (crContract (cdna1F16_exactMultiplier (b := 11) (by decide)) rfl rfl rfl) q
          (Rat.abs ((mcMachine cdna1F16).val c)) (Rat.abs ((mcMachine cdna1F16).val c)) t₁ +
        MMAlgebra.err (crContract (cdna1F16_exactMultiplier (b := 11) (by decide)) rfl rfl rfl) q
          (Rat.abs ((mcMachine cdna1F16).val c)) (Rat.abs ((mcMachine cdna1F16).val c)) t₂ :=
  MMAlgebra.divergence _ _ q q c c c c t₁ t₂ he₁ he₂ hex

end MMAlgebra.MC
