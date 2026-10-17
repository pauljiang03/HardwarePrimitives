import MMAlgebraMC.ParityLaw
import MMAlgebraMC.RigidMC
import MMAlgebra.ParityChain

/-! # CDNA 3 binary8: completeness for chains

CDNA 3 binary8 blocks (`N_FMA = 16`, odd/even grouping) satisfy the laws of a parity-pair
multiplier (`MMAlgebra.Parity.ParityLaws`): an empty slot is the zero pair, a block depends on its
slots only through {odd multiset, even multiset} (the parity law `cdna3FP8_parityEquiv`), and
an empty block passes a finite accumulator other than `−0` through (`e44_pass` …: with no nonzero
product, `c` is added to an exact zero sum and returned). With kernel-checked base witnesses, two
chains over the same products that differ in the parity pattern of some pair, in particular two
chains with different ordered partitions, or the same ordered partition but a different split of
a block into its parity groups, differ on an input supported on that pair
(`e44_chain_complete`, `e55_chain_complete`, `e45_chain_complete`, `e54_chain_complete` for
E4M3 × E4M3, E5M2 × E5M2 and the two mixed pairs). -/

open MatrixCore Ozaki.MC

namespace MMAlgebra.MC.FP8

/-- The CDNA 3 binary8 models for the four operand-format pairs (FNUZ formats). -/
abbrev E44 := cdna3FP8 e4m3fnuz e4m3fnuz
abbrev E55 := cdna3FP8 e5m2fnuz e5m2fnuz
abbrev E45 := cdna3FP8 e4m3fnuz e5m2fnuz
abbrev E54 := cdna3FP8 e5m2fnuz e4m3fnuz

/-- The odd and even slots of `MMAlgebra.Parity` are `MatrixCore`'s odd- and even-indexed
elements. -/
theorem oddSlots_eq {γ : Type} : ∀ l : List γ, MMAlgebra.Parity.oddSlots l = MatrixCore.oddIndexed l
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: l => by simp only [MMAlgebra.Parity.oddSlots, MatrixCore.oddIndexed, oddSlots_eq l]

theorem evenSlots_eq {γ : Type} : ∀ l : List γ, MMAlgebra.Parity.evenSlots l = MatrixCore.evenIndexed l
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: l => by simp only [MMAlgebra.Parity.evenSlots, MatrixCore.evenIndexed, evenSlots_eq l]

theorem parityEquiv_of_slots {γ : Type} {l m : List γ} (h : MMAlgebra.Parity.ParityEquiv l m) :
    MMAlgebra.MC.ParityEquiv l m := by
  unfold MMAlgebra.Parity.ParityEquiv at h
  unfold MMAlgebra.MC.ParityEquiv
  simp only [oddSlots_eq, evenSlots_eq] at h
  exact h

/-- **The parity law on the machine**: a CDNA 3 FP8 block depends on its slots only through the
unordered pair {odd multiset, even multiset}. -/
theorem cdna3FP8_machine_parity (fa fb : Format) (d : F32)
    {ps qs : List (Option ((cdna3FP8 fa fb).a.Word × (cdna3FP8 fa fb).b.Word))}
    (h : MMAlgebra.Parity.ParityEquiv ps qs) :
    (mcMachine (cdna3FP8 fa fb)).block d ps = (mcMachine (cdna3FP8 fa fb)).block d qs := by
  show (blockBits (P := cdna3FP8 fa fb) ⟨(slotPairs _ ps).map Prod.fst, (slotPairs _ ps).map Prod.snd, d⟩).toOption =
    (blockBits (P := cdna3FP8 fa fb) ⟨(slotPairs _ qs).map Prod.fst, (slotPairs _ qs).map Prod.snd, d⟩).toOption
  have hg : MMAlgebra.Parity.ParityEquiv (slotPairs (cdna3FP8 fa fb) ps) (slotPairs (cdna3FP8 fa fb) qs) := by
    unfold slotPairs; exact h.map _
  exact congrArg Except.toOption (cdna3FP8_parityEquiv fa fb d (parityEquiv_of_slots hg))

/-- An empty slot of a CDNA 3 FP8 block is the zero pair. -/
theorem cdna3FP8_slotZero (fa fb : Format) :
    MMAlgebra.SlotZero (mcMachine (cdna3FP8 fa fb)) (0, 0) := fun d ps qs h => by
  show (blockBits (P := cdna3FP8 fa fb) ⟨(slotPairs _ ps).map Prod.fst,
    (slotPairs _ ps).map Prod.snd, d⟩).toOption =
    (blockBits (P := cdna3FP8 fa fb) ⟨(slotPairs _ qs).map Prod.fst,
    (slotPairs _ qs).map Prod.snd, d⟩).toOption
  unfold slotPairs; rw [h]

/-- **An empty CDNA 3 FP8 block (e44) passes a good accumulator through.** -/
theorem e44_pass (d : F32) (hd : GoodW d) :
    (mcMachine E44).block d (List.replicate 16 none) = some d := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hd.1
  obtain ⟨C, hC, rfl⟩ : ∃ C, (binary32.decode d).toFinite = some C ∧ C.value = v := by
    unfold value32 at hv
    cases hc : (binary32.decode d).toFinite with
    | none => rw [hc] at hv; cases hv
    | some C => rw [hc] at hv; exact ⟨C, rfl, Option.some.inj hv⟩
  show (blockBits (P := E44) ⟨(slotPairs E44 (List.replicate 16 none)).map Prod.fst,
    (slotPairs E44 (List.replicate 16 none)).map Prod.snd, d⟩).toOption = some d
  have hz : decPair E44 (0, 0) = some (⟨false, 0, -7, 3⟩, ⟨false, 0, -7, 3⟩) := by
    decide +kernel
  have hslot : slotPairs E44 (List.replicate 16 none) = List.replicate 16 (0, 0) := by
    simp [slotPairs]
  have hL : (List.replicate 16 ((0, 0) : E44.a.Word × E44.b.Word)).mapM (decPair E44) =
      some (List.replicate 16 (⟨false, 0, -7, 3⟩, ⟨false, 0, -7, 3⟩)) := by
    simp only [List.replicate, List.mapM_cons, List.mapM_nil, hz]; rfl
  have hprep : prepare (P := E44) ⟨(slotPairs E44 (List.replicate 16 none)).map Prod.fst,
      (slotPairs E44 (List.replicate 16 none)).map Prod.snd, d⟩ =
      some ⟨List.replicate 16 ⟨false, 0, -7, 3⟩, List.replicate 16 ⟨false, 0, -7, 3⟩, C⟩ := by
    rw [hslot, prepare_pairs, hL, Option.bind_some, hC]; rfl
  have hacc : accumulate E44
      ⟨List.replicate 16 ⟨false, 0, -7, 3⟩, List.replicate 16 ⟨false, 0, -7, 3⟩, C⟩ =
      .ok (lateSum E44 none 0 C) := by
    have hov : Prepared.productOverflows
        ⟨List.replicate 16 ⟨false, 0, -7, 3⟩, List.replicate 16 ⟨false, 0, -7, 3⟩, C⟩ = false := by
      show (List.zipWith Unpacked.mul (List.replicate 16 ⟨false, 0, -7, 3⟩)
        (List.replicate 16 ⟨false, 0, -7, 3⟩)).any (fun p => decide (pow2 128 ≤ absQ p.value)) = false
      decide +kernel
    unfold accumulate
    rw [hov]
    rfl
  have hsum : lateSum E44 none 0 C = C.value := by
    have hl : ∀ eC, cExp E44 C = some eC →
        lateSum E44 none 0 C = normalizeRD 31 (rdMantissa 0 eC 32 + C.value) := by
      intro eC he; unfold lateSum; rw [he]; rfl
    obtain ⟨eC, he⟩ : ∃ eC, cExp E44 C = some eC := by
      unfold cExp; split
      · exact ⟨-126, rfl⟩
      · exact ⟨_, rfl⟩
    rw [hl eC he, show rdMantissa (0 : ℚ) eC 32 = 0 from rdGrid_zero _, Rat.zero_add]
    unfold normalizeRD
    split
    · rename_i h; rw [h]
    · rename_i hne
      show rdGrid C.value (normExp (absQ C.value) - ((31 : ℕ) : ℤ)) = C.value
      apply rdGrid_of_onGrid
      have hval : value32 d = some C.value := by unfold value32; rw [hC]; rfl
      obtain ⟨k, e, h1, h2, h3, he⟩ := value32_finiteValue hval
      have hpos := absQ_pos hne
      obtain ⟨hb1, hb2, hb3⟩ := normExp_bounds hpos
      have hle : normExp (absQ C.value) ≤ e := by
        apply Classical.byContradiction; intro hlt
        have hne' : normExp (absQ C.value) ≠ -126 := by omega
        have hlo := hb2 hne'
        have hk : absQ (k : ℚ) < 16777216 := by
          rw [absQ_intCast]; exact_mod_cast (show k.natAbs < 16777216 from h3)
        have hp := pow2_pos (e - 23)
        have hup : absQ C.value < 16777216 * pow2 (e - 23) := by
          rw [he, absQ_mul_pos _ _ hp]
          exact Rat.mul_lt_mul_of_pos_right hk hp
        have e24 : (16777216 : ℚ) * pow2 (e - 23) = pow2 (e + 1) := by
          rw [show e + 1 = 24 + (e - 23) by omega, pow2_add]; rfl
        have hmono : pow2 (e + 1) ≤ pow2 (normExp (absQ C.value)) := pow2_le_of_le (by omega)
        grind
      rw [he] at hle ⊢
      exact onGrid_intCast_mul k (e - 23) _ (by omega)
  unfold blockBits evalBlock
  simp only [List.length_map, List.length_replicate, hslot]
  rw [if_neg (by decide)]
  rw [hslot] at hprep
  rw [hprep]
  simp only
  rw [hacc, hsum]
  simp only
  have hval : value32 d = some C.value := by unfold value32; rw [hC]; rfl
  rw [show (!E44.subnormals) = false from rfl, fl32_value_self hval hd.2]
  rfl

/-- **An empty CDNA 3 FP8 block (e55) passes a good accumulator through.** -/
theorem e55_pass (d : F32) (hd : GoodW d) :
    (mcMachine E55).block d (List.replicate 16 none) = some d := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hd.1
  obtain ⟨C, hC, rfl⟩ : ∃ C, (binary32.decode d).toFinite = some C ∧ C.value = v := by
    unfold value32 at hv
    cases hc : (binary32.decode d).toFinite with
    | none => rw [hc] at hv; cases hv
    | some C => rw [hc] at hv; exact ⟨C, rfl, Option.some.inj hv⟩
  show (blockBits (P := E55) ⟨(slotPairs E55 (List.replicate 16 none)).map Prod.fst,
    (slotPairs E55 (List.replicate 16 none)).map Prod.snd, d⟩).toOption = some d
  have hz : decPair E55 (0, 0) = some (⟨false, 0, -15, 2⟩, ⟨false, 0, -15, 2⟩) := by
    decide +kernel
  have hslot : slotPairs E55 (List.replicate 16 none) = List.replicate 16 (0, 0) := by
    simp [slotPairs]
  have hL : (List.replicate 16 ((0, 0) : E55.a.Word × E55.b.Word)).mapM (decPair E55) =
      some (List.replicate 16 (⟨false, 0, -15, 2⟩, ⟨false, 0, -15, 2⟩)) := by
    simp only [List.replicate, List.mapM_cons, List.mapM_nil, hz]; rfl
  have hprep : prepare (P := E55) ⟨(slotPairs E55 (List.replicate 16 none)).map Prod.fst,
      (slotPairs E55 (List.replicate 16 none)).map Prod.snd, d⟩ =
      some ⟨List.replicate 16 ⟨false, 0, -15, 2⟩, List.replicate 16 ⟨false, 0, -15, 2⟩, C⟩ := by
    rw [hslot, prepare_pairs, hL, Option.bind_some, hC]; rfl
  have hacc : accumulate E55
      ⟨List.replicate 16 ⟨false, 0, -15, 2⟩, List.replicate 16 ⟨false, 0, -15, 2⟩, C⟩ =
      .ok (lateSum E55 none 0 C) := by
    have hov : Prepared.productOverflows
        ⟨List.replicate 16 ⟨false, 0, -15, 2⟩, List.replicate 16 ⟨false, 0, -15, 2⟩, C⟩ = false := by
      show (List.zipWith Unpacked.mul (List.replicate 16 ⟨false, 0, -15, 2⟩)
        (List.replicate 16 ⟨false, 0, -15, 2⟩)).any (fun p => decide (pow2 128 ≤ absQ p.value)) = false
      decide +kernel
    unfold accumulate
    rw [hov]
    rfl
  have hsum : lateSum E55 none 0 C = C.value := by
    have hl : ∀ eC, cExp E55 C = some eC →
        lateSum E55 none 0 C = normalizeRD 31 (rdMantissa 0 eC 32 + C.value) := by
      intro eC he; unfold lateSum; rw [he]; rfl
    obtain ⟨eC, he⟩ : ∃ eC, cExp E55 C = some eC := by
      unfold cExp; split
      · exact ⟨-126, rfl⟩
      · exact ⟨_, rfl⟩
    rw [hl eC he, show rdMantissa (0 : ℚ) eC 32 = 0 from rdGrid_zero _, Rat.zero_add]
    unfold normalizeRD
    split
    · rename_i h; rw [h]
    · rename_i hne
      show rdGrid C.value (normExp (absQ C.value) - ((31 : ℕ) : ℤ)) = C.value
      apply rdGrid_of_onGrid
      have hval : value32 d = some C.value := by unfold value32; rw [hC]; rfl
      obtain ⟨k, e, h1, h2, h3, he⟩ := value32_finiteValue hval
      have hpos := absQ_pos hne
      obtain ⟨hb1, hb2, hb3⟩ := normExp_bounds hpos
      have hle : normExp (absQ C.value) ≤ e := by
        apply Classical.byContradiction; intro hlt
        have hne' : normExp (absQ C.value) ≠ -126 := by omega
        have hlo := hb2 hne'
        have hk : absQ (k : ℚ) < 16777216 := by
          rw [absQ_intCast]; exact_mod_cast (show k.natAbs < 16777216 from h3)
        have hp := pow2_pos (e - 23)
        have hup : absQ C.value < 16777216 * pow2 (e - 23) := by
          rw [he, absQ_mul_pos _ _ hp]
          exact Rat.mul_lt_mul_of_pos_right hk hp
        have e24 : (16777216 : ℚ) * pow2 (e - 23) = pow2 (e + 1) := by
          rw [show e + 1 = 24 + (e - 23) by omega, pow2_add]; rfl
        have hmono : pow2 (e + 1) ≤ pow2 (normExp (absQ C.value)) := pow2_le_of_le (by omega)
        grind
      rw [he] at hle ⊢
      exact onGrid_intCast_mul k (e - 23) _ (by omega)
  unfold blockBits evalBlock
  simp only [List.length_map, List.length_replicate, hslot]
  rw [if_neg (by decide)]
  rw [hslot] at hprep
  rw [hprep]
  simp only
  rw [hacc, hsum]
  simp only
  have hval : value32 d = some C.value := by unfold value32; rw [hC]; rfl
  rw [show (!E55.subnormals) = false from rfl, fl32_value_self hval hd.2]
  rfl

/-- **An empty CDNA 3 FP8 block (e45) passes a good accumulator through.** -/
theorem e45_pass (d : F32) (hd : GoodW d) :
    (mcMachine E45).block d (List.replicate 16 none) = some d := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hd.1
  obtain ⟨C, hC, rfl⟩ : ∃ C, (binary32.decode d).toFinite = some C ∧ C.value = v := by
    unfold value32 at hv
    cases hc : (binary32.decode d).toFinite with
    | none => rw [hc] at hv; cases hv
    | some C => rw [hc] at hv; exact ⟨C, rfl, Option.some.inj hv⟩
  show (blockBits (P := E45) ⟨(slotPairs E45 (List.replicate 16 none)).map Prod.fst,
    (slotPairs E45 (List.replicate 16 none)).map Prod.snd, d⟩).toOption = some d
  have hz : decPair E45 (0, 0) = some (⟨false, 0, -7, 3⟩, ⟨false, 0, -15, 2⟩) := by
    decide +kernel
  have hslot : slotPairs E45 (List.replicate 16 none) = List.replicate 16 (0, 0) := by
    simp [slotPairs]
  have hL : (List.replicate 16 ((0, 0) : E45.a.Word × E45.b.Word)).mapM (decPair E45) =
      some (List.replicate 16 (⟨false, 0, -7, 3⟩, ⟨false, 0, -15, 2⟩)) := by
    simp only [List.replicate, List.mapM_cons, List.mapM_nil, hz]; rfl
  have hprep : prepare (P := E45) ⟨(slotPairs E45 (List.replicate 16 none)).map Prod.fst,
      (slotPairs E45 (List.replicate 16 none)).map Prod.snd, d⟩ =
      some ⟨List.replicate 16 ⟨false, 0, -7, 3⟩, List.replicate 16 ⟨false, 0, -15, 2⟩, C⟩ := by
    rw [hslot, prepare_pairs, hL, Option.bind_some, hC]; rfl
  have hacc : accumulate E45
      ⟨List.replicate 16 ⟨false, 0, -7, 3⟩, List.replicate 16 ⟨false, 0, -15, 2⟩, C⟩ =
      .ok (lateSum E45 none 0 C) := by
    have hov : Prepared.productOverflows
        ⟨List.replicate 16 ⟨false, 0, -7, 3⟩, List.replicate 16 ⟨false, 0, -15, 2⟩, C⟩ = false := by
      show (List.zipWith Unpacked.mul (List.replicate 16 ⟨false, 0, -7, 3⟩)
        (List.replicate 16 ⟨false, 0, -15, 2⟩)).any (fun p => decide (pow2 128 ≤ absQ p.value)) = false
      decide +kernel
    unfold accumulate
    rw [hov]
    rfl
  have hsum : lateSum E45 none 0 C = C.value := by
    have hl : ∀ eC, cExp E45 C = some eC →
        lateSum E45 none 0 C = normalizeRD 31 (rdMantissa 0 eC 32 + C.value) := by
      intro eC he; unfold lateSum; rw [he]; rfl
    obtain ⟨eC, he⟩ : ∃ eC, cExp E45 C = some eC := by
      unfold cExp; split
      · exact ⟨-126, rfl⟩
      · exact ⟨_, rfl⟩
    rw [hl eC he, show rdMantissa (0 : ℚ) eC 32 = 0 from rdGrid_zero _, Rat.zero_add]
    unfold normalizeRD
    split
    · rename_i h; rw [h]
    · rename_i hne
      show rdGrid C.value (normExp (absQ C.value) - ((31 : ℕ) : ℤ)) = C.value
      apply rdGrid_of_onGrid
      have hval : value32 d = some C.value := by unfold value32; rw [hC]; rfl
      obtain ⟨k, e, h1, h2, h3, he⟩ := value32_finiteValue hval
      have hpos := absQ_pos hne
      obtain ⟨hb1, hb2, hb3⟩ := normExp_bounds hpos
      have hle : normExp (absQ C.value) ≤ e := by
        apply Classical.byContradiction; intro hlt
        have hne' : normExp (absQ C.value) ≠ -126 := by omega
        have hlo := hb2 hne'
        have hk : absQ (k : ℚ) < 16777216 := by
          rw [absQ_intCast]; exact_mod_cast (show k.natAbs < 16777216 from h3)
        have hp := pow2_pos (e - 23)
        have hup : absQ C.value < 16777216 * pow2 (e - 23) := by
          rw [he, absQ_mul_pos _ _ hp]
          exact Rat.mul_lt_mul_of_pos_right hk hp
        have e24 : (16777216 : ℚ) * pow2 (e - 23) = pow2 (e + 1) := by
          rw [show e + 1 = 24 + (e - 23) by omega, pow2_add]; rfl
        have hmono : pow2 (e + 1) ≤ pow2 (normExp (absQ C.value)) := pow2_le_of_le (by omega)
        grind
      rw [he] at hle ⊢
      exact onGrid_intCast_mul k (e - 23) _ (by omega)
  unfold blockBits evalBlock
  simp only [List.length_map, List.length_replicate, hslot]
  rw [if_neg (by decide)]
  rw [hslot] at hprep
  rw [hprep]
  simp only
  rw [hacc, hsum]
  simp only
  have hval : value32 d = some C.value := by unfold value32; rw [hC]; rfl
  rw [show (!E45.subnormals) = false from rfl, fl32_value_self hval hd.2]
  rfl

/-- **An empty CDNA 3 FP8 block (e54) passes a good accumulator through.** -/
theorem e54_pass (d : F32) (hd : GoodW d) :
    (mcMachine E54).block d (List.replicate 16 none) = some d := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hd.1
  obtain ⟨C, hC, rfl⟩ : ∃ C, (binary32.decode d).toFinite = some C ∧ C.value = v := by
    unfold value32 at hv
    cases hc : (binary32.decode d).toFinite with
    | none => rw [hc] at hv; cases hv
    | some C => rw [hc] at hv; exact ⟨C, rfl, Option.some.inj hv⟩
  show (blockBits (P := E54) ⟨(slotPairs E54 (List.replicate 16 none)).map Prod.fst,
    (slotPairs E54 (List.replicate 16 none)).map Prod.snd, d⟩).toOption = some d
  have hz : decPair E54 (0, 0) = some (⟨false, 0, -15, 2⟩, ⟨false, 0, -7, 3⟩) := by
    decide +kernel
  have hslot : slotPairs E54 (List.replicate 16 none) = List.replicate 16 (0, 0) := by
    simp [slotPairs]
  have hL : (List.replicate 16 ((0, 0) : E54.a.Word × E54.b.Word)).mapM (decPair E54) =
      some (List.replicate 16 (⟨false, 0, -15, 2⟩, ⟨false, 0, -7, 3⟩)) := by
    simp only [List.replicate, List.mapM_cons, List.mapM_nil, hz]; rfl
  have hprep : prepare (P := E54) ⟨(slotPairs E54 (List.replicate 16 none)).map Prod.fst,
      (slotPairs E54 (List.replicate 16 none)).map Prod.snd, d⟩ =
      some ⟨List.replicate 16 ⟨false, 0, -15, 2⟩, List.replicate 16 ⟨false, 0, -7, 3⟩, C⟩ := by
    rw [hslot, prepare_pairs, hL, Option.bind_some, hC]; rfl
  have hacc : accumulate E54
      ⟨List.replicate 16 ⟨false, 0, -15, 2⟩, List.replicate 16 ⟨false, 0, -7, 3⟩, C⟩ =
      .ok (lateSum E54 none 0 C) := by
    have hov : Prepared.productOverflows
        ⟨List.replicate 16 ⟨false, 0, -15, 2⟩, List.replicate 16 ⟨false, 0, -7, 3⟩, C⟩ = false := by
      show (List.zipWith Unpacked.mul (List.replicate 16 ⟨false, 0, -15, 2⟩)
        (List.replicate 16 ⟨false, 0, -7, 3⟩)).any (fun p => decide (pow2 128 ≤ absQ p.value)) = false
      decide +kernel
    unfold accumulate
    rw [hov]
    rfl
  have hsum : lateSum E54 none 0 C = C.value := by
    have hl : ∀ eC, cExp E54 C = some eC →
        lateSum E54 none 0 C = normalizeRD 31 (rdMantissa 0 eC 32 + C.value) := by
      intro eC he; unfold lateSum; rw [he]; rfl
    obtain ⟨eC, he⟩ : ∃ eC, cExp E54 C = some eC := by
      unfold cExp; split
      · exact ⟨-126, rfl⟩
      · exact ⟨_, rfl⟩
    rw [hl eC he, show rdMantissa (0 : ℚ) eC 32 = 0 from rdGrid_zero _, Rat.zero_add]
    unfold normalizeRD
    split
    · rename_i h; rw [h]
    · rename_i hne
      show rdGrid C.value (normExp (absQ C.value) - ((31 : ℕ) : ℤ)) = C.value
      apply rdGrid_of_onGrid
      have hval : value32 d = some C.value := by unfold value32; rw [hC]; rfl
      obtain ⟨k, e, h1, h2, h3, he⟩ := value32_finiteValue hval
      have hpos := absQ_pos hne
      obtain ⟨hb1, hb2, hb3⟩ := normExp_bounds hpos
      have hle : normExp (absQ C.value) ≤ e := by
        apply Classical.byContradiction; intro hlt
        have hne' : normExp (absQ C.value) ≠ -126 := by omega
        have hlo := hb2 hne'
        have hk : absQ (k : ℚ) < 16777216 := by
          rw [absQ_intCast]; exact_mod_cast (show k.natAbs < 16777216 from h3)
        have hp := pow2_pos (e - 23)
        have hup : absQ C.value < 16777216 * pow2 (e - 23) := by
          rw [he, absQ_mul_pos _ _ hp]
          exact Rat.mul_lt_mul_of_pos_right hk hp
        have e24 : (16777216 : ℚ) * pow2 (e - 23) = pow2 (e + 1) := by
          rw [show e + 1 = 24 + (e - 23) by omega, pow2_add]; rfl
        have hmono : pow2 (e + 1) ≤ pow2 (normExp (absQ C.value)) := pow2_le_of_le (by omega)
        grind
      rw [he] at hle ⊢
      exact onGrid_intCast_mul k (e - 23) _ (by omega)
  unfold blockBits evalBlock
  simp only [List.length_map, List.length_replicate, hslot]
  rw [if_neg (by decide)]
  rw [hslot] at hprep
  rw [hprep]
  simp only
  rw [hacc, hsum]
  simp only
  have hval : value32 d = some C.value := by unfold value32; rw [hC]; rfl
  rw [show (!E54.subnormals) = false from rfl, fl32_value_self hval hd.2]
  rfl


/-- The laws of a parity-pair multiplier, for CDNA 3 FP8 (E4M3 × E4M3). -/
def e44Laws : MMAlgebra.Parity.ParityLaws (mcMachine E44) 16 where
  z := (0, 0)
  good := GoodW
  slot := cdna3FP8_slotZero e4m3fnuz e4m3fnuz
  grp := fun d _ _ h => cdna3FP8_machine_parity e4m3fnuz e4m3fnuz d h
  zero_good := mc_zero_good
  pass := e44_pass

def e44Witness : MMAlgebra.Parity.ParityWitness e44Laws where
  a := (0x91, 0x5)
  b := (0xc8, 0xf0)
  vx := 0xb8b40000
  vy := 0x43000000
  vs := 0x42fffff5
  vd := 0x42fffff4
  vlt := 0x42fffff4
  vgt := 0x42fffff5
  e₁ := by decide +kernel
  e₂ := by decide +kernel
  e₃ := by decide +kernel
  e₄ := by decide +kernel
  e₅ := by decide +kernel
  e₆ := by decide +kernel
  g₁ := by show GoodW _; decide +kernel
  g₂ := by show GoodW _; decide +kernel
  g₃ := by show GoodW _; decide +kernel
  g₄ := by show GoodW _; decide +kernel
  g₅ := by show GoodW _; decide +kernel
  g₆ := by show GoodW _; decide +kernel
  sep := by decide

/-- **CDNA 3 FP8 (E4M3 × E4M3), completeness for chains.** Two chains over the same products, each
once, that differ in the parity pattern of some pair of products differ on an input supported on
that pair. -/
theorem e44_chain_complete (σ τ : MMAlgebra.Chain) (hσ : ∀ B ∈ σ, B.length = 16)
    (hτ : ∀ B ∈ τ, B.length = 16) (nσ : σ.leaves.Nodup) (nτ : τ.leaves.Nodup)
    (hl : ∀ i, i ∈ σ.leaves ↔ i ∈ τ.leaves)
    (hne : ∃ x y, x ∈ σ.leaves ∧ y ∈ σ.leaves ∧ x ≠ y ∧
      MMAlgebra.Parity.ppattern x y σ ≠ MMAlgebra.Parity.ppattern x y τ) :
    ∃ (x y : ℕ) (q : ℕ → E44.a.Word × E44.b.Word), x ≠ y ∧ (∀ i, i ≠ x → i ≠ y → q i = (0, 0)) ∧
      MMAlgebra.runChain (mcMachine E44) q 0 σ ≠ MMAlgebra.runChain (mcMachine E44) q 0 τ :=
  MMAlgebra.Parity.chain_complete_parity e44Laws (by decide) (by decide) e44Witness σ τ hσ hτ nσ nτ hl hne

/-- The laws of a parity-pair multiplier, for CDNA 3 FP8 (E5M2 × E5M2). -/
def e55Laws : MMAlgebra.Parity.ParityLaws (mcMachine E55) 16 where
  z := (0, 0)
  good := GoodW
  slot := cdna3FP8_slotZero e5m2fnuz e5m2fnuz
  grp := fun d _ _ h => cdna3FP8_machine_parity e5m2fnuz e5m2fnuz d h
  zero_good := mc_zero_good
  pass := e55_pass

def e55Witness : MMAlgebra.Parity.ParityWitness e55Laws where
  a := (0x34, 0x51)
  b := (0x8d, 0x21)
  vx := 0x40200000
  vy := 0xb5480000
  vs := 0x401ffffd
  vd := 0x401ffffc
  vlt := 0x401ffffd
  vgt := 0x401ffffc
  e₁ := by decide +kernel
  e₂ := by decide +kernel
  e₃ := by decide +kernel
  e₄ := by decide +kernel
  e₅ := by decide +kernel
  e₆ := by decide +kernel
  g₁ := by show GoodW _; decide +kernel
  g₂ := by show GoodW _; decide +kernel
  g₃ := by show GoodW _; decide +kernel
  g₄ := by show GoodW _; decide +kernel
  g₅ := by show GoodW _; decide +kernel
  g₆ := by show GoodW _; decide +kernel
  sep := by decide

/-- **CDNA 3 FP8 (E5M2 × E5M2), completeness for chains.** Two chains over the same products, each
once, that differ in the parity pattern of some pair of products differ on an input supported on
that pair. -/
theorem e55_chain_complete (σ τ : MMAlgebra.Chain) (hσ : ∀ B ∈ σ, B.length = 16)
    (hτ : ∀ B ∈ τ, B.length = 16) (nσ : σ.leaves.Nodup) (nτ : τ.leaves.Nodup)
    (hl : ∀ i, i ∈ σ.leaves ↔ i ∈ τ.leaves)
    (hne : ∃ x y, x ∈ σ.leaves ∧ y ∈ σ.leaves ∧ x ≠ y ∧
      MMAlgebra.Parity.ppattern x y σ ≠ MMAlgebra.Parity.ppattern x y τ) :
    ∃ (x y : ℕ) (q : ℕ → E55.a.Word × E55.b.Word), x ≠ y ∧ (∀ i, i ≠ x → i ≠ y → q i = (0, 0)) ∧
      MMAlgebra.runChain (mcMachine E55) q 0 σ ≠ MMAlgebra.runChain (mcMachine E55) q 0 τ :=
  MMAlgebra.Parity.chain_complete_parity e55Laws (by decide) (by decide) e55Witness σ τ hσ hτ nσ nτ hl hne

/-- The laws of a parity-pair multiplier, for CDNA 3 FP8 (E4M3 × E5M2). -/
def e45Laws : MMAlgebra.Parity.ParityLaws (mcMachine E45) 16 where
  z := (0, 0)
  good := GoodW
  slot := cdna3FP8_slotZero e4m3fnuz e5m2fnuz
  grp := fun d _ _ h => cdna3FP8_machine_parity e4m3fnuz e5m2fnuz d h
  zero_good := mc_zero_good
  pass := e45_pass

def e45Witness : MMAlgebra.Parity.ParityWitness e45Laws where
  a := (0xa7, 0xe9)
  b := (0xb7, 0xb)
  vx := 0x43160000
  vy := 0xb8520000
  vs := 0x4315fffd
  vd := 0x4315fffc
  vlt := 0x4315fffd
  vgt := 0x4315fffc
  e₁ := by decide +kernel
  e₂ := by decide +kernel
  e₃ := by decide +kernel
  e₄ := by decide +kernel
  e₅ := by decide +kernel
  e₆ := by decide +kernel
  g₁ := by show GoodW _; decide +kernel
  g₂ := by show GoodW _; decide +kernel
  g₃ := by show GoodW _; decide +kernel
  g₄ := by show GoodW _; decide +kernel
  g₅ := by show GoodW _; decide +kernel
  g₆ := by show GoodW _; decide +kernel
  sep := by decide

/-- **CDNA 3 FP8 (E4M3 × E5M2), completeness for chains.** Two chains over the same products, each
once, that differ in the parity pattern of some pair of products differ on an input supported on
that pair. -/
theorem e45_chain_complete (σ τ : MMAlgebra.Chain) (hσ : ∀ B ∈ σ, B.length = 16)
    (hτ : ∀ B ∈ τ, B.length = 16) (nσ : σ.leaves.Nodup) (nτ : τ.leaves.Nodup)
    (hl : ∀ i, i ∈ σ.leaves ↔ i ∈ τ.leaves)
    (hne : ∃ x y, x ∈ σ.leaves ∧ y ∈ σ.leaves ∧ x ≠ y ∧
      MMAlgebra.Parity.ppattern x y σ ≠ MMAlgebra.Parity.ppattern x y τ) :
    ∃ (x y : ℕ) (q : ℕ → E45.a.Word × E45.b.Word), x ≠ y ∧ (∀ i, i ≠ x → i ≠ y → q i = (0, 0)) ∧
      MMAlgebra.runChain (mcMachine E45) q 0 σ ≠ MMAlgebra.runChain (mcMachine E45) q 0 τ :=
  MMAlgebra.Parity.chain_complete_parity e45Laws (by decide) (by decide) e45Witness σ τ hσ hτ nσ nτ hl hne

/-- The laws of a parity-pair multiplier, for CDNA 3 FP8 (E5M2 × E4M3). -/
def e54Laws : MMAlgebra.Parity.ParityLaws (mcMachine E54) 16 where
  z := (0, 0)
  good := GoodW
  slot := cdna3FP8_slotZero e5m2fnuz e4m3fnuz
  grp := fun d _ _ h => cdna3FP8_machine_parity e5m2fnuz e4m3fnuz d h
  zero_good := mc_zero_good
  pass := e54_pass

def e54Witness : MMAlgebra.Parity.ParityWitness e54Laws where
  a := (0x5e, 0xa2)
  b := (0x7, 0x92)
  vx := 0xc1700000
  vy := 0xb58c0000
  vs := 0xc1700001
  vd := 0xc1700002
  vlt := 0xc1700001
  vgt := 0xc1700002
  e₁ := by decide +kernel
  e₂ := by decide +kernel
  e₃ := by decide +kernel
  e₄ := by decide +kernel
  e₅ := by decide +kernel
  e₆ := by decide +kernel
  g₁ := by show GoodW _; decide +kernel
  g₂ := by show GoodW _; decide +kernel
  g₃ := by show GoodW _; decide +kernel
  g₄ := by show GoodW _; decide +kernel
  g₅ := by show GoodW _; decide +kernel
  g₆ := by show GoodW _; decide +kernel
  sep := by decide

/-- **CDNA 3 FP8 (E5M2 × E4M3), completeness for chains.** Two chains over the same products, each
once, that differ in the parity pattern of some pair of products differ on an input supported on
that pair. -/
theorem e54_chain_complete (σ τ : MMAlgebra.Chain) (hσ : ∀ B ∈ σ, B.length = 16)
    (hτ : ∀ B ∈ τ, B.length = 16) (nσ : σ.leaves.Nodup) (nτ : τ.leaves.Nodup)
    (hl : ∀ i, i ∈ σ.leaves ↔ i ∈ τ.leaves)
    (hne : ∃ x y, x ∈ σ.leaves ∧ y ∈ σ.leaves ∧ x ≠ y ∧
      MMAlgebra.Parity.ppattern x y σ ≠ MMAlgebra.Parity.ppattern x y τ) :
    ∃ (x y : ℕ) (q : ℕ → E54.a.Word × E54.b.Word), x ≠ y ∧ (∀ i, i ≠ x → i ≠ y → q i = (0, 0)) ∧
      MMAlgebra.runChain (mcMachine E54) q 0 σ ≠ MMAlgebra.runChain (mcMachine E54) q 0 τ :=
  MMAlgebra.Parity.chain_complete_parity e54Laws (by decide) (by decide) e54Witness σ τ hσ hτ nσ nτ hl hne

end MMAlgebra.MC.FP8
