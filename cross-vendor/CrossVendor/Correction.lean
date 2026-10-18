import CrossVendor.Rounding

/-! # TC-EFT and MC-EFT return the same word

A Tensor Core block and a Matrix Core block with the same exact sum `S` give different outputs, but
TC-EFT and MC-EFT both return `S` rounded to nearest even, from any finite `D` on either side. -/

namespace CrossVendor

theorem prepareProducts_cons (p : TensorCore.Model) (a b : p.Word) (ws : List (p.Word × p.Word)) :
    TensorCore.prepareProducts p ((a, b) :: ws) =
      (p.decode a).bind fun x => (p.decode b).bind fun y =>
        (TensorCore.prepareProducts p ws).map fun ps => (x, y) :: ps := by
  unfold TensorCore.prepareProducts
  rw [List.mapM_cons]
  cases h1 : p.decode a <;> cases h2 : p.decode b <;> simp [h1, h2]
  cases List.mapM (fun x : p.Word × p.Word => match x with
    | (a, b) => do let a ← p.decode a; let b ← p.decode b; pure (a, b)) ws <;> rfl

theorem mapM_decPair_cons (P : MatrixCore.Model) (q : P.a.Word × P.b.Word)
    (qs : List (P.a.Word × P.b.Word)) :
    (q :: qs).mapM (MatrixCore.decPair P) =
      (MatrixCore.decPair P q).bind fun u => (qs.mapM (MatrixCore.decPair P)).map (u :: ·) := by
  rw [List.mapM_cons]
  cases MatrixCore.decPair P q <;> cases qs.mapM (MatrixCore.decPair P) <;> rfl

/-- The decoded products of a block: the same values in both libraries when every operand word
decodes to the same value. -/
theorem products_eq {p : TensorCore.Model} {P : MatrixCore.Model}
    (fa : p.Word → P.a.Word) (fb : p.Word → P.b.Word)
    (ha : ∀ w, (p.decode w).map TensorCore.Decoded.value =
      (P.a.read (fa w)).toFinite.map MatrixCore.Unpacked.value)
    (hb : ∀ w, (p.decode w).map TensorCore.Decoded.value =
      (P.b.read (fb w)).toFinite.map MatrixCore.Unpacked.value) :
    ∀ ws : List (p.Word × p.Word),
      (TensorCore.prepareProducts p ws).map
          (fun ps => ps.map fun (a, b) => a.value * b.value) =
        ((ws.map fun (a, b) => (fa a, fb b)).mapM (MatrixCore.decPair P)).map
          (fun L => L.map fun q => q.1.value * q.2.value)
  | [] => rfl
  | (a, b) :: ws => by
    have ih := products_eq fa fb ha hb ws
    have ha' := ha a
    have hb' := hb b
    have hd : MatrixCore.decPair P (fa a, fb b) = (P.a.read (fa a)).toFinite.bind fun u =>
        (P.b.read (fb b)).toFinite.map fun v => (u, v) := rfl
    rw [prepareProducts_cons, List.map_cons, mapM_decPair_cons, hd]
    cases hT : TensorCore.prepareProducts p ws <;>
      cases hM : List.mapM (MatrixCore.decPair P) (ws.map fun (a, b) => (fa a, fb b)) <;>
      rw [hT, hM] at ih <;> simp only [Option.map_none, Option.map_some, reduceCtorEq,
        Option.some.injEq] at ih <;>
    cases h1 : p.decode a <;> cases h2 : (P.a.read (fa a)).toFinite <;>
      simp only [h1, h2, Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq]
        at ha' ⊢ <;>
    cases h3 : p.decode b <;> cases h4 : (P.b.read (fb b)).toFinite <;>
      simp only [h3, h4, Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq,
        Option.bind_some, Option.bind_none, List.map_cons] at hb' ⊢
    rw [ha', hb', ih]

/-- Blocks whose operand words decode to the same values have the same exact sum
`Σ a_ℓ b_ℓ + c` in both libraries. -/
theorem exact_eq {p : TensorCore.Model} {P : MatrixCore.Model}
    (fa : p.Word → P.a.Word) (fb : p.Word → P.b.Word)
    (ha : ∀ w, (p.decode w).map TensorCore.Decoded.value =
      (P.a.read (fa w)).toFinite.map MatrixCore.Unpacked.value)
    (hb : ∀ w, (p.decode w).map TensorCore.Decoded.value =
      (P.b.read (fb w)).toFinite.map MatrixCore.Unpacked.value)
    (ws : List (p.Word × p.Word)) (c : BitVec 32) :
    TensorCore.exactDot (⟨ws, c⟩ : TensorCore.BlockInput p) =
      (MatrixCore.prepare (P := P) ⟨(ws.map fun (a, b) => (fa a, fb b)).map Prod.fst,
        (ws.map fun (a, b) => (fa a, fb b)).map Prod.snd, c⟩).map MatrixCore.Prepared.exact := by
  have hp := products_eq fa fb ha hb ws
  have hc := value32_eq c
  rw [MatrixCore.prepare_pairs]
  unfold TensorCore.exactDot TensorCore.prepare
  unfold TensorCore.value32 MatrixCore.value32 at hc
  cases h1 : TensorCore.decode32 c <;> cases h2 : (MatrixCore.fp32.decode c).toFinite <;>
    simp only [h1, h2, Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq] at hc <;>
  cases h3 : TensorCore.prepareProducts p ws <;>
    cases h4 : List.mapM (MatrixCore.decPair P) (ws.map fun (a, b) => (fa a, fb b)) <;>
    simp only [h3, h4, Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq,
      Option.bind_none, Option.bind_some] at hp ⊢
  simp only [MatrixCore.Prepared.exact, MatrixCore.products_pairs, List.map_map,
    Function.comp_def, MatrixCore.Unpacked.value_mul, ← sumQ_eq,
    TensorCore.PreparedBlock.exactDot, TensorCore.PreparedBlock.exactProducts]
  rw [hp, hc]
  exact Rat.add_comm _ _

/-- **The correction does not depend on the vendor.** For a Tensor Core block and a Matrix Core
block with the same exact sum `S` in the FP32 range, TC-EFT and MC-EFT both return a word, the
same one: `S` rounded to nearest even. `D` and `D'` are any finite FP32 words, such as the two
blocks' own outputs. -/
theorem corrections_agree {variant : TensorCore.EFMachine.Variant}
    {x : TensorCore.BlockInput variant.model} {P : MatrixCore.Model} {y : MatrixCore.BlockInput P}
    {D D' : BitVec 32} {s d d' : Rat} {py : MatrixCore.Prepared}
    (hlen : x.products.length = variant.model.nfma) (hla : y.a.length = P.nfma)
    (hlb : y.b.length = P.nfma) (hx : TensorCore.exactDot x = some s)
    (hy : MatrixCore.prepare y = some py) (hs : py.exact = s)
    (hD : TensorCore.value32 D = some d) (hD' : MatrixCore.value32 D' = some d')
    (hr : TensorCore.absQ s ≤ TensorCore.maxFinite32) :
    ∃ r r' b, TensorCore.EFMachine.tcEft variant x D = .ok r ∧ MatrixCore.mcEft y D' = .ok r' ∧
      r.bits = some b ∧ r'.bits = some b ∧ TensorCore.round32 .nearestEven s = some b := by
  obtain ⟨r, htc, hb⟩ := TensorCore.EFMachine.tcEft_correct hlen hx hD
  obtain ⟨r', hmc⟩ := (MatrixCore.mcEft_ok_iff y D').mpr ⟨hla, hlb, ⟨py, hy⟩, ⟨d', hD'⟩⟩
  obtain ⟨py', hpy', hb'⟩ := MatrixCore.mcEft_bits hmc
  rw [hy] at hpy'
  cases hpy'
  obtain ⟨b, hround, -⟩ := TensorCore.round32_nearestEven_correct s hr
  refine ⟨r, r', b, htc, hmc, hb.trans hround, ?_, hround⟩
  rw [hb', hs, ← round32_eq_rne32 hr, hround]

/-- The same operand words on a Tensor Core and a Matrix Core of the same block size: TC-EFT and
MC-EFT return the same word whenever the exact sum is in the FP32 range. -/
theorem corrections_agree_words {variant : TensorCore.EFMachine.Variant} {P : MatrixCore.Model}
    (fa : variant.model.Word → P.a.Word) (fb : variant.model.Word → P.b.Word)
    (ha : ∀ w, (variant.model.decode w).map TensorCore.Decoded.value =
      (P.a.read (fa w)).toFinite.map MatrixCore.Unpacked.value)
    (hb : ∀ w, (variant.model.decode w).map TensorCore.Decoded.value =
      (P.b.read (fb w)).toFinite.map MatrixCore.Unpacked.value)
    (hn : P.nfma = variant.model.nfma) (ws : List (variant.model.Word × variant.model.Word))
    (c D D' : BitVec 32) {s d d' : Rat} (hlen : ws.length = variant.model.nfma)
    (hx : TensorCore.exactDot (⟨ws, c⟩ : TensorCore.BlockInput variant.model) = some s)
    (hD : TensorCore.value32 D = some d) (hD' : MatrixCore.value32 D' = some d')
    (hr : TensorCore.absQ s ≤ TensorCore.maxFinite32) :
    ∃ r r' b, TensorCore.EFMachine.tcEft variant ⟨ws, c⟩ D = .ok r ∧
      MatrixCore.mcEft (P := P) ⟨ws.map (fa ·.1), ws.map (fb ·.2), c⟩ D' = .ok r' ∧
      r.bits = some b ∧ r'.bits = some b ∧ TensorCore.round32 .nearestEven s = some b := by
  have he := exact_eq fa fb ha hb ws c
  simp only [List.map_map, Function.comp_def] at he
  rw [hx] at he
  obtain ⟨py, hpy, hs⟩ := Option.map_eq_some_iff.mp he.symm
  exact corrections_agree hlen (by simp [hlen, hn]) (by simp [hlen, hn]) hx hpy hs hD hD' hr

/-- **FP16: A100 and CDNA 3.** For the same eight FP16 operand pairs and `c`, TC-EFT and MC-EFT
return the same word from any finite outputs, whenever the exact sum is in the FP32 range. -/
theorem fp16_ampere_cdna3 (ws : List (BitVec 16 × BitVec 16)) (c D D' : BitVec 32) {s d d' : Rat}
    (hlen : ws.length = 8) (hx : TensorCore.exactDot (p := TensorCore.ampereF16F32) ⟨ws, c⟩ = some s)
    (hD : TensorCore.value32 D = some d) (hD' : MatrixCore.value32 D' = some d')
    (hr : TensorCore.absQ s ≤ TensorCore.maxFinite32) :
    ∃ r r' b, TensorCore.EFMachine.tcEft .ampereF16 ⟨ws, c⟩ D = .ok r ∧
      MatrixCore.mcEft (P := MatrixCore.cdna3F16) ⟨ws.map Prod.fst, ws.map Prod.snd, c⟩ D' = .ok r' ∧
      r.bits = some b ∧ r'.bits = some b :=
  let ⟨r, r', b, h1, h2, h3, h4, _⟩ := corrections_agree_words (variant := .ampereF16)
    (P := MatrixCore.cdna3F16) id id fp16_value_eq fp16_value_eq rfl ws c D D' hlen hx hD hD' hr
  ⟨r, r', b, h1, h2, h3, h4⟩

/-- **FP16: V100 and CDNA 1.** The same for four FP16 operand pairs. -/
theorem fp16_volta_cdna1 (ws : List (BitVec 16 × BitVec 16)) (c D D' : BitVec 32) {s d d' : Rat}
    (hlen : ws.length = 4) (hx : TensorCore.exactDot (p := TensorCore.v100F16F32) ⟨ws, c⟩ = some s)
    (hD : TensorCore.value32 D = some d) (hD' : MatrixCore.value32 D' = some d')
    (hr : TensorCore.absQ s ≤ TensorCore.maxFinite32) :
    ∃ r r' b, TensorCore.EFMachine.tcEft .v100F16 ⟨ws, c⟩ D = .ok r ∧
      MatrixCore.mcEft (P := MatrixCore.cdna1F16) ⟨ws.map Prod.fst, ws.map Prod.snd, c⟩ D' = .ok r' ∧
      r.bits = some b ∧ r'.bits = some b :=
  let ⟨r, r', b, h1, h2, h3, h4, _⟩ := corrections_agree_words (variant := .v100F16)
    (P := MatrixCore.cdna1F16) id id fp16_value_eq fp16_value_eq rfl ws c D D' hlen hx hD hD' hr
  ⟨r, r', b, h1, h2, h3, h4⟩

/-- **BF16: A100 and CDNA 3.** The same for eight BF16 operand pairs. -/
theorem bf16_ampere_cdna3 (ws : List (BitVec 16 × BitVec 16)) (c D D' : BitVec 32) {s d d' : Rat}
    (hlen : ws.length = 8) (hx : TensorCore.exactDot (p := TensorCore.a100BF16F32) ⟨ws, c⟩ = some s)
    (hD : TensorCore.value32 D = some d) (hD' : MatrixCore.value32 D' = some d')
    (hr : TensorCore.absQ s ≤ TensorCore.maxFinite32) :
    ∃ r r' b, TensorCore.EFMachine.tcEft .ampereBF16 ⟨ws, c⟩ D = .ok r ∧
      MatrixCore.mcEft (P := MatrixCore.cdna3BF16) ⟨ws.map Prod.fst, ws.map Prod.snd, c⟩ D' = .ok r' ∧
      r.bits = some b ∧ r'.bits = some b :=
  let ⟨r, r', b, h1, h2, h3, h4, _⟩ := corrections_agree_words (variant := .ampereBF16)
    (P := MatrixCore.cdna3BF16) id id bf16_value_eq bf16_value_eq rfl ws c D D' hlen hx hD hD' hr
  ⟨r, r', b, h1, h2, h3, h4⟩

end CrossVendor
