import MMAlgebra.Divergence
import MMAlgebraTC.Block
import OzakiTC.Cancellation
import OzakiTC.MatrixMultiplier
import OzakiTC.Schemes

/-! # Inside the exact region every schedule agrees (Tensor Core model)

`tcMachine p` is the Tensor Core model as a `MMAlgebra.Machine`: binary32 accumulator words,
operand pairs, `evalBlock` for a block FMA (an empty slot is the zero pair), and binary32
round-to-nearest-even addition. On integer operands of at most `b` bits (as in the Ozaki schemes),
with an integer `c` and `|c| + Σ|aᵢbᵢ| < 2^24`, every block FMA and every addition of every term is
exact (Ozaki's exactness theorem with cancellation, `Ozaki.TC.evalBlock_cancel_int`), so every
term returns its exact value and any two terms over the same products return the same value
(`eval_agree`). -/

open TensorCore Ozaki.TC

namespace MMAlgebra.TC

/-- The operand pairs of a block's slots: an empty slot is the zero pair. -/
def slotPairs (p : Model) (ps : List (Option (p.Word × p.Word))) : List (p.Word × p.Word) :=
  ps.map fun o => o.getD (0, 0)

/-- The Tensor Core model as a machine for reduction terms. -/
def tcMachine (p : Model) : MMAlgebra.Machine (p.Word × p.Word) F32 where
  val := value32D
  pval q := wordValue p q.1 * wordValue p q.2
  zero := 0
  val_zero := by decide +kernel
  block d ps := (blockOut (p := p) ⟨slotPairs p ps, d⟩).toOption
  add x y := round32 .nearestEven (value32D x + value32D y)

/-- A term without holes whose blocks all have `K` slots. -/
def TermWF (K : ℕ) : MMAlgebra.Term → Prop
  | .zero => True
  | .init => True
  | .hole => False
  | .blk t I => TermWF K t ∧ I.length = K
  | .add t u => TermWF K t ∧ TermWF K u

theorem intWord_zero {p : Model} {b : ℕ} (hh : HoldsInts p b) : IntWord p b (0 : p.Word) := by
  refine ⟨by rw [Model.decode, decode_zero_word p.input hh.wellFormed]; rfl, 0, ?_, by simp⟩
  unfold wordValue decodeD Model.decode; rw [decode_zero_word p.input hh.wellFormed]
  simp [Decoded.value]

theorem wordValue_zero {p : Model} {b : ℕ} (hh : HoldsInts p b) : wordValue p (0 : p.Word) = 0 := by
  unfold wordValue decodeD Model.decode; rw [decode_zero_word p.input hh.wellFormed]
  simp [Decoded.value]

/-- The block's products are the slots' products. -/
theorem wordProducts_slots {p : Model} {b : ℕ} (hh : HoldsInts p b) :
    ∀ ps : List (Option (p.Word × p.Word)),
      wordProducts p (slotPairs p ps) = (tcMachine p).slotVal ps
  | [] => by simp [wordProducts, slotPairs, MMAlgebra.Machine.slotVal]
  | o :: ps => by
    have ih := wordProducts_slots hh ps
    simp only [wordProducts, slotPairs, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, (tcMachine p).slotVal_cons]
    cases o with
    | none =>
      show wordValue p (0 : p.Word) * wordValue p (0 : p.Word) + _ = _
      rw [wordValue_zero hh]; simp
    | some q => rfl

theorem value32D_of {c : F32} {v : ℚ} (h : value32 c = some v) : value32D c = v := by
  simp [value32D, h]

/-- One block FMA inside the exact region returns the exact sum of its inputs. -/
theorem block_int {p : Model} {b : ℕ} (hp : IntExact p b) (hh : HoldsInts p b)
    (q : ℕ → p.Word × p.Word) (hq : ∀ i, IntWord p b (q i).1 ∧ IntWord p b (q i).2)
    {d : F32} {zd : ℤ} (hvd : value32 d = some (zd : ℚ)) (I : List (Option ℕ))
    (hlen : I.length = p.nfma) (hzd : Rat.abs (zd : ℚ) < 2 ^ (24 : ℤ))
    (hsum : Rat.abs ((zd : ℚ) + (tcMachine p).slotVal (I.map (Option.map q))) ≤ 2 ^ (24 : ℤ)) :
    ∃ (o : F32) (z : ℤ), (tcMachine p).block d (I.map (Option.map q)) = some o ∧
      value32 o = some (z : ℚ) ∧ (z : ℚ) = zd + (tcMachine p).slotVal (I.map (Option.map q)) := by
  have hops : ∀ r ∈ slotPairs p (I.map (Option.map q)), IntWord p b r.1 ∧ IntWord p b r.2 := by
    intro r hr
    simp only [slotPairs, List.map_map, List.mem_map] at hr
    obtain ⟨o, _, rfl⟩ := hr
    cases o with
    | none => exact ⟨intWord_zero hh, intWord_zero hh⟩
    | some i => exact hq i
  have hslots := wordProducts_slots hh (I.map (Option.map q))
  rw [← hslots] at hsum
  have hl : (slotPairs p (I.map (Option.map q))).length = p.nfma := by
    simp only [slotPairs, List.length_map]; exact hlen
  obtain ⟨tr, htr, hval⟩ := evalBlock_cancel_int
    (x := (⟨slotPairs p (I.map (Option.map q)), d⟩ : BlockInput p)) hp hl hops hvd hzd hsum
  obtain ⟨Z, hZ, _⟩ := wordProducts_int _ hops
  refine ⟨tr.output.bits, zd + Z, ?_, ?_, ?_⟩
  · have hb : blockOut (p := p) ⟨slotPairs p (I.map (Option.map q)), d⟩ = .ok tr.output.bits := by
      unfold blockOut; rw [htr]; rfl
    show (blockOut (p := p) ⟨slotPairs p (I.map (Option.map q)), d⟩).toOption = _
    rw [hb]; rfl
  · rw [value32_output, hval, hZ, Rat.intCast_add]
  · rw [Rat.intCast_add, ← hZ, hslots]

/-- One binary32 addition of integers within `2^24` is exact. -/
theorem add_int (p : Model) {x y : F32} {zx zy : ℤ} (hvx : value32 x = some (zx : ℚ))
    (hvy : value32 y = some (zy : ℚ)) (hle : (zx + zy).natAbs ≤ 2 ^ 24) :
    ∃ w : F32, (tcMachine p).add x y = some w ∧ value32 w = some ((zx + zy : ℤ) : ℚ) := by
  obtain ⟨w, hw, hvw⟩ := round32_exact_of_finite (int_finiteValue32 (zx + zy) hle)
  refine ⟨w, ?_, hvw⟩
  show round32 .nearestEven (value32D x + value32D y) = some w
  rw [value32D_of hvx, value32D_of hvy, ← Rat.intCast_add]; exact hw

theorem natAbs_le_of_abs_lt {z : ℤ} (h : Rat.abs (z : ℚ) < 2 ^ (24 : ℤ)) : z.natAbs ≤ 2 ^ 24 := by
  rw [Ozaki.abs_intCast] at h
  have h24 : (2 : ℚ) ^ (24 : ℤ) = ((2 ^ 24 : ℕ) : ℚ) := by decide
  rw [h24] at h
  have := Rat.natCast_lt_natCast.mp h
  omega

/-- **Exact region.** Integer operands of at most `b` bits, an integer `c`, and a term whose
products and `c` have total magnitude below `2^24`: the term evaluates to its exact value. -/
theorem eval_int {p : Model} {b : ℕ} (hp : IntExact p b) (hh : HoldsInts p b)
    (q : ℕ → p.Word × p.Word) (hq : ∀ i, IntWord p b (q i).1 ∧ IntWord p b (q i).2)
    (c : F32) {zc : ℤ} (hc : value32 c = some (zc : ℚ)) :
    ∀ t : MMAlgebra.Term, TermWF p.nfma t →
      MMAlgebra.mag (tcMachine p) q (Rat.abs (zc : ℚ)) 0 t < 2 ^ (24 : ℤ) →
      ∃ (o : F32) (z : ℤ), MMAlgebra.eval (tcMachine p) q c c t = some o ∧
        value32 o = some (z : ℚ) ∧ (z : ℚ) = MMAlgebra.exact (tcMachine p) q (zc : ℚ) 0 t
  | .zero, _, _ => ⟨0, 0, rfl, by decide +kernel, by simp [MMAlgebra.exact]⟩
  | .init, _, _ => ⟨c, zc, rfl, hc, by simp [MMAlgebra.exact]⟩
  | .hole, hwf, _ => absurd hwf (by simp [TermWF])
  | .blk t I, hwf, hm => by
    obtain ⟨hwt, hlen⟩ := hwf
    have hsa := (tcMachine p).slotAbs_nonneg (I.map (Option.map q))
    have hm' : MMAlgebra.mag (tcMachine p) q (Rat.abs (zc : ℚ)) 0 t +
        (tcMachine p).slotAbs (I.map (Option.map q)) < 2 ^ (24 : ℤ) := hm
    obtain ⟨d, zd, hd, hvd, hzd⟩ := eval_int hp hh q hq c hc t hwt (by grind)
    have hex := MMAlgebra.abs_exact_le (tcMachine p) q (zc : ℚ) 0 (.blk t I)
    have hext := MMAlgebra.abs_exact_le (tcMachine p) q (zc : ℚ) 0 t
    rw [Ozaki.abs_zero] at hex hext
    have hex' : Rat.abs (MMAlgebra.exact (tcMachine p) q (zc : ℚ) 0 t +
        (tcMachine p).slotVal (I.map (Option.map q))) ≤
        MMAlgebra.mag (tcMachine p) q (Rat.abs (zc : ℚ)) 0 t +
          (tcMachine p).slotAbs (I.map (Option.map q)) := hex
    obtain ⟨o, z, ho, hvo, hz⟩ := block_int hp hh q hq hvd I hlen
      (by rw [hzd]; grind) (by rw [hzd]; grind)
    refine ⟨o, z, ?_, hvo, ?_⟩
    · show (MMAlgebra.eval (tcMachine p) q c c t).bind _ = _
      rw [hd]; exact ho
    · rw [hz, hzd]; rfl
  | .add t u, hwf, hm => by
    obtain ⟨hwt, hwu⟩ := hwf
    have h1 := MMAlgebra.mag_nonneg (tcMachine p) q (Ozaki.abs_nonneg (zc : ℚ)) Rat.le_refl t
    have h2 := MMAlgebra.mag_nonneg (tcMachine p) q (Ozaki.abs_nonneg (zc : ℚ)) Rat.le_refl u
    have hm' : MMAlgebra.mag (tcMachine p) q (Rat.abs (zc : ℚ)) 0 t +
        MMAlgebra.mag (tcMachine p) q (Rat.abs (zc : ℚ)) 0 u < 2 ^ (24 : ℤ) := hm
    obtain ⟨x, zx, hx, hvx, hzx⟩ := eval_int hp hh q hq c hc t hwt (by grind)
    obtain ⟨y, zy, hy, hvy, hzy⟩ := eval_int hp hh q hq c hc u hwu (by grind)
    have hex := MMAlgebra.abs_exact_le (tcMachine p) q (zc : ℚ) 0 (.add t u)
    rw [Ozaki.abs_zero] at hex
    have hex' : Rat.abs (MMAlgebra.exact (tcMachine p) q (zc : ℚ) 0 t +
        MMAlgebra.exact (tcMachine p) q (zc : ℚ) 0 u) ≤
        MMAlgebra.mag (tcMachine p) q (Rat.abs (zc : ℚ)) 0 t +
          MMAlgebra.mag (tcMachine p) q (Rat.abs (zc : ℚ)) 0 u := hex
    have hle : (zx + zy).natAbs ≤ 2 ^ 24 :=
      natAbs_le_of_abs_lt (by rw [Rat.intCast_add, hzx, hzy]; grind)
    obtain ⟨w, hw, hvw⟩ := add_int p hvx hvy hle
    refine ⟨w, zx + zy, ?_, hvw, ?_⟩
    · show (MMAlgebra.eval (tcMachine p) q c c t).bind _ = _
      rw [hx]; show (MMAlgebra.eval (tcMachine p) q c c u).bind _ = _
      rw [hy]; exact hw
    · rw [Rat.intCast_add, hzx, hzy]; rfl

/-- **Every schedule agrees inside the exact region.** Two terms over the same products and `c`
(equal exact values), each with total magnitude below `2^24`, on integer operands: both return
the same binary32 value. -/
theorem eval_agree {p : Model} {b : ℕ} (hp : IntExact p b) (hh : HoldsInts p b)
    (q : ℕ → p.Word × p.Word) (hq : ∀ i, IntWord p b (q i).1 ∧ IntWord p b (q i).2)
    (c : F32) {zc : ℤ} (hc : value32 c = some (zc : ℚ)) (t₁ t₂ : MMAlgebra.Term)
    (hw₁ : TermWF p.nfma t₁) (hw₂ : TermWF p.nfma t₂)
    (hm₁ : MMAlgebra.mag (tcMachine p) q (Rat.abs (zc : ℚ)) 0 t₁ < 2 ^ (24 : ℤ))
    (hm₂ : MMAlgebra.mag (tcMachine p) q (Rat.abs (zc : ℚ)) 0 t₂ < 2 ^ (24 : ℤ))
    (hex : MMAlgebra.exact (tcMachine p) q (zc : ℚ) 0 t₁ = MMAlgebra.exact (tcMachine p) q (zc : ℚ) 0 t₂) :
    ∃ o₁ o₂ : F32, MMAlgebra.eval (tcMachine p) q c c t₁ = some o₁ ∧
      MMAlgebra.eval (tcMachine p) q c c t₂ = some o₂ ∧ value32 o₁ = value32 o₂ := by
  obtain ⟨o₁, z₁, h₁, hv₁, hz₁⟩ := eval_int hp hh q hq c hc t₁ hw₁ hm₁
  obtain ⟨o₂, z₂, h₂, hv₂, hz₂⟩ := eval_int hp hh q hq c hc t₂ hw₂ hm₂
  exact ⟨o₁, o₂, h₁, h₂, by rw [hv₁, hv₂, hz₁, hz₂, hex]⟩

/-- On V100 with fp16 operands that are integers of at most 11 bits: every two schedules agree
inside the exact region. -/
theorem v100_agree (q : ℕ → F16 × F16) (hq : ∀ i, IntWord v100F16F32 11 (q i).1 ∧
      IntWord v100F16F32 11 (q i).2)
    (c : F32) {zc : ℤ} (hc : value32 c = some (zc : ℚ)) (t₁ t₂ : MMAlgebra.Term)
    (hw₁ : TermWF 4 t₁) (hw₂ : TermWF 4 t₂)
    (hm₁ : MMAlgebra.mag (tcMachine v100F16F32) q (Rat.abs (zc : ℚ)) 0 t₁ < 2 ^ (24 : ℤ))
    (hm₂ : MMAlgebra.mag (tcMachine v100F16F32) q (Rat.abs (zc : ℚ)) 0 t₂ < 2 ^ (24 : ℤ))
    (hex : MMAlgebra.exact (tcMachine v100F16F32) q (zc : ℚ) 0 t₁ =
      MMAlgebra.exact (tcMachine v100F16F32) q (zc : ℚ) 0 t₂) :
    ∃ o₁ o₂ : F32, MMAlgebra.eval (tcMachine v100F16F32) q c c t₁ = some o₁ ∧
      MMAlgebra.eval (tcMachine v100F16F32) q c c t₂ = some o₂ ∧ value32 o₁ = value32 o₂ :=
  eval_agree v100_intExact v100_holdsInts q hq c hc t₁ t₂ hw₁ hw₂ hm₁ hm₂ hex

end MMAlgebra.TC
