import TensorCore.Kernels.EFT.Preparation

/-! Correctness of bounded extraction. -/

namespace TensorCore.EFMachine

set_option exponentiation.threshold 1024

theorem split_magnitudeSum (ts : List Term) (g : Grid) :
    wordMagnitudeSum ((ts.map fun t => t.word.split g).map WordSplit.coarse) ≤
      wordMagnitudeSum (ts.map Term.word) ∧
    wordMagnitudeSum ((ts.map fun t => t.word.split g).map WordSplit.low) ≤
      wordMagnitudeSum (ts.map Term.word) := by
  induction ts with
  | nil => simp [wordMagnitudeSum]
  | cons t ts ih =>
    have hs := t.word.split_magnitude g
    simp only [List.map_cons, wordMagnitudeSum, List.sum_cons] at *
    omega

theorem split_sum (ts : List Term) (g : Grid) :
    sumQ (((ts.map fun t => t.word.split g).map WordSplit.coarse).map Word.value) +
      sumQ (((ts.map fun t => t.word.split g).map WordSplit.low).map Word.value) =
      sumQ (ts.map fun t => t.word.value) := by
  induction ts with
  | nil => simp [sumQ, Rat.zero_add]
  | cons t ts ih =>
    have hs := t.word.split_reconstruct g
    simp only [List.map_cons, sumQ]
    grind [Rat.add_assoc, Rat.add_comm]

theorem extract_exists {p : Prepared}
    (hp : wordMagnitudeSum (p.terms.map Term.word) < 2 ^ 555)
    (hd : p.output.magnitude.toNat < 2 ^ 424) : ∃ c, extract p = some c := by
  let hi := (p.terms.map fun t => t.word.split p.grid).map WordSplit.coarse
  let lo := (p.terms.map fun t => t.word.split p.grid).map WordSplit.low
  have hb := split_magnitudeSum p.terms p.grid
  have hhi : wordMagnitudeSum hi < 2 ^ 555 := by dsimp [hi]; omega
  have hlo : wordMagnitudeSum lo < 2 ^ 555 := by dsimp [lo]; omega
  obtain ⟨h, hh, hmh⟩ := sumWords_exists hi (by omega)
  obtain ⟨o, ho⟩ := p.output.add_exists h.neg (by change _ + h.magnitude.toNat < _; omega)
  have hmo := Word.add_magnitude ho
  change o.magnitude.toNat ≤ p.output.magnitude.toNat + h.magnitude.toNat at hmo
  obtain ⟨e, he, hme⟩ := sumWords_exists lo (by omega)
  obtain ⟨d, hdd⟩ := p.output.add_exists o.neg (by change _ + o.magnitude.toNat < _; omega)
  have hmd := Word.add_magnitude hdd
  change d.magnitude.toNat ≤ p.output.magnitude.toNat + o.magnitude.toNat at hmd
  obtain ⟨s, hs⟩ := d.add_exists e (by omega)
  exact ⟨⟨p, hi, lo, h, o, e, s⟩, by
    dsimp only [hi] at hh
    dsimp only [lo] at he
    simp [-List.map_map, extract, hi, lo, Word.sub, hh, ho, he, hdd, hs]⟩

/-- The complete signed extraction identity. -/
theorem extract_spec {p : Prepared} {c : Components} (hc : extract p = some c) :
    c.prepared = p ∧
    c.coarse = (p.terms.map fun t => t.word.split p.grid).map WordSplit.coarse ∧
    c.low = (p.terms.map fun t => t.word.split p.grid).map WordSplit.low ∧
    c.retained.value = sumQ (c.coarse.map Word.value) ∧
    c.overlap.value = p.output.value - c.retained.value ∧
    c.residualSum.value = sumQ (c.low.map Word.value) ∧
    c.recovered.value = c.retained.value + c.residualSum.value ∧
    c.recovered.value = p.ideal := by
  unfold extract at hc
  dsimp only at hc
  cases hh : sumWords ((p.terms.map fun t => t.word.split p.grid).map WordSplit.coarse) with
  | none => simp [-List.map_map, hh] at hc
  | some h =>
    cases ho : p.output.sub h with
    | none => simp [-List.map_map, hh, ho] at hc
    | some o =>
      cases he : sumWords ((p.terms.map fun t => t.word.split p.grid).map WordSplit.low) with
      | none => simp [-List.map_map, hh, he] at hc
      | some e =>
        cases hd : p.output.sub o with
        | none => simp [-List.map_map, hh, ho, he, hd] at hc
        | some d =>
          cases hs : d.add e with
          | none => simp [-List.map_map, hh, ho, he, hd, hs] at hc
          | some s =>
            simp [-List.map_map, hh, ho, he, hd, hs] at hc
            subst c
            have hvh := sumWords_value hh
            have hvo := Word.sub_value ho
            have hve := sumWords_value he
            have hvd := Word.sub_value hd
            have hvs := Word.add_value hs
            have hsum := split_sum p.terms p.grid
            refine ⟨rfl, rfl, rfl, hvh, hvo, hve, ?_, ?_⟩
            · dsimp only; grind [Rat.sub_eq_add_neg]
            · dsimp only [Prepared.ideal]; grind [Rat.sub_eq_add_neg]

/-- Each coarse part is the truncation to the grid and each low part the remainder. -/
theorem extract_component (t : Term) (g : Grid) :
    (t.word.split g).coarse.value = truncGrid t.word.value (g.toNat - 272) ∧
    (t.word.split g).low.value = t.word.value - truncGrid t.word.value (g.toNat - 272) :=
  ⟨t.word.split_coarse_value g, t.word.split_low_value g⟩

end TensorCore.EFMachine
