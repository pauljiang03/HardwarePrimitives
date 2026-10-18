import TCFloat.Equivalence.Encoded
import TensorCore.TC.Flowback
import TensorCore.TC.MonotonicityRange

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
namespace TCFloat.Equivalence
open FloatLib.Floats.Formats.BinaryInterchange

def SupportedFormat (f : FloatFormat) : Prop :=
  f=.binary16 ∨ f=.bfloat16 ∨ f=.tf32 ∨ f=.e5m2 ∨ f=e4m3x
theorem SupportedFormat.decodes {f : FloatFormat} (h : SupportedFormat f) : DecodesLikeReference f := by
  rcases h with rfl|rfl|rfl|rfl|rfl
  iterate 4 exact DecodesLikeReference.of_isIEEE (by decide +kernel)
  exact e4m3x_decodesLikeReference

/-- The universal equivalence for the FP16, BF16, TF32, E5M2 and `e4m3x` input formats, for every
output width. -/
theorem supportedFormat_equivalence (p : TCModel) (hf : SupportedFormat p.format)
    (x : TensorCore.BlockInput (model p)) (D : TensorCore.F32) :
    Interface.tc p (inputPairs x) x.c.toNat =
        (TensorCore.evalBlock x).toOption.map (fun t => t.output.bits.toNat) ∧
    Interface.eft p (inputPairs x) x.c.toNat D.toNat =
        (TensorCore.tcEftEncoded x D).toOption.map encodedResult :=
  universal_equivalence p hf.decodes x D

theorem trace_related (t : Trace) (hb : ValidBlock t.block) (hw : t.bits < 2^32)
    (hv : TCFloat.value32 t.bits=some t.output) : ∃ s, TraceRel s t := by
  let D : TensorCore.F32 := BitVec.ofNat 32 t.bits
  have hD : D.toNat=t.bits := Nat.mod_eq_of_lt hw
  have hvs : TensorCore.value32 D=some t.output := by rw [← value32_eq,hD]; exact hv
  obtain ⟨d,_,hd,ho⟩ := TensorCore.finite32_of_value32 D t.output hvs
  exact ⟨⟨block t.block,d⟩,⟨rfl,by rw [hd,hD],ho,hb⟩⟩

theorem trace_evaluated {s : TensorCore.BlockTrace} {t : Trace} (h : TraceRel s t)
    (ht : t.block.evaluate=some t.bits) : TensorCore.evalPrepared s.block=.ok s := by
  rw [evaluate_eq t.block h.valid,← h.block_eq] at ht
  obtain ⟨bits,hbits,hval⟩ := Option.map_eq_some_iff.mp ht
  have heq : TensorCore.truncateMantissa32 t.block.model.outputMantissaBits bits = s.output.bits :=
    BitVec.eq_of_toNat_eq ((truncateMantissa32_toNat _ _).trans (hval.trans h.bits_eq.symm))
  have hd : TensorCore.finite32 s.output.bits=some s.output := by
    unfold TensorCore.finite32
    split
    · rename_i hd
      rw [s.output.valid] at hd
      contradiction
    · rename_i d hd
      have he : d=s.output.decoded := Option.some.inj (hd.symm.trans s.output.valid)
      subst d
      rfl
  have hw : s.block.model.outputMantissaBits = t.block.model.outputMantissaBits := by
    rw [h.block_eq]; rfl
  simp only [TensorCore.evalPrepared,hbits,hw,heq,hd]

/-- Error below terms × alignment quantum plus the output quantum (TC-EFT paper, Theorem III.1). -/
theorem floatlib_error_bound (t : Trace) (hb : ValidBlock t.block) (hw : t.bits<2^32)
    (hv : TCFloat.value32 t.bits=some t.output) (ht : t.block.evaluate=some t.bits)
    (hm : t.block.model.outputMantissaBits = 23) :
    |t.block.ideal-t.output| < (t.block.terms.length:Rat)*TCFloat.pow2 t.block.q +
      TCFloat.pow2 (outputUlpExponent t.bits) := by
  obtain ⟨s,hs⟩ := trace_related t hb hw hv
  have h := TensorCore.evalPrepared_error_bound (trace_evaluated hs ht)
    (by rw [hs.block_eq]; exact hm ▸ Nat.le_refl 23)
  simp only [abs_eq,hs.block_eq,ideal_eq _ hb,hs.output_eq,terms_eq,List.length_map,
    q_eq,pow2_eq,TensorCore.outputUlpExponent,hs.bits_eq] at h
  exact h

/-- Every low part is below the extraction quantum in magnitude (TC-EFT paper, Lemma IV.1). -/
theorem floatlib_lowPart_bound (t : Trace) (e : Rat) (he : e ∈ t.lowParts) :
    |e| < TCFloat.pow2 t.extractionExponent := by
  obtain ⟨x,_,rfl⟩ := List.mem_map.mp he
  exact truncGrid_error x.value t.extractionExponent

/-- The extraction grid is never finer than the alignment grid (TC-EFT paper, Lemma IV.2). -/
theorem floatlib_overlap_width (t : Trace) :
    0 ≤ t.extractionExponent-t.block.q ∧
      t.extractionExponent-t.block.q = max 0 (outputUlpExponent t.bits-t.block.q) := by
  unfold Trace.extractionExponent
  omega

/-- The accumulator is the retained sum plus the aligned low parts (TC-EFT paper, Lemma IV.3). -/
theorem floatlib_accumulator_eq_retained (t : Trace) :
    t.block.accumulator = t.retained + t.retainedLowParts.sum := by
  let τ := (t.extractionExponent-t.block.q).toNat
  have ht : t.extractionExponent=t.block.q+τ := by
    have := (floatlib_overlap_width t).1
    dsimp [τ]; omega
  have hsplit (x : Rat) : truncGrid x t.block.q = truncGrid x t.extractionExponent +
      truncGrid (x-truncGrid x t.extractionExponent) t.block.q := by
    rw [ht]
    exact TensorCore.truncGrid_split x t.block.q τ
  simp only [Block.accumulator,Block.aligned,Trace.retained,Trace.coarse,
    Trace.retainedLowParts,Trace.lowParts,List.map_map,Function.comp_def]
  have hm : (t.block.terms.map fun x => truncGrid x.value t.block.q) =
      t.block.terms.map (fun x => truncGrid x.value t.extractionExponent+
        truncGrid (x.value-truncGrid x.value t.extractionExponent) t.block.q) := by
    apply List.map_congr_left
    intro x _
    exact hsplit x.value
  rw [hm,List.sum_map_add]

/-- `D − H` is the aligned low parts minus the output residual (TC-EFT paper, Lemma IV.4). -/
theorem floatlib_overlap_eq_retained_sub_outputResidual (t : Trace) :
    t.overlap = t.retainedLowParts.sum-t.outputResidual := by
  have h := floatlib_accumulator_eq_retained t
  unfold Trace.overlap Trace.outputResidual
  linarith

theorem rtz_value_spec (x : Rat) (bits : Nat) (y : Rat)
    (hr : TCFloat.round32 .towardZero x=some bits) (hv : TCFloat.value32 bits=some y) :
    y=TensorCore.signedRounded .truncate x := by
  rw [round32_rtz_eq] at hr
  obtain ⟨b,hb,hbits⟩ := Option.map_eq_some_iff.mp hr
  rw [← hbits,value32_eq] at hv
  by_cases hz : x=0
  · subst x
    have h0 : TensorCore.round32 .truncate 0=some 0 := by decide +kernel
    rw [h0] at hb
    cases Option.some.inj hb
    have hz : TensorCore.value32 0=some 0 := by decide +kernel
    rw [hz] at hv
    have hy : y=0 := (Option.some.inj hv).symm
    rw [hy]
    decide +kernel
  · obtain ⟨b',hb',hv',_,_⟩ := TensorCore.round32_nonzero_spec .truncate x hz (TensorCore.round32_range hb)
    rw [hb] at hb'
    cases Option.some.inj hb'
    rw [hv] at hv'
    exact Option.some.inj hv'

theorem rtz_range (x : Rat) (b : Nat) (h : TCFloat.round32 .towardZero x=some b) :
    TensorCore.absQ x ≤ TensorCore.maxFinite32 := by
  rw [round32_rtz_eq] at h
  obtain ⟨b,hb,_⟩ := Option.map_eq_some_iff.mp h
  exact TensorCore.round32_range hb

/-- FloatLib RTZ outputs are monotone in the exact value. -/
theorem rtz_output_monotone (x y : Rat) (bx by' : Nat) (dx dy : Rat)
    (hx : TCFloat.round32 .towardZero x=some bx) (hy : TCFloat.round32 .towardZero y=some by')
    (hdx : TCFloat.value32 bx=some dx) (hdy : TCFloat.value32 by'=some dy) (hxy : x≤y) : dx≤dy := by
  rw [rtz_value_spec x bx dx hx hdx,rtz_value_spec y by' dy hy hdy]
  exact TensorCore.signedRounded_trunc_monotone x y hxy (rtz_range x bx hx) (rtz_range y by' hy)

/-- After changing C, the output rises iff its truncated accumulator does (TC-EFT paper, Eq. 6). -/
theorem floatlib_output_increase_iff (p : TCModel) (ps : List (Term×Term)) (c c' : Term)
    (bits bits' : Nat) (d d' : Rat) (hm : p.outputMantissaBits = 23)
    (h : (Block.mk p c ps).evaluate=some bits) (h' : (Block.mk p c' ps).evaluate=some bits')
    (hd : TCFloat.value32 bits=some d) (hd' : TCFloat.value32 bits'=some d') :
    (d<d' ↔ TensorCore.signedRounded .truncate (Block.mk p c ps).accumulator <
      TensorCore.signedRounded .truncate ((Block.mk p c ps).accumulator+
        TCFloat.flowback p ps c c'-TCFloat.accumulatorShift p ps c c')) := by
  rw [evaluate_fp32 (b := Block.mk p c ps) hm] at h
  rw [evaluate_fp32 (b := Block.mk p c' ps) hm] at h'
  rw [rtz_value_spec _ _ _ h hd,rtz_value_spec _ _ _ h' hd',TCFloat.perturbed_accumulator p ps c c']

theorem floatlib_flowback_necessary (p : TCModel) (ps : List (Term×Term)) (c c' : Term)
    (bits bits' : Nat) (d d' : Rat) (hm : p.outputMantissaBits = 23)
    (h : (Block.mk p c ps).evaluate=some bits) (h' : (Block.mk p c' ps).evaluate=some bits')
    (hd : TCFloat.value32 bits=some d) (hd' : TCFloat.value32 bits'=some d') (hi : d<d') :
    TCFloat.accumulatorShift p ps c c' < TCFloat.flowback p ps c c' := by
  rw [evaluate_fp32 (b := Block.mk p c ps) hm] at h
  rw [evaluate_fp32 (b := Block.mk p c' ps) hm] at h'
  by_contra hn
  have ha : (Block.mk p c' ps).accumulator ≤ (Block.mk p c ps).accumulator := by
    rw [TCFloat.perturbed_accumulator p ps c c']; linarith
  have hm := rtz_output_monotone _ _ _ _ _ _ h' h hd' hd ha
  linarith

theorem floatlib_flowback_sufficient (p : TCModel) (ps : List (Term×Term)) (c c' : Term)
    (bits bits' : Nat) (d d' : Rat) (hm : p.outputMantissaBits = 23)
    (h : (Block.mk p c ps).evaluate=some bits) (h' : (Block.mk p c' ps).evaluate=some bits')
    (hd : TCFloat.value32 bits=some d) (hd' : TCFloat.value32 bits'=some d')
    (ha : TensorCore.FiniteValue32 (Block.mk p c ps).accumulator)
    (ha' : TensorCore.FiniteValue32 (Block.mk p c' ps).accumulator)
    (hi : TCFloat.accumulatorShift p ps c c' < TCFloat.flowback p ps c c') : d<d' := by
  rw [evaluate_fp32 (b := Block.mk p c ps) hm] at h
  rw [evaluate_fp32 (b := Block.mk p c' ps) hm] at h'
  rw [rtz_value_spec _ _ _ h hd,rtz_value_spec _ _ _ h' hd',
    TensorCore.signedRounded_trunc_of_finite _ ha,TensorCore.signedRounded_trunc_of_finite _ ha',
    TCFloat.perturbed_accumulator p ps c c']
  linarith

def belowTerm (j : Nat) : Term :=
  ⟨FloatLib.Numerics.Dyadic.ofScaledInt ((16777216-j : Nat):Int) (-24),-1,23⟩

theorem belowTerm_project (j : Nat) : project (belowTerm j)=TensorCore.belowDecoded j :=
  project_term (TensorCore.belowDecoded j)

/-- Non-monotonicity over `C = 1 − j·2^-24`, for any p and K (TC-EFT paper, Theorem III.5). -/
theorem floatlib_nonmonotone_range (M : TCModel) (p K j : Nat) (a b : Term)
    (hp : M.padding=p) (hm : M.outputMantissaBits = 23) (ha : ValidTerm a) (hb : ValidTerm b)
    (hf : ∀ f ∈ M.eAlignMin, f≤ -1)
    (hv : (a.mul b).value=TCFloat.pow2 (-(24+(p:Int))))
    (hs : (a.mul b).exponent≤ -1) (hK : K<2^(24+p)) (hj : 1≤j) (hj' : j≤2^23) :
    ∃ bits y,
      (Block.mk M (belowTerm j) (List.replicate K (a,b))).evaluate=some bits ∧
      TCFloat.value32 bits=some y ∧
      (1<y ↔ (j+2)*2^p≤K) ∧
      (j*2^p≤K → y=1+((K-j*2^p)/2^(p+1):Nat)*TCFloat.pow2 (-23)) ∧
      y≤1+((K-2^p)/2^(p+1):Nat)*TCFloat.pow2 (-23) := by
  have hva : a.value=(project a).value := ha
  have hvb : b.value=(project b).value := hb
  have hvs : (TensorCore.denormalizedMul (project a) (project b)).value = TensorCore.pow2 (-(24+(p:Int))) := by
    rw [TensorCore.denormalizedProduct_value,← hva,← hvb,← TCFloat.mul_value,pow2_eq]
    exact hv
  obtain ⟨s,he,hi,hy,hu⟩ := TensorCore.nonmonotone_range (model M) p K j
    (project a) (project b) (by simp [model,hp,hm]) hf (by simp [model,hm]) hvs hs hK hj hj'
  let t : Block := ⟨M,belowTerm j,List.replicate K (a,b)⟩
  have ht : ValidBlock t := by
    constructor
    · change (term (TensorCore.belowDecoded j)).value = _
      rw [term_value,belowTerm_project]
    · intro ab hab
      have hab' : ab=(a,b) := List.eq_of_mem_replicate hab
      subst ab
      exact ⟨ha,hb⟩
  have hblock : block t=⟨model M,List.replicate K (project a,project b),TensorCore.belowDecoded j⟩ := by
    simp [t,block,List.map_replicate,belowTerm_project]
  have hout := TensorCore.evalPrepared_output he (by simp [model,hm])
  refine ⟨s.output.bits.toNat,s.output.value,?_,?_,?_,?_,?_⟩
  · change t.evaluate=_
    rw [evaluate_fp32 (b := t) hm, ← evaluate_fp32 (b := t) hm, evaluate_eq t ht,hblock,hout]
    simp [t, hm, truncateMantissa]
  · rw [value32_eq]
    simp [TensorCore.value32,s.output.valid,TensorCore.Finite32.value]
  · exact hi
  · simpa only [pow2_eq] using hy
  · simpa only [pow2_eq] using hu

/-- The source's finite FP32 values are exactly those passing the port's `representable` test. -/
theorem finiteValue32_iff_representable (x : Rat) :
    TensorCore.FiniteValue32 x ↔ TCFloat.representable x=true := by
  rw [representable_eq]
  constructor
  · intro hx
    obtain ⟨b,hb,hv⟩ := TensorCore.round32_exact_of_finite hx
    simp [TensorCore.representable32,hb,hv]
  · exact TensorCore.representable32_finite

private theorem sum_map_difference (xs : List Rat) (f g : Rat → Rat) :
    (xs.map fun x => f x-g x).sum=(xs.map f).sum-(xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons,List.sum_cons,ih]; ring

/-- The output rises only if flowback exceeds the shift (general form of Definition III.3). -/
theorem general_flowback_necessary (primary primary' : Rat) (others : List Rat) (q q' : Int)
    (bits bits' : Nat) (d d' : Rat)
    (h : TCFloat.round32 .towardZero
      (truncGrid primary q+(others.map fun x => truncGrid x q).sum)=some bits)
    (h' : TCFloat.round32 .towardZero
      (truncGrid primary' q'+(others.map fun x => truncGrid x q').sum)=some bits')
    (hd : TCFloat.value32 bits=some d) (hd' : TCFloat.value32 bits'=some d') (hi : d<d') :
    truncGrid primary q-truncGrid primary' q' <
      (others.map fun x => truncGrid x q'-truncGrid x q).sum := by
  rw [sum_map_difference]
  by_contra hn
  have hle : truncGrid primary' q'+(others.map fun x => truncGrid x q').sum ≤
      truncGrid primary q+(others.map fun x => truncGrid x q).sum := by linarith
  have hm := rtz_output_monotone _ _ _ _ _ _ h' h hd' hd hle
  linarith

theorem general_flowback_sufficient (primary primary' : Rat) (others : List Rat) (q q' : Int)
    (bits bits' : Nat) (d d' : Rat)
    (h : TCFloat.round32 .towardZero
      (truncGrid primary q+(others.map fun x => truncGrid x q).sum)=some bits)
    (h' : TCFloat.round32 .towardZero
      (truncGrid primary' q'+(others.map fun x => truncGrid x q').sum)=some bits')
    (hd : TCFloat.value32 bits=some d) (hd' : TCFloat.value32 bits'=some d')
    (ha : TCFloat.representable (truncGrid primary q+(others.map fun x => truncGrid x q).sum)=true)
    (ha' : TCFloat.representable (truncGrid primary' q'+(others.map fun x => truncGrid x q').sum)=true)
    (hi : truncGrid primary q-truncGrid primary' q' <
      (others.map fun x => truncGrid x q'-truncGrid x q).sum) : d<d' := by
  rw [rtz_value_spec _ _ _ h hd,rtz_value_spec _ _ _ h' hd',
    TensorCore.signedRounded_trunc_of_finite _ ((finiteValue32_iff_representable _).mpr ha),
    TensorCore.signedRounded_trunc_of_finite _ ((finiteValue32_iff_representable _).mpr ha')]
  rw [sum_map_difference] at hi
  linarith

end TCFloat.Equivalence
