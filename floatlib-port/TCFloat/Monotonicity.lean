import TCFloat.DirectedRounding

/-! Parameterized TC nonmonotonicity. -/
namespace TCFloat
set_option maxRecDepth 2048
set_option maxHeartbeats 800000

private theorem pow2_pos' (e : Int) : 0 < pow2 e := zpow_pos (by norm_num) e
private theorem pow2_add' (e f : Int) : pow2 (e+f) = pow2 e*pow2 f :=
  zpow_add₀ (by norm_num) _ _
private theorem pow2_div' (e f : Int) : pow2 e / pow2 f = pow2 (e-f) :=
  (zpow_sub₀ (by norm_num) _ _).symm

/-- Truncating an integer multiple of the alignment quantum preserves it exactly. -/
theorem truncGrid_integer (z : Int) (e : Int) :
    truncGrid ((z : ℚ)*pow2 e) e = (z : ℚ)*pow2 e := by
  have hp := (pow2_pos' e).ne'
  unfold truncGrid truncCoeff
  split_ifs
  · simp only [neg_div, mul_div_cancel_right₀ _ hp, ← Int.cast_neg, Int.floor_intCast, neg_neg]
  · simp only [mul_div_cancel_right₀ _ hp, Int.floor_intCast]

private theorem alignment_replicate (t : Term) (k : Nat) :
    maxTermExp (List.replicate k t) =
      if k = 0 ∨ t.dyadic.significand = 0 then none else some t.exponent := by
  induction k with
  | zero => simp [maxTermExp]
  | succ k ih =>
    simp only [List.replicate_succ, maxTermExp, ih]
    by_cases hz : t.dyadic.significand = 0
    · simp [hz]
    · by_cases hk : k = 0 <;> simp [hz,hk]

/-- A leading nonzero C selects eta if each repeated product's exponent is no larger. -/
theorem construction_alignExp (M : TCModel) (K : Nat) (a b c : Term)
    (hc : c.dyadic.significand ≠ 0) (hs : (a.mul b).exponent ≤ c.exponent)
    (hf : ∀ f ∈ M.eAlignMin, f ≤ c.exponent) :
    Block.alignExp ⟨M,c,List.replicate K (a,b)⟩ = some c.exponent := by
  have ha : maxTermExp (c :: List.replicate K (a.mul b)) = some c.exponent := by
    simp only [maxTermExp, alignment_replicate, ite_eq_right hc]
    split_ifs <;> simp [max_eq_left hs]
  simp only [Block.alignExp, Block.terms, List.map_replicate, ha, Option.map_some]
  cases hp : M.eAlignMin with
  | none => simp
  | some f =>
    have h := hf f (by simp [hp])
    simp [max_eq_left h]

def oneTerm : Term := ⟨⟨false,8388608,-23⟩,0,23⟩
def belowOneTerm : Term := ⟨⟨false,16777215,-24⟩,-1,23⟩

theorem oneTerm_value : oneTerm.value = 1 := by decide +kernel
theorem belowOneTerm_value : belowOneTerm.value = 1-pow2 (-24) := by decide +kernel

/-- With C=1 all products of the family fall below the alignment quantum. -/
theorem construction_accumulator_one (M : TCModel) (p K : Nat) (a b : Term)
    (hp : M.neab = p) (hf : ∀ f ∈ M.eAlignMin, f ≤ -1)
    (hv : (a.mul b).value = pow2 (-(24+(p:Int)))) (hs : (a.mul b).exponent ≤ -1) :
    Block.accumulator ⟨M,oneTerm,List.replicate K (a,b)⟩ = 1 := by
  have he := construction_alignExp M K a b oneTerm (by decide) (by exact le_trans hs (by decide))
    (by intro f h; exact le_trans (hf f h) (by decide))
  have hq : Block.q ⟨M,oneTerm,List.replicate K (a,b)⟩ = -(23+(p:Int)) := by
    unfold Block.q
    rw [he]
    change 0 - ((23+M.neab:Nat):Int) = _
    rw [hp]
    omega
  have hone : truncGrid 1 (-(23+(p:Int))) = 1 := by
    have hpow : ((2^(23+p):Nat):ℚ)*pow2 (-(23+(p:Int))) = 1 := by
      simp [pow2, ← zpow_natCast, ← zpow_add₀ (by norm_num : (2:ℚ) ≠ 0)]
    have h := truncGrid_integer ((2^(23+p):Nat):Int) (-(23+(p:Int)))
    simpa only [Int.cast_natCast, hpow] using h
  have hterm : truncGrid (a.mul b).value (-(23+(p:Int))) = 0 := by
    rw [hv]
    simp only [truncGrid, truncCoeff, not_lt.mpr (pow2_pos' _).le, ite_false, pow2_div']
    rw [show (-(24+(p:Int)))-(-(23+(p:Int))) = -1 by omega]
    have hhalf : ⌊pow2 (-1)⌋ = 0 := by decide +kernel
    simp [hhalf]
  simp only [Block.accumulator, Block.aligned, Block.terms, List.map_cons, List.map_replicate,
    List.sum_cons, List.sum_replicate, hq, oneTerm_value, hone, hterm, nsmul_zero, add_zero]

/-- Lowering C by one FP32 step exposes all K product contributions. -/
theorem construction_accumulator_below (M : TCModel) (p K : Nat) (a b : Term)
    (hp : M.neab = p) (hf : ∀ f ∈ M.eAlignMin, f ≤ -1)
    (hv : (a.mul b).value = pow2 (-(24+(p:Int)))) (hs : (a.mul b).exponent ≤ -1) :
    Block.accumulator ⟨M,belowOneTerm,List.replicate K (a,b)⟩ =
      1-pow2 (-24)+(K:ℚ)*pow2 (-(24+(p:Int))) := by
  have he := construction_alignExp M K a b belowOneTerm (by decide) hs hf
  have hq : Block.q ⟨M,belowOneTerm,List.replicate K (a,b)⟩ = -(24+(p:Int)) := by
    unfold Block.q
    rw [he]
    change -1 - ((23+M.neab:Nat):Int) = _
    rw [hp]
    omega
  have hcval : belowOneTerm.value = ((16777215*2^p:Nat):ℚ)*pow2 (-(24+(p:Int))) := by
    have hpow : ((2^p:Nat):ℚ)*pow2 (-(24+(p:Int))) = pow2 (-24) := by
      rw [Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast]
      change pow2 (p:Int)*pow2 (-(24+(p:Int))) = _
      rw [← pow2_add']
      congr 1
      omega
    rw [Nat.cast_mul, mul_assoc, hpow]
    decide +kernel
  have hc : truncGrid belowOneTerm.value (-(24+(p:Int))) = belowOneTerm.value := by
    rw [hcval]
    simpa only [Int.cast_natCast] using truncGrid_integer ((16777215*2^p:Nat):Int) (-(24+(p:Int)))
  have ht : truncGrid (a.mul b).value (-(24+(p:Int))) = pow2 (-(24+(p:Int))) := by
    rw [hv]
    simpa using truncGrid_integer 1 (-(24+(p:Int)))
  simp only [Block.accumulator, Block.aligned, Block.terms, List.map_cons, List.map_replicate,
    List.sum_cons, List.sum_replicate, hq, hc, ht, nsmul_eq_mul]
  rw [belowOneTerm_value]

private theorem truncGrid_le_nonneg (x : ℚ) (e : Int) (hx : 0 ≤ x) : truncGrid x e ≤ x := by
  simp only [truncGrid, truncCoeff, not_lt.mpr hx, ite_false]
  exact (le_div_iff₀ (pow2_pos' e)).mp (Int.floor_le _)

private theorem truncGrid_above_one (x : ℚ) (hx : 0 ≤ x) :
    1 < truncGrid x (-23) ↔ 1+pow2 (-23) ≤ x := by
  simp only [truncGrid, truncCoeff, not_lt.mpr hx, ite_false]
  have hq : pow2 (-23) = (1:ℚ)/8388608 := by decide +kernel
  rw [hq]
  have hstep (m : Int) : (1:ℚ) < (m:ℚ)*(1/8388608) ↔ (8388608:Int) < m := by
    constructor <;> intro h
    · have hh : (8388608:ℚ) < (m:ℚ) := by linarith
      exact_mod_cast hh
    · have hh : (8388608:ℚ) < (m:ℚ) := by exact_mod_cast h
      linarith
  rw [hstep, Int.lt_iff_add_one_le, Int.le_floor]
  norm_num
  constructor <;> intro h <;> linarith

/-- The executable RTZ converter crosses 1 at the next FP32 number above 1. -/
theorem round32_rtz_above_one (x : ℚ) (hx : (1:ℚ)/2 ≤ x) (hx2 : x < 2) :
    ∃ bits y, round32 .towardZero x = some bits ∧ value32 bits = some y ∧
      (1 < y ↔ 1+pow2 (-23) ≤ x) := by
  have hr : |x| ≤ maxFinite32 := by
    rw [abs_of_nonneg (by linarith)]
    have : (2:ℚ) ≤ maxFinite32 := by decide +kernel
    linarith
  by_cases h1 : 1 ≤ x
  · obtain ⟨bits,y,hb,hy,hv⟩ := round32_rtz_normal x 0 (by omega) (by omega)
      (by simpa [pow2] using h1) (by simpa [pow2] using hx2) hr
    exact ⟨bits,y,hb,hy,by rw [hv]; exact truncGrid_above_one x (by linarith)⟩
  · obtain ⟨bits,y,hb,hy,hv⟩ := round32_rtz_normal x (-1) (by omega) (by omega)
      (by norm_num [pow2]; exact hx) (by norm_num [pow2]; linarith) hr
    refine ⟨bits,y,hb,hy,?_⟩
    have hle := truncGrid_le_nonneg x (-24) (by linarith)
    have hpos := pow2_pos' (-23)
    norm_num at hv
    rw [hv]
    constructor <;> intro h <;> linarith

/-- General TC-EFT nonmonotonicity threshold (Theorem III.4), for all natural p and K. -/
theorem nonmonotone_perturbation (M : TCModel) (p K : Nat) (a b : Term)
    (hp : M.neab = p) (hf : ∀ f ∈ M.eAlignMin, f ≤ -1)
    (hv : (a.mul b).value = pow2 (-(24+(p:Int)))) (hs : (a.mul b).exponent ≤ -1)
    (hK : K < 2^(24+p)) :
    ∃ bits y,
      Block.evaluate ⟨M,oneTerm,List.replicate K (a,b)⟩ = some 0x3f800000 ∧
      Block.evaluate ⟨M,belowOneTerm,List.replicate K (a,b)⟩ = some bits ∧
      value32 bits = some y ∧ (1 < y ↔ 3*2^p ≤ K) := by
  have ha := construction_accumulator_one M p K a b hp hf hv hs
  have hb := construction_accumulator_below M p K a b hp hf hv hs
  let q := pow2 (-(24+(p:Int)))
  let A : ℚ := 1-pow2 (-24)+(K:ℚ)*q
  have hq : 0 < q := pow2_pos' _
  have hpq : ((2^p:Nat):ℚ)*q = pow2 (-24) := by
    change ((2^p:Nat):ℚ)*pow2 (-(24+(p:Int))) = _
    rw [Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast]
    change pow2 (p:Int)*pow2 (-(24+(p:Int))) = _
    rw [← pow2_add']
    congr 1
    omega
  have hbig : ((2^(24+p):Nat):ℚ)*q = 1 := by
    change ((2^(24+p):Nat):ℚ)*pow2 (-(24+(p:Int))) = _
    simp [pow2, ← zpow_natCast, ← zpow_add₀ (by norm_num : (2:ℚ) ≠ 0)]
  have hδ : pow2 (-24) = (1:ℚ)/16777216 := by decide +kernel
  have hAlo : (1:ℚ)/2 ≤ A := by
    have := mul_nonneg (Nat.cast_nonneg K : (0:ℚ) ≤ K) hq.le
    dsimp [A]
    rw [hδ]
    linarith
  have hAhi : A < 2 := by
    have hk : (K:ℚ) < (2^(24+p):Nat) := by exact_mod_cast hK
    have hprod := mul_lt_mul_of_pos_right hk hq
    rw [hbig] at hprod
    dsimp [A]
    rw [hδ]
    linarith
  obtain ⟨bits,y,hr,hy,hcross⟩ := round32_rtz_above_one A hAlo hAhi
  refine ⟨bits,y,?_,?_,hy,?_⟩
  · rw [Block.evaluate, ha]
    decide +kernel
  · simpa only [Block.evaluate, hb, A, q] using hr
  · rw [hcross]
    have hdouble : pow2 (-23) = 2*pow2 (-24) := by decide +kernel
    dsimp only [A]
    rw [hdouble, ← hpq]
    rw [← mul_assoc]
    change 1+2*((2^p:Nat):ℚ)*q ≤ 1-((2^p:Nat):ℚ)*q+(K:ℚ)*q ↔ _
    have he : (1+2*((2^p:Nat):ℚ)*q ≤ 1-((2^p:Nat):ℚ)*q+(K:ℚ)*q) ↔
        (3*((2^p:Nat):ℚ))*q ≤ (K:ℚ)*q := by constructor <;> intro h <;> linarith
    rw [he, mul_le_mul_iff_left₀ hq]
    exact_mod_cast (Iff.rfl : 3*2^p ≤ K ↔ 3*2^p ≤ K)

/-- The same monotonicity property as the source: fix products and decrease C. -/
def MonotoneInAccumulator (M : TCModel) (products : List (Term × Term)) : Prop :=
  ∀ (c c' : Term) (bits bits' : Nat) (y y' : ℚ),
    Block.evaluate ⟨M,c,products⟩ = some bits →
    Block.evaluate ⟨M,c',products⟩ = some bits' →
    value32 bits = some y → value32 bits' = some y' →
    c'.value < c.value → y' ≤ y

/-- An explicit failure of monotonicity whenever the general family's threshold is met. -/
theorem construction_not_monotone (M : TCModel) (p K : Nat) (a b : Term)
    (hp : M.neab = p) (hf : ∀ f ∈ M.eAlignMin, f ≤ -1)
    (hv : (a.mul b).value = pow2 (-(24+(p:Int)))) (hs : (a.mul b).exponent ≤ -1)
    (hK : K < 2^(24+p)) (hthreshold : 3*2^p ≤ K) :
    ¬ MonotoneInAccumulator M (List.replicate K (a,b)) := by
  obtain ⟨bits,y,h1,h2,hy,hiff⟩ := nonmonotone_perturbation M p K a b hp hf hv hs hK
  intro hm
  have hle := hm oneTerm belowOneTerm 0x3f800000 bits 1 y h1 h2 (by decide +kernel) hy
    (by rw [oneTerm_value, belowOneTerm_value]; exact sub_lt_self 1 (pow2_pos' _))
  exact (not_le_of_gt (hiff.mpr hthreshold)) hle

private theorem prepare_replicate (M : TCModel) (K aw bw c : Nat) (a b d : Term)
    (hk : M.nfma = K)
    (ha : decode M.format aw = some a) (hb : decode M.format bw = some b)
    (hc : decode .binary32 c = some d) :
    prepare M (List.replicate K (aw,bw)) c = some ⟨M,d,List.replicate K (a,b)⟩ := by
  have hm : (List.replicate K (aw,bw)).mapM (fun (u,v) => do
      return (← decode M.format u, ← decode M.format v)) = some (List.replicate K (a,b)) := by
    clear hk
    induction K with
    | zero => rfl
    | succ k ih =>
      simp at ih
      simp [List.replicate_succ, List.mapM_cons, ha, hb, ih]
  simp at hm
  simp [prepare, hk, hc, hm]

/-- The parameterized theorem at the actual encoded FP16 entry point, with arbitrary K/p. -/
theorem nonmonotone_encoded (K p : Nat) (eAlignMin : Option Int)
    (hf : ∀ f ∈ eAlignMin, f ≤ -1) (aw bw : Nat) (a b : Term)
    (ha : decode .binary16 aw = some a) (hb : decode .binary16 bw = some b)
    (hv : (a.mul b).value = pow2 (-(24+(p:Int)))) (hs : (a.mul b).exponent ≤ -1)
    (hK : K < 2^(24+p)) :
    ∃ bits y,
      evalWords (fp16 K p eAlignMin) (List.replicate K (aw,bw)) 0x3f800000 = some 0x3f800000 ∧
      evalWords (fp16 K p eAlignMin) (List.replicate K (aw,bw)) 0x3f7fffff = some bits ∧
      value32 bits = some y ∧ (1 < y ↔ 3*2^p ≤ K) := by
  have h1 : decode .binary32 0x3f800000 = some oneTerm := by rfl
  have h2 : decode .binary32 0x3f7fffff = some belowOneTerm := by rfl
  have hp1 := prepare_replicate (fp16 K p eAlignMin) K aw bw 0x3f800000 a b oneTerm rfl ha hb h1
  have hp2 := prepare_replicate (fp16 K p eAlignMin) K aw bw 0x3f7fffff a b belowOneTerm rfl ha hb h2
  obtain ⟨bits,y,he1,he2,hy,hi⟩ := nonmonotone_perturbation (fp16 K p eAlignMin) p K a b rfl hf hv hs hK
  exact ⟨bits,y,by simpa [evalWords, hp1] using he1,
    by simpa [evalWords, hp2] using he2,hy,hi⟩

end TCFloat
