import OzakiTC.Exactness

/-! # The Tensor Core as an Ozaki engine

`tcMultiplier p` evaluates an integer dot product on the Tensor Core model of profile `p`: it encodes
each integer exactly as an operand word (fp16, bf16, or tf32 by profile), pads the product list
with zero words to whole groups of `K`, and chains the groups through `runBlocks` from `c = +0`.

`tcMultiplier_exactOn`: under the conditions of `IntExact` and when the operand format holds every
`b`-bit integer, the engine is exact on `b`-bit vectors whose products total at most `2^24` in
magnitude. The concrete instances for the eight GPU paths of `TensorCore` are in
`OzakiTC.Models`. -/

open TensorCore

namespace Ozaki.TC

/-! ## Exact integer encoding -/

/-- Encode an integer exactly as a word of `f`, or fail. -/
def encodeInt (f : Format) (z : ℤ) : Option (BitVec f.width) :=
  match roundBinary f .nearestEven (z : ℚ) with
  | some w => if binaryValue f w = some (z : ℚ) then some w else none
  | none => none

/-- The format holds every integer of magnitude at most `2^(m+1)`, where `m` is its number of
stored mantissa bits. -/
theorem int_finiteValue (f : Format) (hemin : f.emin ≤ f.mantissaBits)
    (hemax : (f.mantissaBits : ℤ) + 1 ≤ f.emax) {z : ℤ} (hz : z.natAbs ≤ 2 ^ (f.mantissaBits + 1)) :
    f.FiniteValue (z : ℚ) := by
  by_cases hlt : z.natAbs < 2 ^ (f.mantissaBits + 1)
  · exact ⟨z, f.mantissaBits, hemin, by omega, hlt, by rw [Int.sub_self, pow2_zero, Rat.mul_one]⟩
  · have hz2 : z = (z / 2) * 2 := by
      have : z.natAbs = 2 ^ (f.mantissaBits + 1) := by omega
      have h2 : 2 ^ (f.mantissaBits + 1) = 2 * 2 ^ f.mantissaBits := by rw [Nat.pow_succ]; omega
      omega
    refine ⟨z / 2, f.mantissaBits + 1, by omega, hemax, ?_, ?_⟩
    · have h2 : 2 ^ (f.mantissaBits + 1) = 2 * 2 ^ f.mantissaBits := by rw [Nat.pow_succ]; omega
      have : (2 : ℕ) ^ f.mantissaBits ≥ 1 := Nat.one_le_two_pow
      omega
    · have he : (f.mantissaBits : ℤ) + 1 - f.mantissaBits = 1 := by omega
      rw [he, pow2_one]
      conv => lhs; rw [hz2]
      rw [Rat.intCast_mul, Rat.intCast_ofNat]

theorem int_le_maxFinite (f : Format) (hemax : (f.mantissaBits : ℤ) + 1 ≤ f.emax) {z : ℤ}
    (hz : z.natAbs ≤ 2 ^ (f.mantissaBits + 1)) : absQ (z : ℚ) ≤ f.maxFinite := by
  rw [absQ_eq, abs_intCast]
  unfold Format.maxFinite
  have hN : 2 ≤ 2 ^ (f.mantissaBits + 1) := by
    have : (2 : ℕ) ^ f.mantissaBits ≥ 1 := Nat.one_le_two_pow
    rw [Nat.pow_succ]; omega
  have hp : (2 : ℚ) ≤ pow2 (f.emax - f.mantissaBits) := by
    have := pow2_le_of_le (show (1 : ℤ) ≤ f.emax - f.mantissaBits by omega)
    rwa [pow2_one] at this
  have hz' : ((z.natAbs : ℕ) : ℚ) ≤ ((2 ^ (f.mantissaBits + 1) : ℕ) : ℚ) :=
    Rat.natCast_le_natCast.mpr hz
  have hsub : (((2 ^ (f.mantissaBits + 1) - 1 : ℕ)) : ℚ) * 2 ≥ ((2 ^ (f.mantissaBits + 1) : ℕ) : ℚ) := by
    have : (2 ^ (f.mantissaBits + 1) - 1) * 2 ≥ 2 ^ (f.mantissaBits + 1) := by omega
    have := Rat.natCast_le_natCast.mpr this
    rwa [Rat.natCast_mul] at this
  have hnn : (0 : ℚ) ≤ ((2 ^ (f.mantissaBits + 1) - 1 : ℕ) : ℚ) := Rat.natCast_nonneg
  have := Rat.mul_le_mul_of_nonneg_left hp hnn
  grind

/-- An integer that the format holds is encoded exactly. -/
theorem encodeInt_spec {f : Format} (hf : f.WellFormed) (hemin : f.emin ≤ f.mantissaBits)
    (hemax : (f.mantissaBits : ℤ) + 1 ≤ f.emax) {z : ℤ}
    (hz : z.natAbs ≤ 2 ^ (f.mantissaBits + 1)) :
    ∃ w, encodeInt f z = some w ∧ ∃ d, (classify f w).finite = some d ∧ d.value = z := by
  have hfin := int_finiteValue f hemin hemax hz
  obtain ⟨w, hw, d, hd, hnear, _⟩ := roundBinary_nearestEven_correct f hf (z : ℚ)
    (int_le_maxFinite f hemax hz)
  have hdz : d = z := by
    have h := hnear z hfin
    have h0 : absQ ((z : ℚ) - z) = 0 := by rw [show (z : ℚ) - z = 0 by grind]; rfl
    rw [h0] at h
    have := (absQ_le_iff _ _).mp h
    grind
  subst hdz
  refine ⟨w, ?_, ?_⟩
  · unfold encodeInt; rw [hw]; simp [hd]
  · unfold binaryValue at hd
    cases hc : (classify f w).finite with
    | none => simp [hc] at hd
    | some dd => simp only [hc, Option.map_some, Option.some.injEq] at hd; exact ⟨dd, rfl, hd⟩

/-- The zero word decodes to zero. -/
theorem decode_zero_word (f : Format) (hf : f.WellFormed) :
    (classify f (0 : BitVec f.width)).finite = some ⟨0, 0, 0⟩ := by
  have hE : 2 ≤ 2 ^ f.exponentBits := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 1 ≤ f.exponentBits by
      have := hf.2; omega)
    simpa using this
  have h0 : (0 : BitVec f.width).toNat = 0 := by simp
  unfold classify classifyNat
  rw [h0]
  simp only [Nat.zero_mod, Nat.zero_div]
  rw [if_neg (by omega)]
  simp only [if_true]
  rfl

/-! ## Grouping into blocks -/

/-- `m` groups of `n`: every group has `n` elements. -/
theorem chunks_length_mem (n : ℕ) : ∀ (m : ℕ) (xs : List α), xs.length = m * n →
    ∀ g ∈ chunks n m xs, g.length = n
  | 0, _, _ => by simp [chunks]
  | m + 1, xs, h => by
    intro g hg
    simp only [chunks, List.mem_cons] at hg
    rcases hg with rfl | hg
    · rw [List.length_take]; rw [Nat.succ_mul] at h; omega
    · exact chunks_length_mem n m (xs.drop n) (by rw [List.length_drop, h, Nat.succ_mul]; omega) g hg

/-- Number of groups of `K` that hold `L` products. -/
def groupCount (K L : ℕ) : ℕ := (L + K - 1) / K

theorem groupCount_spec {K : ℕ} (hK : 0 < K) (L : ℕ) : L ≤ groupCount K L * K := by
  unfold groupCount
  have h := Nat.div_add_mod (L + K - 1) K
  have h2 := Nat.mod_lt (L + K - 1) hK
  rw [Nat.mul_comm] at h
  omega

/-- Pad with `pad` to whole groups of `K`, and split into groups. -/
def groupsOf (K : ℕ) (pad : α) (ps : List α) : List (List α) :=
  chunks K (groupCount K ps.length)
    (ps ++ List.replicate (groupCount K ps.length * K - ps.length) pad)

theorem groupsOf_spec {K : ℕ} (hK : 0 < K) (pad : α) (ps : List α) :
    (∀ g ∈ groupsOf K pad ps, g.length = K) ∧
      (groupsOf K pad ps).flatten =
        ps ++ List.replicate (groupCount K ps.length * K - ps.length) pad := by
  have hlen : (ps ++ List.replicate (groupCount K ps.length * K - ps.length) pad).length =
      groupCount K ps.length * K := by
    have := groupCount_spec hK ps.length
    simp only [List.length_append, List.length_replicate]; omega
  exact ⟨chunks_length_mem K _ _ hlen, chunks_flatten K _ _ hlen⟩

/-! ## The engine -/

/-- **The Tensor Core as an Ozaki engine.** Encode the integers exactly, pad with zero words to
whole groups of `K` products, run the chained blocks from `c = +0`, and return the value. -/
def tcMultiplier (p : Model) : MatrixMultiplier := fun x y => do
  let ax ← x.mapM (encodeInt p.input)
  let ay ← y.mapM (encodeInt p.input)
  match runBlocks p 0 (groupsOf p.nfma (0, 0) (List.zip ax ay)) with
  | .ok ts => some (runValue 0 ts)
  | .error _ => none

/-- The operand format holds every `b`-bit integer and is a well-formed binary format. -/
structure HoldsInts (p : Model) (b : ℕ) : Prop where
  wellFormed : p.input.WellFormed
  bits : b ≤ p.input.mantissaBits + 1
  emin : p.input.emin ≤ p.input.mantissaBits
  emax : (p.input.mantissaBits : ℤ) + 1 ≤ p.input.emax

theorem dotZ_eq_zip_sum (x y : List ℤ) :
    ((dotZ x y : ℤ) : ℚ) = ((List.zip x y).map fun q => (q.1 : ℚ) * q.2).sum := by
  induction x generalizing y with
  | nil => simp
  | cons a x ih =>
    cases y with
    | nil => simp
    | cons b y => simp [ih, Rat.intCast_add, Rat.intCast_mul]

theorem dotAbs_eq_zip_sum (x y : List ℤ) :
    ((dotAbs x y : ℕ) : ℚ) = ((List.zip x y).map fun q => Rat.abs ((q.1 : ℚ) * q.2)).sum := by
  induction x generalizing y with
  | nil => simp
  | cons a x ih =>
    cases y with
    | nil => simp
    | cons b y =>
      simp only [dotAbs_cons, List.zip_cons_cons, List.map_cons, List.sum_cons, Rat.natCast_add, ih]
      rw [← Rat.intCast_mul, abs_intCast]

theorem wordDotAbs_replicate_zero (p : Model) (hf : p.input.WellFormed) (n : ℕ) :
    wordDotAbs p (List.replicate n (0, 0)) = 0 ∧ wordProducts p (List.replicate n (0, 0)) = 0 := by
  have hz : wordValue p 0 = 0 := by
    unfold wordValue decodeD Model.decode
    rw [decode_zero_word p.input hf]; simp [Decoded.value]
  induction n with
  | zero => simp [wordDotAbs, wordProducts]
  | succ n ih =>
    simp only [wordDotAbs, wordProducts, List.replicate_succ, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih.1, ih.2, hz, Rat.zero_mul, abs_zero]
    grind

/-- **Exact engine.** Under `IntExact` and `HoldsInts`, the Tensor Core engine is exact on `b`-bit
integer vectors whose products total at most `2^24` in magnitude. -/
theorem tcMultiplier_exactOn {p : Model} {b : ℕ} (hp : IntExact p b) (hh : HoldsInts p b)
    (hK : 0 < p.nfma) : (tcMultiplier p).ExactOn b (2 ^ 24) := by
  intro x y hlen hx hy hbound
  -- every entry is encoded exactly
  have henc : ∀ z : ℤ, z.natAbs ≤ 2 ^ b → ∃ w, encodeInt p.input z = some w ∧
      (p.decode w).isSome ∧ wordValue p w = z := by
    intro z hz
    obtain ⟨w, hw, d, hd, hv⟩ := encodeInt_spec hh.wellFormed hh.emin hh.emax
      (Nat.le_trans hz (Nat.pow_le_pow_right (by decide) hh.bits))
    refine ⟨w, hw, by simp [Model.decode, hd], ?_⟩
    unfold wordValue decodeD Model.decode; rw [hd]; exact hv
  let E : ℤ → p.Word := fun z => (encodeInt p.input z).getD 0
  have hE : ∀ z : ℤ, z.natAbs ≤ 2 ^ b → encodeInt p.input z = some (E z) ∧
      IntWord p b (E z) ∧ wordValue p (E z) = z := by
    intro z hz
    obtain ⟨w, hw, hs, hv⟩ := henc z hz
    have : E z = w := by simp [E, hw]
    rw [this]; exact ⟨hw, ⟨hs, z, hv, hz⟩, hv⟩
  have hmx : x.mapM (encodeInt p.input) = some (x.map E) :=
    mapM_eq_some_map fun z hz => (hE z (hx z hz)).1
  have hmy : y.mapM (encodeInt p.input) = some (y.map E) :=
    mapM_eq_some_map fun z hz => (hE z (hy z hz)).1
  have hzip : List.zip (x.map E) (y.map E) = (List.zip x y).map (Prod.map E E) := List.zip_map
  have hz0 : IntWord p b (0 : p.Word) := by
    refine ⟨by rw [Model.decode, decode_zero_word p.input hh.wellFormed]; rfl, 0, ?_, by simp⟩
    unfold wordValue decodeD Model.decode; rw [decode_zero_word p.input hh.wellFormed]
    simp [Decoded.value]
  obtain ⟨hglen, hflat⟩ := groupsOf_spec hK ((0 : p.Word), (0 : p.Word))
    ((List.zip x y).map (Prod.map E E))
  generalize hpad : groupCount p.nfma ((List.zip x y).map (Prod.map E E)).length * p.nfma -
    ((List.zip x y).map (Prod.map E E)).length = n at hflat
  have hzw := wordDotAbs_replicate_zero p hh.wellFormed n
  -- values and budget of the encoded pairs
  have hvals : ∀ q ∈ List.zip x y, wordValue p (E q.1) * wordValue p (E q.2) = (q.1 : ℚ) * q.2 := by
    intro q hq
    have := List.of_mem_zip hq
    rw [(hE q.1 (hx _ this.1)).2.2, (hE q.2 (hy _ this.2)).2.2]
  have hprod : wordProducts p ((List.zip x y).map (Prod.map E E)) = (dotZ x y : ℚ) := by
    unfold wordProducts; rw [List.map_map, dotZ_eq_zip_sum]
    exact congrArg List.sum (List.map_congr_left hvals)
  have hbud : wordDotAbs p ((List.zip x y).map (Prod.map E E)) = (dotAbs x y : ℚ) := by
    unfold wordDotAbs; rw [List.map_map, dotAbs_eq_zip_sum]
    exact congrArg List.sum (List.map_congr_left fun q hq => by
      simp only [Function.comp_def, Prod.map]; rw [hvals q hq])
  obtain ⟨ts, hts, hval⟩ := runBlocks_int hp (groupsOf p.nfma (0, 0)
    ((List.zip x y).map (Prod.map E E))) 0 0 (by decide +kernel)
    (fun g hg => ⟨hglen g hg, fun q hq => by
      have hq' : q ∈ (groupsOf p.nfma (0, 0) ((List.zip x y).map (Prod.map E E))).flatten :=
        List.mem_flatten.mpr ⟨g, hg, hq⟩
      rw [hflat] at hq'
      rcases List.mem_append.mp hq' with hq' | hq'
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq'
        have := List.of_mem_zip hr
        exact ⟨(hE r.1 (hx _ this.1)).2.1, (hE r.2 (hy _ this.2)).2.1⟩
      · rw [(List.mem_replicate.mp hq').2]; exact ⟨hz0, hz0⟩⟩)
    (by
      rw [hflat, wordDotAbs_append, hzw.1, hbud, Rat.intCast_zero, abs_zero]
      have : ((dotAbs x y : ℕ) : ℚ) ≤ ((2 ^ 24 : ℕ) : ℚ) := Rat.natCast_le_natCast.mpr hbound
      rw [← two_pow_natCast] at this
      grind)
  unfold tcMultiplier
  simp only [hmx, hmy, Option.bind_eq_bind, Option.bind_some, hzip, hts]
  rw [hval, hflat, wordProducts_append, hzw.2, hprod, Rat.intCast_zero]
  congr 1; grind

end Ozaki.TC
