import MMAlgebra.Schedule
import MMAlgebraMC.Exact
import MMAlgebraMC.Pinned
import OzakiMC

/-! # Every schedule is an exact matrix multiplier (matrix-core model)

`scheduleMultiplier P S` runs any reduction schedule `S` on the AMD matrix-core model;
`scheduleMultiplier_exactOn` shows that on every exact configuration (SFMA, CDNA 1, CDNA 2, and
CDNA 3 fp16 and bf16) every schedule is exact on `b`-bit integers whose products total at most
`2^24`; on CDNA 2 that bound also covers every pairwise sum inside a block. So Ozaki-I and Ozaki-II
return the same bits under every schedule (`ozaki1_schedules_agree`, `ozaki2_schedules_agree`),
and their correctly rounded versions return the correctly rounded `x · y`
(`ozaki1CR_every_schedule`, `ozaki2CR_every_schedule`).

The three ways to make the result schedule-independent, as on the Tensor Core side: the exact
region (`scheduleFree_exact`), pinning on CDNA 3 (`scheduleFree_pinned`), and correct rounding
(`scheduleFree_correctlyRounded`). -/

open MatrixCore Ozaki Ozaki.MC

namespace MMAlgebra.MC

/-- The matrix multiplier that encodes two integer vectors as operand words and evaluates the
schedule's term for their length on the matrix-core model, from `c = 0`. -/
def scheduleMultiplier (P : Model) (S : MMAlgebra.Schedule P.nfma) : MatrixMultiplier :=
  fun x y => do
    let ax ← x.mapM fun z : ℤ => P.a.encodeExact (z : ℚ)
    let ay ← y.mapM fun z : ℤ => P.b.encodeExact (z : ℚ)
    (MMAlgebra.eval (mcMachine P) (fun i => (ax.getD i 0, ay.getD i 0)) 0 0
      (S.term x.length)).map (mcMachine P).val

/-- **Every schedule is an exact matrix multiplier.** On every exact configuration, any schedule
returns `Σ xᵢyᵢ` exactly on `b`-bit integer vectors whose products total at most `2^24`. -/
theorem scheduleMultiplier_exactOn {P : Model} {b : ℕ} (hE : ExactMultiplier P b)
    (S : MMAlgebra.Schedule P.nfma) : (scheduleMultiplier P S).ExactOn b (2 ^ 24) := by
  intro x y hlen hx hy hbound
  let EA : ℤ → P.a.Word := fun z => (P.a.encodeExact (z : ℚ)).getD 0
  let EB : ℤ → P.b.Word := fun z => (P.b.encodeExact (z : ℚ)).getD 0
  have hA : ∀ z : ℤ, z.natAbs ≤ 2 ^ b → P.a.encodeExact (z : ℚ) = some (EA z) ∧
      IntWord P.a (EA z) ∧ P.a.wordValue (EA z) = z := by
    intro z hz
    obtain ⟨w, hw, hint, hv⟩ := hE.encA z hz
    have : EA z = w := by simp [EA, hw]
    rw [this]; exact ⟨hw, hint, hv⟩
  have hB : ∀ z : ℤ, z.natAbs ≤ 2 ^ b → P.b.encodeExact (z : ℚ) = some (EB z) ∧
      IntWord P.b (EB z) ∧ P.b.wordValue (EB z) = z := by
    intro z hz
    obtain ⟨w, hw, hint, hv⟩ := hE.encB z hz
    have : EB z = w := by simp [EB, hw]
    rw [this]; exact ⟨hw, hint, hv⟩
  have hmx : (x.mapM fun z : ℤ => P.a.encodeExact (z : ℚ)) = some (x.map EA) :=
    mapM_eq_some_map fun z hz => (hA z (hx z hz)).1
  have hmy : (y.mapM fun z : ℤ => P.b.encodeExact (z : ℚ)) = some (y.map EB) :=
    mapM_eq_some_map fun z hz => (hB z (hy z hz)).1
  let q : ℕ → P.a.Word × P.b.Word := fun i => ((x.map EA).getD i 0, (y.map EB).getD i 0)
  have hq : ∀ i, IntWord P.a (q i).1 ∧ IntWord P.b (q i).2 := by
    intro i
    constructor
    · rcases MMAlgebra.getD_map_cases EA 0 x i with h | ⟨z, hz, h⟩
      · show IntWord P.a ((x.map EA).getD i 0); rw [h]; exact intWord_zero hE.encA
      · show IntWord P.a ((x.map EA).getD i 0); rw [h]; exact (hA z (hx z hz)).2.1
    · rcases MMAlgebra.getD_map_cases EB 0 y i with h | ⟨z, hz, h⟩
      · show IntWord P.b ((y.map EB).getD i 0); rw [h]; exact intWord_zero hE.encB
      · show IntWord P.b ((y.map EB).getD i 0); rw [h]; exact (hB z (hy z hz)).2.1
  have hval : ∀ i ∈ List.range x.length,
      (mcMachine P).pval (q i) = ((x.getD i 0 : ℤ) : ℚ) * ((y.getD i 0 : ℤ) : ℚ) := by
    intro i hi
    rw [List.mem_range] at hi
    have hi' : i < y.length := hlen ▸ hi
    show P.a.wordValue ((x.map EA).getD i 0) * P.b.wordValue ((y.map EB).getD i 0) = _
    rw [MMAlgebra.getD_map_lt EA 0 0 x i hi, MMAlgebra.getD_map_lt EB 0 0 y i hi',
      (hA _ (hx _ (MMAlgebra.getD_mem_of_lt 0 x i hi))).2.2,
      (hB _ (hy _ (MMAlgebra.getD_mem_of_lt 0 y i hi'))).2.2]
  have hwf := S.wf x.length
  have hnh := hwf.noHole
  have hz0 : Rat.abs ((0 : ℤ) : ℚ) = 0 := by rw [Rat.intCast_zero, Ozaki.abs_zero]
  have hmag : MMAlgebra.mag (mcMachine P) q (Rat.abs ((0 : ℤ) : ℚ)) 0 (S.term x.length) ≤
      2 ^ (24 : ℤ) := by
    rw [hz0, MMAlgebra.mag_eq_leaves _ _ _ _ hnh, MMAlgebra.sum_leaves_eq_range (S.leaves _)]
    rw [List.map_congr_left (fun i hi => by rw [hval i hi]), MMAlgebra.range_sum_dotAbs x y hlen]
    have : ((dotAbs x y : ℕ) : ℚ) ≤ ((2 ^ 24 : ℕ) : ℚ) := Rat.natCast_le_natCast.mpr hbound
    rw [← Ozaki.two_pow_natCast] at this
    exact this
  obtain ⟨o, z, ho, hvo, hz⟩ := eval_int hE q hq 0 (zc := 0) (by decide +kernel)
    (S.term x.length) hwf hmag
  have hex : MMAlgebra.exact (mcMachine P) q ((0 : ℤ) : ℚ) 0 (S.term x.length) = (dotZ x y : ℚ) := by
    rw [Rat.intCast_zero, MMAlgebra.exact_eq_leaves _ _ _ _ hnh,
      MMAlgebra.sum_leaves_eq_range (S.leaves _)]
    rw [List.map_congr_left (fun i hi => by simp only [Function.comp]; rw [hval i hi]),
      MMAlgebra.range_sum_dotZ x y hlen]
  unfold scheduleMultiplier
  simp only [hmx, hmy, Option.bind_eq_bind, Option.bind_some]
  show (MMAlgebra.eval (mcMachine P) q 0 0 (S.term x.length)).map (mcMachine P).val = _
  rw [ho, Option.map_some, val_of hvo, hz, hex]; rfl

/-! ## The Ozaki schemes under every schedule -/

/-- **Ozaki-I gives the same bits under every schedule** of its slice products. -/
theorem ozaki1_schedules_agree {P : Model} {b : ℕ} (hE : ExactMultiplier P b)
    (S₁ S₂ : MMAlgebra.Schedule P.nfma) (add : ℚ → ℚ → Option ℚ) (s : ℕ) {x y : List ℚ}
    (hlen : x.length = y.length) (hbound : x.length * (2 ^ b * 2 ^ b) ≤ 2 ^ 24) :
    ozaki1 (scheduleMultiplier P S₁) add b s x y = ozaki1 (scheduleMultiplier P S₂) add b s x y := by
  rw [ozaki1_eq_sumWith (scheduleMultiplier_exactOn hE S₁) add s hlen hbound,
    ozaki1_eq_sumWith (scheduleMultiplier_exactOn hE S₂) add s hlen hbound]

/-- **Ozaki-II gives the same bits under every schedule** of its residue products. -/
theorem ozaki2_schedules_agree {P : Model} {b : ℕ} (hE : ExactMultiplier P b)
    (S₁ S₂ : MMAlgebra.Schedule P.nfma) (round : ℚ → Option ℚ) {B : CRTBasis} (hB : B.Valid)
    (hmb : ∀ m ∈ B.moduli, m ≤ 2 ^ (b + 1)) (Pr : ℕ) {x y : List ℚ} (hlen : x.length = y.length)
    (hbound : x.length * (2 ^ b * 2 ^ b) ≤ 2 ^ 24)
    (hrange : 2 * x.length * (2 ^ Pr * 2 ^ Pr) < B.modulus) :
    ozaki2 (scheduleMultiplier P S₁) round B Pr x y = ozaki2 (scheduleMultiplier P S₂) round B Pr x y := by
  rw [ozaki2_eq (scheduleMultiplier_exactOn hE S₁) round hB hmb Pr hlen hbound hrange,
    ozaki2_eq (scheduleMultiplier_exactOn hE S₂) round hB hmb Pr hlen hbound hrange]

/-- **Correctly rounded Ozaki-I under every schedule.** -/
theorem ozaki1CR_every_schedule {P : Model} {b : ℕ} (hE : ExactMultiplier P b)
    (S : MMAlgebra.Schedule P.nfma) {R : ℚ → Prop} {rnd : ℚ → Option ℚ} (h : RoundsToNearest R rnd)
    (hI : RoundsOnIntervals rnd) (ss : List ℕ) {x y : List ℚ} (hlen : x.length = y.length)
    (hbound : x.length * (2 ^ b * 2 ^ b) ≤ 2 ^ 24) :
    ozaki1CR (scheduleMultiplier P S) rnd b ss x y = rnd (dot x y) :=
  ozaki1CR_eq h hI (scheduleMultiplier_exactOn hE S) ss hlen hbound

/-- **Correctly rounded Ozaki-II under every schedule.** -/
theorem ozaki2CR_every_schedule {P : Model} {b : ℕ} (hE : ExactMultiplier P b)
    (S : MMAlgebra.Schedule P.nfma) {R : ℚ → Prop} {rnd : ℚ → Option ℚ} (h : RoundsToNearest R rnd)
    (hI : RoundsOnIntervals rnd) {cfgs : List (CRTBasis × ℕ)} {x y : List ℚ}
    (hcfg : ∀ c ∈ cfgs, c.1.Valid ∧ (∀ m ∈ c.1.moduli, m ≤ 2 ^ (b + 1)) ∧
      2 * x.length * (2 ^ c.2 * 2 ^ c.2) < c.1.modulus)
    (hlen : x.length = y.length) (hbound : x.length * (2 ^ b * 2 ^ b) ≤ 2 ^ 24) :
    ozaki2CR (scheduleMultiplier P S) rnd cfgs x y = rnd (dot x y) :=
  ozaki2CR_eq h hI (scheduleMultiplier_exactOn hE S) hcfg hlen hbound

/-! ## Three ways to make the result schedule-independent -/

/-- **(1) The exact region.** Two terms over the same multiset of products, on integer operands of
an exact configuration whose products total at most `2^24`, from `c = 0`: both return the exact sum
of their products. -/
theorem scheduleFree_exact {P : Model} {b : ℕ} (hE : ExactMultiplier P b)
    (q : ℕ → P.a.Word × P.b.Word) (hq : ∀ i, IntWord P.a (q i).1 ∧ IntWord P.b (q i).2)
    (t₁ t₂ : MMAlgebra.Term) (hw₁ : TermWF P.nfma t₁) (hw₂ : TermWF P.nfma t₂)
    (hperm : t₁.leaves.Perm t₂.leaves)
    (hm : (t₁.leaves.map fun i => Rat.abs ((mcMachine P).pval (q i))).sum ≤ 2 ^ (24 : ℤ)) :
    ∃ o₁ o₂ : F32, MMAlgebra.eval (mcMachine P) q 0 0 t₁ = some o₁ ∧
      MMAlgebra.eval (mcMachine P) q 0 0 t₂ = some o₂ ∧
      value32 o₁ = some (t₁.leaves.map ((mcMachine P).pval ∘ q)).sum ∧
      value32 o₂ = some (t₁.leaves.map ((mcMachine P).pval ∘ q)).sum := by
  have hz : value32 (0 : F32) = some ((0 : ℤ) : ℚ) := by decide +kernel
  have hz0 : Rat.abs ((0 : ℤ) : ℚ) = 0 := by rw [Rat.intCast_zero, Ozaki.abs_zero]
  have run : ∀ t : MMAlgebra.Term, TermWF P.nfma t → t.leaves.Perm t₁.leaves →
      ∃ o : F32, MMAlgebra.eval (mcMachine P) q 0 0 t = some o ∧
        value32 o = some (t₁.leaves.map ((mcMachine P).pval ∘ q)).sum := by
    intro t hw hp'
    have hmt : MMAlgebra.mag (mcMachine P) q (Rat.abs ((0 : ℤ) : ℚ)) 0 t ≤ 2 ^ (24 : ℤ) := by
      rw [hz0, MMAlgebra.mag_eq_leaves _ _ _ _ hw.noHole, MMAlgebra.sum_perm (hp'.map _)]
      exact hm
    obtain ⟨o, z, ho, hvo, hzv⟩ := eval_int hE q hq 0 (zc := 0) hz t hw hmt
    refine ⟨o, ho, ?_⟩
    rw [hvo, hzv, Rat.intCast_zero, MMAlgebra.exact_eq_leaves _ _ _ _ hw.noHole,
      MMAlgebra.sum_perm (hp'.map _)]
  obtain ⟨o₁, h₁, v₁⟩ := run t₁ hw₁ (List.Perm.refl _)
  obtain ⟨o₂, h₂, v₂⟩ := run t₂ hw₂ hperm.symm
  exact ⟨o₁, o₂, h₁, h₂, v₁, v₂⟩

theorem sum_truncSum (α : ℤ) : ∀ ts : List (BlockTrace P),
    sumQ (ts.map fun t => truncSum α t.prepared) =
      ((ts.flatMap fun t => t.prepared.p).map fun p => truncMantissa p.value α 24).sum
  | [] => by simp [sumQ]
  | t :: ts => by
    rw [List.map_cons, sumQ, sum_truncSum α ts, List.flatMap_cons, List.map_append, List.sum_append]
    unfold truncSum; rw [sumQ_eq]

/-- **(2) Pinning on CDNA 3.** Two pinned runs from the same `c₀` whose blocks hold the same multiset
of products, in any order and grouping, return the same word value: `c₀ + Σ trunc_{α−24}(p_ℓ)`
over that multiset (see `runBlocks_pinned` for the conditions). -/
theorem scheduleFree_pinned {P : Model} (hP : CDNA3Like P) {α : ℤ} (hlo : -125 ≤ α) (hhi : α ≤ 128)
    (bs₁ bs₂ : List (List P.a.Word × List P.b.Word)) (c : F32) (v : ℚ)
    (ts₁ ts₂ : List (BlockTrace P)) (hc : value32 c = some v) (hgrid : OnGrid v (α - 24))
    (h₁ : runBlocks P c bs₁ = .ok ts₁) (h₂ : runBlocks P c bs₂ = .ok ts₂)
    (hp₁ : ∀ t ∈ ts₁, PinnedProducts α t.prepared) (hp₂ : ∀ t ∈ ts₂, PinnedProducts α t.prepared)
    (hr₁ : ∀ n ≤ ts₁.length, absQ (v + sumQ ((ts₁.take n).map fun t => truncSum α t.prepared)) < pow2 α)
    (hr₂ : ∀ n ≤ ts₂.length, absQ (v + sumQ ((ts₂.take n).map fun t => truncSum α t.prepared)) < pow2 α)
    (hperm : (ts₁.flatMap fun t => t.prepared.p).Perm (ts₂.flatMap fun t => t.prepared.p)) :
    value32 (lastOutput c ts₁) = value32 (lastOutput c ts₂) := by
  rw [runBlocks_pinned hP hlo hhi bs₁ c v ts₁ hc hgrid h₁ hp₁ hr₁,
    runBlocks_pinned hP hlo hhi bs₂ c v ts₂ hc hgrid h₂ hp₂ hr₂, sum_truncSum, sum_truncSum,
    MMAlgebra.sum_perm (hperm.map _)]

/-- **(3) Correct rounding.** The correctly rounded Ozaki-I, run on any two schedules, returns the
correctly rounded `x · y` on both. -/
theorem scheduleFree_correctlyRounded {P : Model} {b : ℕ} (hE : ExactMultiplier P b)
    (S₁ S₂ : MMAlgebra.Schedule P.nfma) {R : ℚ → Prop} {rnd : ℚ → Option ℚ}
    (h : RoundsToNearest R rnd) (hI : RoundsOnIntervals rnd) (ss : List ℕ) {x y : List ℚ}
    (hlen : x.length = y.length) (hbound : x.length * (2 ^ b * 2 ^ b) ≤ 2 ^ 24) :
    ozaki1CR (scheduleMultiplier P S₁) rnd b ss x y = rnd (dot x y) ∧
      ozaki1CR (scheduleMultiplier P S₂) rnd b ss x y = rnd (dot x y) :=
  ⟨ozaki1CR_every_schedule hE S₁ h hI ss hlen hbound,
    ozaki1CR_every_schedule hE S₂ h hI ss hlen hbound⟩

end MMAlgebra.MC
