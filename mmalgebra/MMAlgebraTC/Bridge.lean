import MMAlgebra.Schedule
import MMAlgebraTC.Exact
import MMAlgebraTC.Pinned
import OzakiTC

/-! # Every schedule is an exact matrix multiplier (Tensor Core model)

The Ozaki schemes rely on a matrix multiplier that returns `Σ xᵢyᵢ` exactly on small integers
(`Ozaki.MatrixMultiplier.ExactOn`). `scheduleMultiplier p S` runs any reduction schedule `S` (a
chain, split-K, stream-K, pairwise reduction, or any other order and grouping of block FMAs and
binary32 additions) on the Tensor Core model; `scheduleMultiplier_exactOn` shows that every one of
them is exact on `b`-bit integers whose products total at most `2^24`, the bound the Ozaki schemes
use. So Ozaki-I and Ozaki-II return the same bits under every schedule of their slice and residue
products (`ozaki1_schedules_agree`, `ozaki2_schedules_agree`), and their correctly rounded versions
return the correctly rounded `x · y` under every schedule (`ozaki1CR_every_schedule`,
`ozaki2CR_every_schedule`).

## Three ways to make the result schedule-independent

Each of the following states that a program's value is a function of the multiset of its
products alone, so that every schedule gives the same bits:

1. **The exact region** (`scheduleFree_exact`): on integer operands within the exactness bound,
   every schedule returns the exact sum of its products.
2. **Pinning** (`scheduleFree_pinned`): with a cancelling pin pair in every block FMA, a chain
   returns the sum of its products each truncated to a fixed grid.
3. **Correct rounding** (`scheduleFree_correctlyRounded`): the correctly rounded Ozaki scheme,
   run on any schedule, returns the correctly rounded exact product. -/

open TensorCore Ozaki Ozaki.TC

namespace MMAlgebra.TC

/-- The matrix multiplier that encodes two integer vectors as operand words and evaluates the
schedule's term for their length on the Tensor Core model, from `c = 0`. -/
def scheduleMultiplier (p : Model) (S : MMAlgebra.Schedule p.nfma) : MatrixMultiplier :=
  fun x y => do
    let ax ← x.mapM (encodeInt p.input)
    let ay ← y.mapM (encodeInt p.input)
    (MMAlgebra.eval (tcMachine p) (fun i => (ax.getD i 0, ay.getD i 0)) 0 0
      (S.term x.length)).map value32D

/-- **Every schedule is an exact matrix multiplier.** On every Tensor Core model with `2b ≤ F`, any
schedule returns `Σ xᵢyᵢ` exactly on `b`-bit integer vectors whose products total at most `2^24`. -/
theorem scheduleMultiplier_exactOn {p : Model} {b : ℕ} (hp : IntExact p b) (hh : HoldsInts p b)
    (S : MMAlgebra.Schedule p.nfma) : (scheduleMultiplier p S).ExactOn b (2 ^ 24) := by
  intro x y hlen hx hy hbound
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
  let q : ℕ → p.Word × p.Word := fun i => ((x.map E).getD i 0, (y.map E).getD i 0)
  have hint : ∀ (v : List ℤ), (∀ a ∈ v, a.natAbs ≤ 2 ^ b) → ∀ i, IntWord p b ((v.map E).getD i 0) := by
    intro v hv i
    rcases MMAlgebra.getD_map_cases E 0 v i with h | ⟨z, hz, h⟩
    · rw [h]; exact intWord_zero hh
    · rw [h]; exact (hE z (hv z hz)).2.1
  have hq : ∀ i, IntWord p b (q i).1 ∧ IntWord p b (q i).2 := fun i => ⟨hint x hx i, hint y hy i⟩
  have hval : ∀ i ∈ List.range x.length,
      (tcMachine p).pval (q i) = ((x.getD i 0 : ℤ) : ℚ) * ((y.getD i 0 : ℤ) : ℚ) := by
    intro i hi
    rw [List.mem_range] at hi
    have hi' : i < y.length := hlen ▸ hi
    show wordValue p ((x.map E).getD i 0) * wordValue p ((y.map E).getD i 0) = _
    rw [MMAlgebra.getD_map_lt E 0 0 x i hi, MMAlgebra.getD_map_lt E 0 0 y i hi',
      (hE _ (hx _ (MMAlgebra.getD_mem_of_lt 0 x i hi))).2.2,
      (hE _ (hy _ (MMAlgebra.getD_mem_of_lt 0 y i hi'))).2.2]
  have hwf := S.wf x.length
  have hnh := hwf.noHole
  have hz0 : Rat.abs ((0 : ℤ) : ℚ) = 0 := by rw [Rat.intCast_zero, Ozaki.abs_zero]
  have hmag : MMAlgebra.mag (tcMachine p) q (Rat.abs ((0 : ℤ) : ℚ)) 0 (S.term x.length) ≤
      2 ^ (24 : ℤ) := by
    rw [hz0, MMAlgebra.mag_eq_leaves _ _ _ _ hnh, MMAlgebra.sum_leaves_eq_range (S.leaves _)]
    rw [List.map_congr_left (fun i hi => by rw [hval i hi]), MMAlgebra.range_sum_dotAbs x y hlen]
    have : ((dotAbs x y : ℕ) : ℚ) ≤ ((2 ^ 24 : ℕ) : ℚ) := Rat.natCast_le_natCast.mpr hbound
    rw [← two_pow_natCast] at this
    exact this
  obtain ⟨o, z, ho, hvo, hz⟩ := eval_int hp hh q hq 0 (zc := 0) (by decide +kernel)
    (S.term x.length) hwf hmag
  have hex : MMAlgebra.exact (tcMachine p) q ((0 : ℤ) : ℚ) 0 (S.term x.length) = (dotZ x y : ℚ) := by
    rw [Rat.intCast_zero, MMAlgebra.exact_eq_leaves _ _ _ _ hnh,
      MMAlgebra.sum_leaves_eq_range (S.leaves _)]
    rw [List.map_congr_left (fun i hi => by simp only [Function.comp]; rw [hval i hi]),
      MMAlgebra.range_sum_dotZ x y hlen]
  unfold scheduleMultiplier
  simp only [hmx, hmy, Option.bind_eq_bind, Option.bind_some]
  show (MMAlgebra.eval (tcMachine p) q 0 0 (S.term x.length)).map value32D = _
  rw [ho, Option.map_some, value32D_of hvo, hz, hex]; rfl

/-! ## The Ozaki schemes under every schedule -/

/-- **Ozaki-I gives the same bits under every schedule** of its slice products. -/
theorem ozaki1_schedules_agree {p : Model} {b : ℕ} (hp : IntExact p b) (hh : HoldsInts p b)
    (S₁ S₂ : MMAlgebra.Schedule p.nfma) (add : ℚ → ℚ → Option ℚ) (s : ℕ) {x y : List ℚ}
    (hlen : x.length = y.length) (hbound : x.length * (2 ^ b * 2 ^ b) ≤ 2 ^ 24) :
    ozaki1 (scheduleMultiplier p S₁) add b s x y = ozaki1 (scheduleMultiplier p S₂) add b s x y := by
  rw [ozaki1_eq_sumWith (scheduleMultiplier_exactOn hp hh S₁) add s hlen hbound,
    ozaki1_eq_sumWith (scheduleMultiplier_exactOn hp hh S₂) add s hlen hbound]

/-- **Ozaki-II gives the same bits under every schedule** of its residue products. -/
theorem ozaki2_schedules_agree {p : Model} {b : ℕ} (hp : IntExact p b) (hh : HoldsInts p b)
    (S₁ S₂ : MMAlgebra.Schedule p.nfma) (round : ℚ → Option ℚ) {B : CRTBasis} (hB : B.Valid)
    (hmb : ∀ m ∈ B.moduli, m ≤ 2 ^ (b + 1)) (P : ℕ) {x y : List ℚ} (hlen : x.length = y.length)
    (hbound : x.length * (2 ^ b * 2 ^ b) ≤ 2 ^ 24)
    (hrange : 2 * x.length * (2 ^ P * 2 ^ P) < B.modulus) :
    ozaki2 (scheduleMultiplier p S₁) round B P x y = ozaki2 (scheduleMultiplier p S₂) round B P x y := by
  rw [ozaki2_eq (scheduleMultiplier_exactOn hp hh S₁) round hB hmb P hlen hbound hrange,
    ozaki2_eq (scheduleMultiplier_exactOn hp hh S₂) round hB hmb P hlen hbound hrange]

/-- **Correctly rounded Ozaki-I under every schedule.** Run on any schedule, the correctly rounded
Ozaki-I returns the correctly rounded `x · y`. -/
theorem ozaki1CR_every_schedule {p : Model} {b : ℕ} (hp : IntExact p b) (hh : HoldsInts p b)
    (S : MMAlgebra.Schedule p.nfma) {R : ℚ → Prop} {rnd : ℚ → Option ℚ} (h : RoundsToNearest R rnd)
    (hI : RoundsOnIntervals rnd) (ss : List ℕ) {x y : List ℚ} (hlen : x.length = y.length)
    (hbound : x.length * (2 ^ b * 2 ^ b) ≤ 2 ^ 24) :
    ozaki1CR (scheduleMultiplier p S) rnd b ss x y = rnd (dot x y) :=
  ozaki1CR_eq h hI (scheduleMultiplier_exactOn hp hh S) ss hlen hbound

/-- **Correctly rounded Ozaki-II under every schedule.** -/
theorem ozaki2CR_every_schedule {p : Model} {b : ℕ} (hp : IntExact p b) (hh : HoldsInts p b)
    (S : MMAlgebra.Schedule p.nfma) {R : ℚ → Prop} {rnd : ℚ → Option ℚ} (h : RoundsToNearest R rnd)
    (hI : RoundsOnIntervals rnd) {cfgs : List (CRTBasis × ℕ)} {x y : List ℚ}
    (hcfg : ∀ c ∈ cfgs, c.1.Valid ∧ (∀ m ∈ c.1.moduli, m ≤ 2 ^ (b + 1)) ∧
      2 * x.length * (2 ^ c.2 * 2 ^ c.2) < c.1.modulus)
    (hlen : x.length = y.length) (hbound : x.length * (2 ^ b * 2 ^ b) ≤ 2 ^ 24) :
    ozaki2CR (scheduleMultiplier p S) rnd cfgs x y = rnd (dot x y) :=
  ozaki2CR_eq h hI (scheduleMultiplier_exactOn hp hh S) hcfg hlen hbound

/-! ## Three ways to make the result schedule-independent -/

/-- **(1) The exact region.** Two terms over the same multiset of products (their leaves are
permutations of each other), on `b`-bit integer operands whose products total at most `2^24`, from
`c = 0`: both return the exact sum of their products, so they agree. -/
theorem scheduleFree_exact {p : Model} {b : ℕ} (hp : IntExact p b) (hh : HoldsInts p b)
    (q : ℕ → p.Word × p.Word) (hq : ∀ i, IntWord p b (q i).1 ∧ IntWord p b (q i).2)
    (t₁ t₂ : MMAlgebra.Term) (hw₁ : TermWF p.nfma t₁) (hw₂ : TermWF p.nfma t₂)
    (hperm : t₁.leaves.Perm t₂.leaves)
    (hm : (t₁.leaves.map fun i => Rat.abs ((tcMachine p).pval (q i))).sum ≤ 2 ^ (24 : ℤ)) :
    ∃ o₁ o₂ : F32, MMAlgebra.eval (tcMachine p) q 0 0 t₁ = some o₁ ∧
      MMAlgebra.eval (tcMachine p) q 0 0 t₂ = some o₂ ∧
      value32 o₁ = some (t₁.leaves.map ((tcMachine p).pval ∘ q)).sum ∧
      value32 o₂ = some (t₁.leaves.map ((tcMachine p).pval ∘ q)).sum := by
  have hz : value32 (0 : F32) = some ((0 : ℤ) : ℚ) := by decide +kernel
  have hz0 : Rat.abs ((0 : ℤ) : ℚ) = 0 := by rw [Rat.intCast_zero, Ozaki.abs_zero]
  have run : ∀ t : MMAlgebra.Term, TermWF p.nfma t → t.leaves.Perm t₁.leaves →
      ∃ o : F32, MMAlgebra.eval (tcMachine p) q 0 0 t = some o ∧
        value32 o = some (t₁.leaves.map ((tcMachine p).pval ∘ q)).sum := by
    intro t hw hp'
    have hmt : MMAlgebra.mag (tcMachine p) q (Rat.abs ((0 : ℤ) : ℚ)) 0 t ≤ 2 ^ (24 : ℤ) := by
      rw [hz0, MMAlgebra.mag_eq_leaves _ _ _ _ hw.noHole, MMAlgebra.sum_perm (hp'.map _)]
      exact hm
    obtain ⟨o, z, ho, hvo, hzv⟩ := eval_int hp hh q hq 0 (zc := 0) hz t hw hmt
    refine ⟨o, ho, ?_⟩
    rw [hvo, hzv, Rat.intCast_zero, MMAlgebra.exact_eq_leaves _ _ _ _ hw.noHole,
      MMAlgebra.sum_perm (hp'.map _)]
  obtain ⟨o₁, h₁, v₁⟩ := run t₁ hw₁ (List.Perm.refl _)
  obtain ⟨o₂, h₂, v₂⟩ := run t₂ hw₂ hperm.symm
  exact ⟨o₁, o₂, h₁, h₂, v₁, v₂⟩

/-- **(2) Pinning.** On every Tensor Core model, a pinned chain over any arrangement of a multiset of
products returns `c + Σ trunc_g(aᵢbᵢ)` over that multiset, with `g = α − F`: a function of the
multiset alone (see `runBlocks_pinned` for the conditions). -/
theorem scheduleFree_pinned {p : Model} {α : ℤ} (hm : PinnedModel p α)
    (blocks : List (List (p.Word × p.Word))) (l : List (p.Word × p.Word))
    (hperm : blocks.flatten.Perm l) (c : F32) (v : ℚ) (hc : value32 c = some v)
    (hcg : ∃ z : ℤ, v = z * pow2 (α - p.alignFracBits)) (hg : ∀ gr ∈ blocks, PinnedBlock p α gr)
    (hr : PrefixesInRange p (α - p.alignFracBits) v blocks) {ts : List BlockTrace}
    (h : runBlocks p c blocks = .ok ts) :
    runValue c ts = v + truncSum p (α - p.alignFracBits) l := by
  rw [runBlocks_pinned hm blocks c v ts hc hcg hg hr h, truncSum_perm p _ hperm]

/-- **(3) Correct rounding.** The correctly rounded Ozaki-I, run on any schedule, returns the
correctly rounded `x · y`, a function of the inputs alone. -/
theorem scheduleFree_correctlyRounded {p : Model} {b : ℕ} (hp : IntExact p b) (hh : HoldsInts p b)
    (S₁ S₂ : MMAlgebra.Schedule p.nfma) {R : ℚ → Prop} {rnd : ℚ → Option ℚ}
    (h : RoundsToNearest R rnd) (hI : RoundsOnIntervals rnd) (ss : List ℕ) {x y : List ℚ}
    (hlen : x.length = y.length) (hbound : x.length * (2 ^ b * 2 ^ b) ≤ 2 ^ 24) :
    ozaki1CR (scheduleMultiplier p S₁) rnd b ss x y = rnd (dot x y) ∧
      ozaki1CR (scheduleMultiplier p S₂) rnd b ss x y = rnd (dot x y) :=
  ⟨ozaki1CR_every_schedule hp hh S₁ h hI ss hlen hbound,
    ozaki1CR_every_schedule hp hh S₂ h hI ss hlen hbound⟩

end MMAlgebra.TC
