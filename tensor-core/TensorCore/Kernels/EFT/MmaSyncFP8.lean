import TensorCore.Kernels.EFT.Correctness
import TensorCore.TC.MmaSyncFP8Bounds

/-! # TC-EFT for FP8 `mma.sync`

B200's FP8 block FMA takes all 32 products of an FP8 `mma.sync` and `c` in one block, so the 576-bit
TC-EFT of that block corrects the instruction from any finite `D`, such as its own output. -/

namespace TensorCore.EFMachine

theorem prepareProducts_cons {p : Model} {a b : p.Word} {rest : List (p.Word × p.Word)}
    {x y : Decoded} {ds : List (Decoded × Decoded)} (ha : p.decode a = some x) (hb : p.decode b = some y)
    (hr : prepareProducts p rest = some ds) :
    prepareProducts p ((a, b) :: rest) = some ((x, y) :: ds) := by
  unfold prepareProducts at hr ⊢
  rw [List.mapM_cons, hr]
  simp [ha, hb]

theorem value16_of_decode {w : BitVec 8} {conv : BitVec 8 → F16} {d : Decoded}
    (hexact : (decode16 (conv w)).map Decoded.value = some d.value) : value16 (conv w) = d.value := by
  unfold value16; rw [hexact]; rfl

/-- The FP8 products decode in a block of B200's FP8 model with their FP16 conversions' values. -/
theorem prepareProducts_fp8 {p : Model} (conv : BitVec 8 → F16) (word : BitVec 8 → p.Word)
    (hval : ∀ w d, p.decode (word w) = some d → value16 (conv w) = d.value) :
    ∀ {ps : List (BitVec 8 × BitVec 8)},
      (∀ ab ∈ ps, (p.decode (word ab.1)).isSome ∧ (p.decode (word ab.2)).isSome) →
      ∃ ds, prepareProducts p (ps.map fun (a, b) => (word a, word b)) = some ds ∧
        sumQ (ds.map fun (a, b) => a.value * b.value) =
          sumQ (ps.map fun (a, b) => value16 (conv a) * value16 (conv b))
  | [], _ => ⟨[], rfl, rfl⟩
  | (a, b) :: rest, h => by
    obtain ⟨ds, hds, hsum⟩ := prepareProducts_fp8 conv word hval (ps := rest)
      (fun ab hab => h ab (List.mem_cons_of_mem _ hab))
    obtain ⟨ha, hb⟩ := h (a, b) (List.mem_cons_self ..)
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp ha
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hb
    refine ⟨(x, y) :: ds, prepareProducts_cons hx hy hds, ?_⟩
    simp only [List.map_cons, sumQ]
    rw [hsum, hval a x hx, hval b y hy]

theorem fp8Block_exactDot {p : Model} (conv : BitVec 8 → F16) (word : BitVec 8 → p.Word)
    (hval : ∀ w d, p.decode (word w) = some d → value16 (conv w) = d.value)
    {ps : List (BitVec 8 × BitVec 8)} {c : F32}
    (hfin : ∀ ab ∈ ps, (p.decode (word ab.1)).isSome ∧ (p.decode (word ab.2)).isSome)
    (hc : ∃ v, value32 c = some v) :
    TensorCore.exactDot (⟨ps.map fun (a, b) => (word a, word b), c⟩ : BlockInput p) =
      some (mmaSyncFP8Exact conv c ps) := by
  obtain ⟨ds, hds, hsum⟩ := prepareProducts_fp8 conv word hval hfin
  obtain ⟨vc, hvc⟩ := hc
  unfold value32 at hvc
  cases hd : decode32 c with
  | none => rw [hd] at hvc; cases hvc
  | some cd =>
    rw [hd] at hvc
    simp only [Option.map_some, Option.some.injEq] at hvc
    unfold TensorCore.exactDot TensorCore.prepare
    simp only [hd, hds, Option.map_some, PreparedBlock.exactDot, PreparedBlock.exactProducts]
    unfold mmaSyncFP8Exact
    rw [hsum, show value32 c = some vc by simp [value32, hd, hvc], Option.getD_some, hvc]

/-- E5M2 `mma.sync`: the 576-bit TC-EFT of B200's E5M2 block returns `c + Σ a_k b_k` rounded to
nearest even, from any finite `D`. -/
theorem mmaSyncFP8_eft_e5m2 {c D : F32} {ps : List (BitVec 8 × BitVec 8)} {d : ℚ}
    (hlen : ps.length = 32)
    (hfin : ∀ ab ∈ ps, (e5m2Encoding.decode ab.1).isSome ∧ (e5m2Encoding.decode ab.2).isSome)
    (hc : ∃ v, value32 c = some v) (hD : value32 D = some d) :
    ∃ r, tcEft .blackwellE5M2 ⟨ps, c⟩ D = .ok r ∧
      r.bits = round32 .nearestEven (mmaSyncFP8Exact e5m2ToF16 c ps) := by
  have hdec : ∀ w, blackwellE5M2F32.decode w = e5m2Encoding.decode w := fun w => (e5m2_decode w).symm
  have hval : ∀ w d, blackwellE5M2F32.decode (id w) = some d → value16 (e5m2ToF16 w) = d.value := by
    intro w d h
    have h' : blackwellE5M2F32.decode w = some d := h
    apply value16_of_decode
    rw [(e5m2ToF16_exact w).1, ← hdec, h']; rfl
  have hx := fp8Block_exactDot (p := blackwellE5M2F32) e5m2ToF16 id hval
    (fun ab hab => by
      show (blackwellE5M2F32.decode ab.1).isSome ∧ (blackwellE5M2F32.decode ab.2).isSome
      rw [hdec, hdec]; exact hfin ab hab) hc
  have hps : (ps.map fun (ab : BitVec 8 × BitVec 8) => (id ab.1, id ab.2)) = ps := by
    clear hx hfin hlen; induction ps <;> simp_all
  rw [hps] at hx
  exact tcEft_correct (hlen.trans rfl) hx hD

/-- E4M3 `mma.sync`: the 576-bit TC-EFT of B200's E4M3 block, on the `e4m3x` words, returns
`c + Σ a_k b_k` rounded to nearest even, from any finite `D`. -/
theorem mmaSyncFP8_eft_e4m3 {c D : F32} {ps : List (BitVec 8 × BitVec 8)} {d : ℚ}
    (hlen : ps.length = 32)
    (hfin : ∀ ab ∈ ps, (e4m3Encoding.decode ab.1).isSome ∧ (e4m3Encoding.decode ab.2).isSome)
    (hc : ∃ v, value32 c = some v) (hD : value32 D = some d) :
    ∃ r, tcEft .blackwellE4M3 ⟨widenE4M3Pairs ps, c⟩ D = .ok r ∧
      r.bits = round32 .nearestEven (mmaSyncFP8Exact e4m3ToF16 c ps) := by
  have hdec : ∀ w, blackwellE4M3F32.decode (widenE4M3 w) = e4m3Encoding.decode w :=
    fun w => (e4m3_decode_widen w).symm
  have hval : ∀ w d, blackwellE4M3F32.decode (widenE4M3 w) = some d →
      value16 (e4m3ToF16 w) = d.value := by
    intro w d h
    apply value16_of_decode
    rw [(e4m3ToF16_exact w).1, ← hdec, h]; rfl
  have hx := fp8Block_exactDot (p := blackwellE4M3F32) e4m3ToF16 widenE4M3 hval
    (fun ab hab => by rw [hdec, hdec]; exact hfin ab hab) hc
  exact tcEft_correct (show (widenE4M3Pairs ps).length = 32 by simp [widenE4M3Pairs, hlen]) hx hD

end TensorCore.EFMachine
