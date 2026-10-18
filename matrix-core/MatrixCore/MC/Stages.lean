import MatrixCore.MC.Block

/-! # Accumulation stages

The exact rational value `S_acc` that each configuration presents to the final `fl{·}`. -/

namespace MatrixCore

/-! ## `pair_wise_sum` (CDNA 2) -/

/-- `fl{x}` as a value: FP32 RNE, subnormal results flushed when `ftz`; `none` on overflow. -/
def flValue (ftz : Bool) (x : ℚ) : Option ℚ := (fl32 ftz x).bind value32

/-- Balanced pairwise sum, rounding each node with `fl{·}`; any `depth` ≥ the length suffices. -/
def pairwiseGroupSum (ftz : Bool) : ℕ → List ℚ → Option ℚ
  | _, [] => some 0
  | _, [x] => some x
  | 0, _ => none
  | depth + 1, xs => do
    let h := xs.length / 2
    let u ← pairwiseGroupSum ftz depth (xs.take h)
    let v ← pairwiseGroupSum ftz depth (xs.drop h)
    flValue ftz (u + v)

/-- CDNA 2 `S_acc`: `c` plus the pairwise sum of the products, each rounded with `fl{·}`. -/
def pairwiseSum (P : Model) (x : Prepared) : Option ℚ := do
  let x' := if P.subnormals then x else x.flushed
  let ps ← x'.p.mapM fun p => flValue (!P.subnormals) p.value
  let t ← pairwiseGroupSum (!P.subnormals) ps.length ps
  return x'.c.value + t

/-! ## `global_alignment` and `odd_even_grouping` (CDNA 3) -/

/-- `(e_max, S_{p_i,sum})` with products truncated to `23 + padding` mantissa bits at `e_max`. -/
def alignedSum (padding : ℕ) (ps : List Unpacked) : Option ℤ × ℚ :=
  match maxExp ps with
  | none => (none, 0)
  | some e => (some e, sumQ (ps.map fun p => truncMantissa p.value e (23 + padding)))

/-- `(e_max, S_{p_i,sum})` of the configuration (Algorithm 2 lines 1–6 for odd/even grouping). -/
def productSum (P : Model) (ps : List Unpacked) : Option ℤ × ℚ :=
  match P.accumulation with
  | .oddEvenGrouping =>
    let odd := alignedSum P.padding (oddIndexed ps)
    let even := alignedSum P.padding (evenIndexed ps)
    match joinExp odd.1 even.1 with
    | none => (none, 0)
    | some e => (some e, rdMantissa odd.2 e (23 + P.padding) + rdMantissa even.2 e (23 + P.padding))
  | _ => alignedSum P.padding ps

/-- `s'_c`: `s_c` shifted to `e_max` and RD; zero once the shift exceeds the cutoff (FP8). -/
def shiftedC (P : Model) (eMax eC : ℤ) (c : Unpacked) : ℚ :=
  match P.late.cCutoff with
  | some n => if eMax - eC > n then 0 else rdMantissa c.value eMax P.late.cMantissaBits
  | none => rdMantissa c.value eMax P.late.cMantissaBits

/-- Normalization to an exponent of at least `−126`, then RD to `k` mantissa bits. -/
def normalizeRD (k : ℕ) (x : ℚ) : ℚ := if x = 0 then 0 else rdMantissa x (normExp (absQ x)) k

/-- `S_acc` when `e_c > e_max` (Algorithm 1 lines 8–11). -/
def shiftedSum (P : Model) (eC : ℤ) (pSum : ℚ) (c : Unpacked) : ℚ :=
  normalizeRD P.late.accMantissaBits (rdMantissa pSum eC P.late.sumMantissaBits + c.value)

/-- `S_acc` after the late addition of `c` (Algorithm 1 lines 3–11). -/
def lateSum (P : Model) (eMax : Option ℤ) (pSum : ℚ) (c : Unpacked) : ℚ :=
  match cExp P c with
  | none => pSum
  | some eC =>
    match eMax with
    | some e => if eC ≤ e then pSum + shiftedC P e eC c else shiftedSum P eC pSum c
    | none => shiftedSum P eC pSum c

/-- `S_acc` of Algorithms 1 and 2. -/
def alignedAccumulation (P : Model) (x : Prepared) : ℚ :=
  let s := productSum P x.p
  lateSum P s.1 s.2 x.c

end MatrixCore
