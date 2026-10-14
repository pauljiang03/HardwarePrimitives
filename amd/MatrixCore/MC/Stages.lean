import MatrixCore.MC.Block

/-! # Accumulation stages

The value `S_acc` that each configuration presents to the final `fl{·}`. Every stage is an
exact rational computation; bits are discarded only where the paper names a truncation, an RD,
or an `fl{·}`. -/

namespace MatrixCore

/-! ## `pair_wise_sum` (CDNA 2) -/

/-- `fl{x}` as a value: binary32 RNE, with subnormal results flushed when `ftz`; `none` on
overflow. -/
def flValue (ftz : Bool) (x : ℚ) : Option ℚ := (fl32 ftz x).bind value32

/-- The balanced pairwise sum of a group: split it into halves, sum each half, and round their sum
with `fl{·}`. `depth` bounds the recursion; any `depth` at least the list length gives the full
pairwise sum. -/
def pairwiseGroupSum (ftz : Bool) : ℕ → List ℚ → Option ℚ
  | _, [] => some 0
  | _, [x] => some x
  | 0, _ => none
  | depth + 1, xs => do
    let h := xs.length / 2
    let u ← pairwiseGroupSum ftz depth (xs.take h)
    let v ← pairwiseGroupSum ftz depth (xs.drop h)
    flValue ftz (u + v)

/-- CDNA 2: inputs flushed when subnormals are unsupported, every product converted to binary32
with `fl{·}`, the pairwise sum `fl{fl{p₁ + p₂} + fl{p₃ + p₄}}`, then `c` added. Returns the
exact sum of `c` and the pairwise sum, which the final `fl{·}` rounds; `none` on an intermediate overflow. -/
def pairwiseSum (P : Model) (x : Prepared) : Option ℚ := do
  let x' := if P.subnormals then x else x.flushed
  let ps ← x'.p.mapM fun p => flValue (!P.subnormals) p.value
  let t ← pairwiseGroupSum (!P.subnormals) ps.length ps
  return x'.c.value + t

/-! ## `global_alignment` and `odd_even_grouping` (CDNA 3) -/

/-- Align the significands to `e_max`, truncate them to `23 + padding` mantissa bits, and
accumulate (exactly) into `S_{p_i,sum}`. Returns `(e_max, S_{p_i,sum})` as an exact value. -/
def alignedSum (padding : ℕ) (ps : List Unpacked) : Option ℤ × ℚ :=
  match maxExp ps with
  | none => (none, 0)
  | some e => (some e, sumQ (ps.map fun p => truncMantissa p.value e (23 + padding)))

/-- `(e_max, S_{p_i,sum})` of the configuration. With odd/even grouping, the odd and even sums
are each aligned to their own maximum exponent, then the one with the smaller exponent is shifted
to the common `e_max` and RD to `23 + padding` mantissa bits (Algorithm 2 lines 1–6). -/
def productSum (P : Model) (ps : List Unpacked) : Option ℤ × ℚ :=
  match P.accumulation with
  | .oddEvenGrouping =>
    let odd := alignedSum P.padding (oddIndexed ps)
    let even := alignedSum P.padding (evenIndexed ps)
    match joinExp odd.1 even.1 with
    | none => (none, 0)
    | some e => (some e, rdMantissa odd.2 e (23 + P.padding) + rdMantissa even.2 e (23 + P.padding))
  | _ => alignedSum P.padding ps

/-- `s'_c`: `s_c` shifted right by `e_max − e_c` and RD to `24` mantissa bits; zero once the
shift exceeds the cutoff (binary8). -/
def shiftedC (P : Model) (eMax eC : ℤ) (c : Unpacked) : ℚ :=
  match P.late.cCutoff with
  | some n => if eMax - eC > n then 0 else rdMantissa c.value eMax P.late.cMantissaBits
  | none => rdMantissa c.value eMax P.late.cMantissaBits

/-- Subnormal-aware normalization followed by RD to `k` mantissa bits: the leading bit is
moved to the binary point, but never below exponent `−126`. -/
def normalizeRD (k : ℕ) (x : ℚ) : ℚ := if x = 0 then 0 else rdMantissa x (normExp (absQ x)) k

/-- `S_acc` when `e_c > e_max`: `S'_{p_i,sum}` is `S_{p_i,sum}` shifted right by `e_c − e_max` and
RD to `32` mantissa bits; `S_acc = S'_{p_i,sum} + s_c` is normalized and RD to `31`
mantissa bits (Algorithm 1 lines 8–11). -/
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
