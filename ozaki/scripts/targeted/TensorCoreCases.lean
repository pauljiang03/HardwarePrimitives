import TensorCore

/-! Targeted hardware-validation cases on the NVIDIA Tensor Core model.

Run from the repository root: `lake env lean ozaki/scripts/targeted/TensorCoreCases.lean`.
Each `#eval` prints one line per instruction-level inner product,
`TC|id|model|K|c|products|output|value|exact`: the words are decimal naturals (converted to hex
by `targeted_validation.py`), `products` is the whole `k`-long vector of operand pairs, `K` the
FMA size of the block FMAs it is split into (`TensorCore.runBlocks`: contiguous blocks in
increasing `k`, the FP32 output of each block FMA the `c` of the next), `output` the model's final
output word (or `ERR <error>`), `value` its value and `exact` the exact `c + Σ aᵢbᵢ`. An id
containing `@alt=` is the same input under an alternative hypothesis (another FMA size, number of
extra alignment bits or minimum alignment exponent), which a hardware mismatch with the main
prediction would point to. -/

open TensorCore

namespace TargetedTC

def ratStr (q : ℚ) : String := if q.den = 1 then toString q.num else s!"{q.num}/{q.den}"

def pairsStr {p : Model} (ps : List (p.Word × p.Word)) : String :=
  "[" ++ ", ".intercalate (ps.map fun (a, b) => s!"[{a.toNat}, {b.toNat}]") ++ "]"

/-- Contiguous blocks of `k` (the last one shorter if `k` does not divide the length). -/
def blocksOf {α : Type} (k : ℕ) (xs : List α) : List (List α) :=
  (List.range ((xs.length + k - 1) / k)).map fun i => (xs.drop (i * k)).take k

/-- The exact `c + Σ aᵢbᵢ` of the decoded words. -/
def exactQ {p : Model} (ps : List (p.Word × p.Word)) (c : F32) : String :=
  match decode32 c, prepareProducts p ps with
  | some c, some qs => ratStr (c.value + sumQ (qs.map fun (a, b) => a.value * b.value))
  | _, _ => "none"

/-- Evaluate the inner product in block FMAs of size `p.nfma` and print its line; returns the
output value of the last block FMA. -/
def run (id mname : String) (p : Model) (ps : List (p.Word × p.Word)) (c : F32) :
    IO (Option ℚ) := do
  let pre := s!"TC|{id}|{mname}|{p.nfma}|{c.toNat}|{pairsStr ps}"
  match runBlocks p c (blocksOf p.nfma ps) with
  | .ok ts =>
    match ts.getLast? with
    | some t =>
      IO.println s!"{pre}|{t.output.bits.toNat}|{ratStr t.output.value}|{exactQ ps c}"
      return some t.output.value
    | none => IO.println s!"{pre}|ERR empty|none|{exactQ ps c}"; return none
  | .error e =>
    IO.println s!"{pre}|ERR {repr e}|none|{exactQ ps c}"
    return none

/-- The binary32 word of a value, round to nearest (`c = −D1` of the second pass). -/
def word32 (v : ℚ) : F32 := (round32 .nearestEven v).getD 0

/-- Pass 1 from `c = +0`, then pass 2 from `c = −D1`, as `Ozaki.TC.twoPass`. -/
def twoPass (id mname : String) (p : Model) (ps : List (p.Word × p.Word)) : IO Unit := do
  match ← run (id ++ "/pass1") mname p ps 0 with
  | some d1 => let _ ← run (id ++ "/pass2") mname p ps (word32 (-d1))
  | none => pure ()

/-- bf16 word: sign, biased exponent field, mantissa field. -/
def bfw (neg : Bool) (field m : ℕ) : BitVec 16 :=
  BitVec.ofNat 16 ((if neg then 2 ^ 15 else 0) + field * 2 ^ 7 + m)
/-- bf16 `±2^e` (normal). -/
def bf (neg : Bool) (e : ℤ) : BitVec 16 := bfw neg (e + 127).toNat 0
/-- tf19 word: sign, biased exponent field, mantissa field. -/
def tfw (neg : Bool) (field m : ℕ) : BitVec 19 :=
  BitVec.ofNat 19 ((if neg then 2 ^ 18 else 0) + field * 2 ^ 10 + m)
/-- tf19 `±2^e` (normal). -/
def tf (neg : Bool) (e : ℤ) : BitVec 19 := tfw neg (e + 127).toNat 0

def zs {w : ℕ} (n : ℕ) : List (BitVec w × BitVec w) := List.replicate n (0, 0)

/-- BF16 and TF32 models with a given FMA size, number of extra alignment bits and minimum
alignment exponent (the alternative hypotheses). -/
def bfM (K neab : ℕ) (eAlignMin : Option ℤ) : Model := bf16Fp32Model K neab eAlignMin
def tfM (K neab : ℕ) (eAlignMin : Option ℤ) : Model := tf19Fp32Model K neab eAlignMin

#eval show IO Unit from do
  /- 1. Full block FMAs and two passes (ozaki/OzakiTC). -/
  let full7 : List (F16 × F16) := List.replicate 7 (0x67FF, 0x67FF) ++ [(0, 0)]
  let _ ← run "nv-a100-f16-full-block" "ampereF16F32" ampereF16F32 full7 0
  twoPass "nv-a100-f16-two-pass" "ampereF16F32" ampereF16F32 full7
  let full16 : List (F16 × F16) := List.replicate 15 (0x67FF, 0x67FF) ++ [(0x67FF, 0x67FE)]
  let _ ← run "nv-h100-f16-full-block" "hopperF16F32" hopperF16F32 full16 0
  twoPass "nv-h100-f16-two-pass" "hopperF16F32" hopperF16F32 full16
  let wide : List (F16 × F16) :=
    List.replicate 5 (0x67FF, 0x67FF) ++ [(0x3C00, 0x3C00)] ++ List.replicate 2 (0xE7FF, 0x67FF)
  let _ ← run "nv-a100-f16-exact-not-binary32" "ampereF16F32" ampereF16F32 wide 0
  /- 2. Cancellation beyond the old exactness bound (ozaki/OzakiTC/Cancellation.lean). -/
  let _ ← run "nv-a100-f16-cancel-zero" "ampereF16F32" ampereF16F32
    (List.replicate 4 (0x6800, 0x6800) ++ List.replicate 4 (0xE800, 0x6800)) 0
  let _ ← run "nv-a100-f16-cancel-2047" "ampereF16F32" ampereF16F32
    (List.replicate 4 (0x67FF, 0x67FF) ++ List.replicate 3 (0xE7FF, 0x67FF) ++ [(0, 0)]) 0
  let _ ← run "nv-h100-f16-cancel-zero" "hopperF16F32" hopperF16F32
    (List.replicate 8 (0x6800, 0x6800) ++ List.replicate 8 (0xE800, 0x6800)) 0
  /- 3. Non-monotonicity in `c` (tests/TensorCoreTests/TC/Monotonicity.lean). -/
  for (c, tag) in [((0x3f800000 : F32), "c=1"), (0x3f7fffff, "c=1-1ulp"), (0x3f7ffffe, "c=1-2ulp"),
      (0x3f7ffffd, "c=1-3ulp")] do
    let _ ← run s!"nv-v100-f16-nonmonotone/{tag}" "v100F16F32" v100F16F32
      (List.replicate 4 (0x0c00, 0x0c00)) c
    let _ ← run s!"nv-a100-f16-nonmonotone/{tag}" "ampereF16F32" ampereF16F32
      (List.replicate 8 (0x0c00, 0x0800)) c
    let _ ← run s!"nv-h100-f16-nonmonotone/{tag}" "hopperF16F32" hopperF16F32
      (List.replicate 16 (0x0c00, 0x0400)) c
  /- 4. Minimum alignment exponent. A product `2^-140` sets the maximum exponent below the minimum
  alignment exponent `eAlignMin`, so the alignment exponent is `eAlignMin` and the grid is
  `2^(eAlignMin − F)`. A negative product `−2^-j` on that grid is kept (the output drops one
  subnormal ulp below `2^-140`); one step below the grid it is truncated away. -/
  let bfMin (j : ℕ) : List (BitVec 16 × BitVec 16) :=
    [(bf false (-70), bf false (-70)), (bf true (-78), bf false (78 - (j : ℤ)))]
  let tfMin (j : ℕ) : List (BitVec 19 × BitVec 19) :=
    [(tf false (-70), tf false (-70)), (tf true (-78), tf false (78 - (j : ℤ)))]
  for (j, tag) in [(156, "kept"), (157, "dropped")] do
    let id := s!"nv-a100-bf16-min-align-exp-{tag}"
    let _ ← run id "a100BF16F32" a100BF16F32 (bfMin j ++ zs 6) 0
    let _ ← run s!"{id}@alt=no-min-align-exp" "bf16 K=8 F=24 no eAlignMin" (bfM 8 1 none)
      (bfMin j ++ zs 6) 0
    for e in [-131, -133] do
      let _ ← run s!"{id}@alt=min-align-exp{e}" s!"bf16 K=8 F=24 eAlignMin {e}" (bfM 8 1 (some e))
        (bfMin j ++ zs 6) 0
    let id := s!"nv-a100-tf32-min-align-exp-{tag}"
    let _ ← run id "a100TF32F32" a100TF32F32 (tfMin j ++ zs 2) 0
    let _ ← run s!"{id}@alt=no-min-align-exp" "tf32 K=4 F=24 no eAlignMin" (tfM 4 1 none)
      (tfMin j ++ zs 2) 0
    for e in [-131, -133] do
      let _ ← run s!"{id}@alt=min-align-exp{e}" s!"tf32 K=4 F=24 eAlignMin {e}" (tfM 4 1 (some e))
        (tfMin j ++ zs 2) 0
  for (j, tag) in [(158, "kept"), (159, "dropped")] do
    let id := s!"nv-h100-bf16-min-align-exp-{tag}"
    let _ ← run id "hopperBF16F32" hopperBF16F32 (bfMin j ++ zs 14) 0
    let _ ← run s!"{id}@alt=no-min-align-exp" "bf16 K=16 F=25 no eAlignMin" (bfM 16 2 none)
      (bfMin j ++ zs 14) 0
    for e in [-132, -134] do
      let _ ← run s!"{id}@alt=min-align-exp{e}" s!"bf16 K=16 F=25 eAlignMin {e}"
        (bfM 16 2 (some e)) (bfMin j ++ zs 14) 0
    let id := s!"nv-h100-tf32mma-min-align-exp-{tag}"
    let _ ← run id "hopperTF32MmaF32" hopperTF32MmaF32 (tfMin j ++ zs 6) 0
    let _ ← run s!"{id}@alt=no-min-align-exp" "tf32 K=8 F=25 no eAlignMin" (tfM 8 2 none)
      (tfMin j ++ zs 6) 0
    for e in [-132, -134] do
      let _ ← run s!"{id}@alt=min-align-exp{e}" s!"tf32 K=8 F=25 eAlignMin {e}" (tfM 8 2 (some e))
        (tfMin j ++ zs 6) 0
  /- 5. Signed zeros. The model returns `+0` for every zero sum, including `c = −0` with `−0`
  products, where IEEE addition gives `−0`. -/
  for (pid, p) in [("v100F16F32", v100F16F32), ("ampereF16F32", ampereF16F32),
      ("hopperF16F32", hopperF16F32)] do
    let k := p.nfma
    let w (x : BitVec 16) : p.Word := BitVec.ofNat _ x.toNat
    let z (n : ℕ) : List (p.Word × p.Word) := List.replicate n (0, 0)
    let _ ← run s!"nv-{pid}-negzero-products-negzero-c" pid p
      (List.replicate k (w 0x8000, w 0x3C00)) 0x80000000
    let _ ← run s!"nv-{pid}-negzero-products-poszero-c" pid p
      (List.replicate k (w 0x8000, w 0x3C00)) 0
    let _ ← run s!"nv-{pid}-zero-products-negzero-c" pid p (z k) 0x80000000
    let _ ← run s!"nv-{pid}-cancel-to-zero-negzero-c" pid p
      ([(w 0x3C00, w 0x3C00), (w 0xBC00, w 0x3C00)] ++ z (k - 2)) 0x80000000
    /- 6. Subnormal FP16 operands and a subnormal FP32 `c`. -/
    let _ ← run s!"nv-{pid}-subnormal-products" pid p (List.replicate k (w 0x0001, w 0x0001)) 0
    let _ ← run s!"nv-{pid}-subnormal-operand-beside-normal" pid p
      ([(w 0x0001, w 0x7BFF), (w 0x0400, w 0x3C00)] ++ z (k - 2)) 0
    let _ ← run s!"nv-{pid}-subnormal-c-passthrough" pid p (z k) 3
  for (pid, p) in [("a100BF16F32", a100BF16F32), ("hopperBF16F32", hopperBF16F32)] do
    let k := p.nfma
    let w (x : BitVec 16) : p.Word := BitVec.ofNat _ x.toNat
    let z (n : ℕ) : List (p.Word × p.Word) := List.replicate n (0, 0)
    let _ ← run s!"nv-{pid}-subnormal-operand" pid p ((w 0x0001, w (bf false 22)) :: z (k - 1)) 0
    let _ ← run s!"nv-{pid}-subnormal-output" pid p
      ((w (bf false (-126)), w (bf false (-4))) :: z (k - 1)) 0
  /- 7. TF32: exponent range beyond FP16, subnormal TF32 operands. -/
  for (pid, p) in [("a100TF32F32", a100TF32F32), ("hopperTF32MmaF32", hopperTF32MmaF32),
      ("hopperTF32WmmaF32", hopperTF32WmmaF32)] do
    let k := p.nfma
    let pr (a b : BitVec 19) : p.Word × p.Word := (BitVec.ofNat _ a.toNat, BitVec.ofNat _ b.toNat)
    let z (n : ℕ) : List (p.Word × p.Word) := List.replicate n (0, 0)
    let _ ← run s!"nv-{pid}-wide-spread" pid p
      ([pr (tf false 60) (tf false 60), pr (tf false (-60)) (tf false (-60)),
        pr (tf true 60) (tf false 60)] ++ z (k - 3)) 0
    let _ ← run s!"nv-{pid}-small-range" pid p
      ([pr (tf false (-60)) (tf false (-60)), pr (tf false (-61)) (tf false (-62)),
        pr (tf false (-63)) (tf false (-63))] ++ z (k - 3)) 0
    let _ ← run s!"nv-{pid}-above-fp32-max-in-block" pid p
      ([pr (tf false 127) (tf false 0), pr (tf false 127) (tf false 0),
        pr (tf true 127) (tf false 0)] ++ z (k - 3)) 0
    let _ ← run s!"nv-{pid}-overflow" pid p
      ([pr (tf false 127) (tf false 0), pr (tf false 127) (tf false 0)] ++ z (k - 2)) 0
    let _ ← run s!"nv-{pid}-subnormal-operand" pid p
      (pr (tfw false 0 1) (tf false 120) :: z (k - 1)) 0
    let _ ← run s!"nv-{pid}-subnormal-output" pid p
      (pr (tf false (-126)) (tf false (-4)) :: z (k - 1)) 0
  /- 8. H100 TF32 MMA (one block FMA of size 8, F = 25). -/
  let t2047 : BitVec 19 := tfw false 137 1023
  let _ ← run "nv-h100-tf32mma-full-block" "hopperTF32MmaF32" hopperTF32MmaF32
    (List.replicate 7 (t2047, t2047) ++ zs 1) 0
  twoPass "nv-h100-tf32mma-two-pass" "hopperTF32MmaF32" hopperTF32MmaF32
    (List.replicate 7 (t2047, t2047) ++ zs 1)
  let _ ← run "nv-h100-tf32mma-cancel-zero" "hopperTF32MmaF32" hopperTF32MmaF32
    (List.replicate 4 (tf false 11, tf false 11) ++ List.replicate 4 (tf true 11, tf false 11)) 0
  -- FMA-size probe: `2^23 + 2^23 + 1 − 2^23 − 2^23`; block FMAs of size 4 lose the `1` to the FP32
  -- output of the first one.
  let kProbe : List (BitVec 19 × BitVec 19) :=
    [(tf false 12, tf false 11), (tf false 12, tf false 11), (tf false 0, tf false 0), (0, 0),
      (tf true 12, tf false 11), (tf true 12, tf false 11), (0, 0), (0, 0)]
  let _ ← run "nv-tf32-k8-fma-size-probe" "hopperTF32MmaF32" hopperTF32MmaF32 kProbe 0
  let _ ← run "nv-tf32-k8-fma-size-probe@alt=K4-chained (H100 WMMA)" "hopperTF32WmmaF32"
    hopperTF32WmmaF32 kProbe 0
  let _ ← run "nv-tf32-k8-fma-size-probe@alt=K4-chained (A100)" "a100TF32F32" a100TF32F32 kProbe 0
  -- Extra-alignment-bits probe: `c = 1` and products `1.5·2^-25`, kept on the grid `2^-(23+p)` iff
  -- `p ≥ 2`, with `p` extra alignment bits.
  let tp : BitVec 19 × BitVec 19 := (tfw false 115 512, tf false (-13))
  let _ ← run "nv-h100-tf32mma-align-bits-probe" "hopperTF32MmaF32" hopperTF32MmaF32
    (List.replicate 8 tp) 0x3f800000
  for x in [1, 3] do
    let _ ← run s!"nv-h100-tf32mma-align-bits-probe@alt=p{x}"
      s!"tf32 K=8 F={23 + x} eAlignMin -133" (tfM 8 x (some (-133))) (List.replicate 8 tp)
      0x3f800000
  let _ ← run "nv-h100-tf32wmma-align-bits-probe" "hopperTF32WmmaF32" hopperTF32WmmaF32
    (List.replicate 8 tp) 0x3f800000
  let _ ← run "nv-a100-tf32-align-bits-probe" "a100TF32F32" a100TF32F32 (List.replicate 8 tp)
    0x3f800000
  let _ ← run "nv-a100-tf32-align-bits-probe@alt=p2" "tf32 K=4 F=25 eAlignMin -132"
    (tfM 4 2 (some (-132))) (List.replicate 8 tp) 0x3f800000
  let bp : BitVec 16 × BitVec 16 := (bfw false 115 64, bf false (-13))
  let _ ← run "nv-a100-bf16-align-bits-probe" "a100BF16F32" a100BF16F32 (List.replicate 8 bp)
    0x3f800000
  let _ ← run "nv-a100-bf16-align-bits-probe@alt=p2" "bf16 K=8 F=25 eAlignMin -132"
    (bfM 8 2 (some (-132))) (List.replicate 8 bp) 0x3f800000
  let _ ← run "nv-h100-bf16-align-bits-probe" "hopperBF16F32" hopperBF16F32 (List.replicate 16 bp)
    0x3f800000
  for x in [1, 3] do
    let _ ← run s!"nv-h100-bf16-align-bits-probe@alt=p{x}" s!"bf16 K=16 F={23 + x} eAlignMin -133"
      (bfM 16 x (some (-133))) (List.replicate 16 bp) 0x3f800000
  -- The `c` family of the H100 FP16 witness at TF32 MMA's FMA size `8 < 3·2^2`: monotone.
  for (c, tag) in [((0x3f800000 : F32), "c=1"), (0x3f7fffff, "c=1-1ulp")] do
    let _ ← run s!"nv-h100-tf32mma-c-family/{tag}" "hopperTF32MmaF32" hopperTF32MmaF32
      (List.replicate 8 (tf false (-12), tf false (-14))) c

end TargetedTC
