---
title: "5. CDNA 3: global alignment"
description: The block semantics of CDNA 3 (MI300A, MI300X) - products aligned to e_max and truncated, the odd and even groups of FP8, the late addition of c, and fixed-width registers.
---

CDNA 3 aligns its products to their largest exponent `e_max`, truncates them
to a fixed-point grid, adds them exactly, and adds `c` **late**, in a separate
two-operand alignment. This is Algorithm 1 of the paper (`global_alignment`
with `late_partial_sum`). For FP8 the odd- and even-indexed products are
aligned separately first: Algorithm 2 (`odd_even_grouping`). Alignment is
where CDNA 3 loses information, so this page follows it step by step.

## Variants

| Variant | Lean model | Inputs | `N_FMA` | Configuration |
| --- | --- | --- | ---: | --- |
| CDNA 3 FP16 | `cdna3F16` | FP16 | 8 | `globalAlignment` |
| CDNA 3 BF16 | `cdna3BF16` | BF16 | 8 | `globalAlignment` |
| CDNA 3 XF32 | `cdna3XF32` | XF32 (FP32 read as tf19) | 4 | `globalAlignment` |
| CDNA 3 FP8 | `cdna3FP8 fa fb` | any mix of E4M3 and E5M2 FNUZ | 16 | `oddEvenGrouping` |

```lean
def cdna3F16 : Model :=
  { a := .packed fp16, b := .packed fp16, nfma := 8, accumulation := .globalAlignment,
    productOverflow := true }

def cdna3FP8 (fa fb : Format) : Model :=
  { a := .packed fa, b := .packed fb, nfma := 16, accumulation := .oddEvenGrouping,
    late := { cCutoff := some 25 }, productOverflow := true }
```

All four share the features of the paper's table: product alignment
`(2, 24)`, `e_{c=0} = −126`, late `c` with `align(c, S_{p_i,sum}) =
(24, 32, RD)`, round to nearest even, and product overflow at `2^128`. The
FP32 instructions of CDNA 3 are the SFMA ([CDNA 1](/HardwarePrimitives/amd/cdna1/#the-sfma)).

```text
e_max = max{e_{p_i}}  over nonzero products
S_{p_i,sum} = Σ s_{p_i} aligned to e_max, truncated to 24 mantissa bits
e_c = −126 if c = 0
if e_max ≥ e_c:
    s′_c = s_c shifted right by e_max − e_c, rounded down to 24 mantissa bits
    S_acc = S_{p_i,sum} + s′_c
else:
    S′_{p_i,sum} = S_{p_i,sum} shifted right by e_c − e_max, rounded down to 32 mantissa bits
    S_acc = S′_{p_i,sum} + s_c, normalized (subnormal-aware), rounded down to 31 mantissa bits
d = fl{S_acc}
```

## Step 1: the alignment exponent `e_max`

```lean
/-- One step of `e_max`: zero products are skipped. -/
def maxExpStep (acc : Option ℤ) (p : Unpacked) : Option ℤ :=
  if p.m = 0 then acc else some (match acc with | none => p.e | some v => max v p.e)

def maxExp (ps : List Unpacked) : Option ℤ := ps.foldl maxExpStep none
```

- `e_max` is the **largest exponent among the nonzero products**. Zero
  products are skipped, so a zero product never coarsens the grid.
- The exponent of a product is the sum of the input exponents
  ([exact products](/HardwarePrimitives/amd/products/)), so a product with a
  subnormal operand can have a small value and still set `e_max`.
- `c` takes no part: it is aligned later, against the sum of the products.
- If every product is zero, `e_max` is `none`, and `S_acc` is `c`.
- Unlike the Tensor Core models of Ampere and Hopper, the model has no minimum
  alignment exponent.

## Step 2: the grid

The products are aligned with `(2, 23 + padding)`: two integer bits, because a
product's significand lies in `[0, 4)`, and `23 + padding` mantissa bits below
`e_max`. On CDNA 3 `padding = 1`, so the grid step is `2^(e_max − 24)`.

## Step 3: truncation

```lean
/-- Magnitude truncation onto multiples of `2^g`; the sign is kept. -/
def truncGrid (x : ℚ) (g : ℤ) : ℚ :=
  if x < 0 then -(((-x / pow2 g).floor : ℚ) * pow2 g) else ((x / pow2 g).floor : ℚ) * pow2 g

abbrev truncMantissa (x : ℚ) (e : ℤ) (k : ℕ) : ℚ := truncGrid x (e - k)

def alignedSum (padding : ℕ) (ps : List Unpacked) : Option ℤ × ℚ :=
  match maxExp ps with
  | none => (none, 0)
  | some e => (some e, sumQ (ps.map fun p => truncMantissa p.value e (23 + padding)))
```

[`MatrixCore.truncGrid`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/Numerics/Grid.lean#L13)
takes the floor of the **magnitude** and restores the sign, as a
sign-magnitude shifter does. For a negative product this is not rounding down
(toward −∞). `alignedSum` returns `e_max` and the exact sum `S_{p_i,sum}` of
the truncated products. Each truncated product loses less than one grid step:

```lean
theorem alignedSum_error {padding : ℕ} {ps : List Unpacked} {e : ℤ} {S : ℚ}
    (h : alignedSum padding ps = (some e, S)) :
    absQ (sumQ (ps.map Unpacked.value) - S) ≤ ps.length * pow2 (e - (23 + padding : ℕ))
```

## Odd and even groups (FP8, Algorithm 2)

On FP8, the odd-indexed products `p₁, p₃, …` and the even-indexed products
`p₂, p₄, …` are aligned separately, each group to its own largest exponent.
The group with the smaller exponent is then moved to the common `e_max` and
**rounded down** (RD) to `23 + padding` mantissa bits, and the two are added
without normalization:

```lean
def productSum (P : Model) (ps : List Unpacked) : Option ℤ × ℚ :=
  match P.accumulation with
  | .oddEvenGrouping =>
    let odd := alignedSum P.padding (oddIndexed ps)
    let even := alignedSum P.padding (evenIndexed ps)
    match joinExp odd.1 even.1 with
    | none => (none, 0)
    | some e => (some e, rdMantissa odd.2 e (23 + P.padding) + rdMantissa even.2 e (23 + P.padding))
  | _ => alignedSum P.padding ps
```

The group that holds `e_max` is already on that grid, so only the other group
loses bits. Because the groups are formed by position, the order of the
products matters on FP8.

## Late accumulation of `c`

`c` is added to `S_{p_i,sum}` in a separate two-operand alignment,
`align(c, S_{p_i,sum}) = (24, 32, RD)` (Algorithm 1, lines 3–11):

```lean
def shiftedC (P : Model) (eMax eC : ℤ) (c : Unpacked) : ℚ :=
  match P.late.cCutoff with
  | some n => if eMax - eC > n then 0 else rdMantissa c.value eMax P.late.cMantissaBits
  | none => rdMantissa c.value eMax P.late.cMantissaBits

def shiftedSum (P : Model) (eC : ℤ) (pSum : ℚ) (c : Unpacked) : ℚ :=
  normalizeRD P.late.accMantissaBits (rdMantissa pSum eC P.late.sumMantissaBits + c.value)

def lateSum (P : Model) (eMax : Option ℤ) (pSum : ℚ) (c : Unpacked) : ℚ :=
  match cExp P c with
  | none => pSum
  | some eC =>
    match eMax with
    | some e => if eC ≤ e then pSum + shiftedC P e eC c else shiftedSum P eC pSum c
    | none => shiftedSum P eC pSum c

def alignedAccumulation (P : Model) (x : Prepared) : ℚ :=
  let s := productSum P x.p
  lateSum P s.1 s.2 x.c
```

- The operand with the smaller exponent loses bits, by **rounding down**,
  not by truncation.
- On FP8, `s′_c = 0` once `e_max − e_c > 25` (`cCutoff`), a truncation
  instead of a round down.
- `c` never sets the products' alignment.

## A fixed-width register model

Exact accumulation is a modeling choice, so the library also models the
product accumulation as a register would perform it: `w`-bit two's-complement
additions that wrap on overflow, one aligned product at a time, with the
odd/even shift of Algorithm 2 an arithmetic right shift, which rounds down:

```lean
/-- The aligned significands of the products as integers: steps of `2^(e − 23 − padding)`. -/
def alignedBits (padding : ℕ) (e : ℤ) (ps : List Unpacked) : List ℤ :=
  ps.map fun p => truncBits p.value (e - (23 + padding : ℕ))

/-- Modular `w`-bit additions, starting from the register `acc`. -/
def machineAccumulate (w : ℕ) (acc : BitVec w) : List ℤ → BitVec w
  | [] => acc
  | z :: zs => machineAccumulate w (acc + BitVec.ofInt w z) zs

def evalBlockMachine (w : ℕ) {P : Model} (x : BlockInput P) : Except ModelError (BlockTrace P)
  -- identical to evalBlock, but accumulates the products with machineAccumulate w
```

Each aligned product has at most `23 + padding + 2` magnitude bits, and there
are `N_FMA` of them, so those bits, plus `⌈log₂ N_FMA⌉` carry bits, plus one
sign bit, are always enough:

```lean
theorem evalBlockMachine_eq {P : Model} (x : BlockInput P) (w carryBits : ℕ)
    (hcount : P.nfma ≤ 2 ^ carryBits) (hw : P.alignMantissaBits + 2 + carryBits + 1 ≤ w) :
    evalBlockMachine w x = evalBlock x
```

| Theorem | Model | Register width |
| --- | --- | --- |
| `cdna3F16_machine_eq` | FP16, `N_FMA = 8` | 30 bits |
| `cdna3BF16_machine_eq` | BF16, `N_FMA = 8` | 30 bits |
| `cdna3XF32_machine_eq` | XF32, `N_FMA = 4` | 29 bits |
| `cdna3FP8_machine_eq` | FP8, `N_FMA = 16`, any mix of formats | 31 bits |

These hold for **every** encoded input, and the tests show they are needed:
eight FP16 products just below 4 wrap in a 29-bit register.
[`MatrixCore.machinePrefix_exact`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/MachineRefinement.lean#L185)
adds that every **prefix** of the accumulation is exact at that width, so the
result does not depend on the order of the additions, even with cancellation.
The exact accumulator is a sound abstraction of any adder at least this wide;
the model does not assume which width a particular GPU uses.

## Example: a small product disappears

CDNA 3 FP16, `c = 0`, one product `1.5 × 1.5` (`e_p = 0`) and one product
`2^-12 × 2^-12 = 2^-24` (`e_p = −24`): `e_max = 0`, the grid is `2^-24`, and the
small product is kept. Write the large product as `2.25 × 1` instead
(`e_p = 1`): the grid becomes `2^-23`, and the small product is truncated away
although the large product has the same value.
[The worked trace](/HardwarePrimitives/amd/#a-worked-trace) follows a block of
this kind through every stage.

The [CDNA 3 properties](/HardwarePrimitives/amd/properties/cdna3/) bound the
losses of each step, characterize when a rising product lowers the output,
and say exactly how much of the order of the products matters.
