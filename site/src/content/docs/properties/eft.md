---
title: TC-EFT correction
description: Does TC-EFT work? What it recovers, its fast path and exact fallback, and what its guarantees do and do not say.
---

TC-EFT is the algorithm of the **TC-EFT paper** (*TC-EFT: Characterizing and
Correcting Tensor Core Arithmetic*), Section IV. It takes the encoded inputs
of one block and a finite FP32 word `D`, normally the Tensor Core's output. It
returns the exact sum `S = C + Σ aᵢ·bᵢ` rounded to the nearest FP32 value
(ties to even).

## Does it work?

**Yes.** Lean proves that whenever TC-EFT returns a value, that value is the
exact sum `S` correctly rounded to FP32. It returns a value exactly when that
rounded sum is a finite FP32 number. The fixed-size 576-bit implementation is
proved to return the same bits.

The caveats below never involve a wrong answer. They concern **which of two
routes** produces the answer (a fast FP32 path or a slower exact fallback), and
**what the proofs do and do not cover**.

## What it recovers, in bits

The Tensor Core [aligns](/MMAlgebra/model/alignment/) every term to the bit
position of the largest exponent and **drops every bit below its lowest kept
bit**. Then it [truncates](/MMAlgebra/model/normalization/) the sum to FP32's 24
significant bits. TC-EFT puts those dropped bits back.

1. **Pick a cut-off bit.** This is whichever is higher: the lowest bit the
   Tensor Core kept during alignment, or the lowest bit of `D`.
2. **Split every term at the cut-off** into its *high bits* (at or above it)
   and its *low bits* (below it). The low bits of each term are exactly what
   was lost or is not visible in `D`.
3. **Sum the high bits** to get `H`. `H` and `D` agree except in a few
   overlapping bits. Their difference is the *overlap* `εₒ = D − H`.
4. **Add the low bits back:** `S = D − εₒ + (sum of all low bits)`, which is
   just `H + (sum of all low bits)`. Then round once to FP32.

```lean
theorem overlap_recovery (t : BlockTrace) : ...   -- S = D − εₒ + Σ low parts
```

The identity in step 4 holds for **any** `D`, because `εₒ` is defined as
`D − H`. On its own it is bookkeeping. The real work is computing the final
sum cheaply without losing bits.

## Two ways to finish

### The fast path: plain FP32 additions

If every intermediate result fits in FP32 without losing a bit, the sum can
be finished with ordinary FP32 additions. Only the last addition rounds.
TC-EFT runs a check first. The fast path is used only if all of these hold:

- **The low bits of all terms fit together within 24 bits.** Measured from
  the lowest low bit present, the low parts need fewer than 24 bits in total,
  so adding them in FP32 never drops a bit.
- **Those bits sit inside FP32's exponent range:** the lowest one is no lower
  than `2^-149` (FP32's smallest subnormal bit), and the span of these bits
  does not reach past `2^128`.
- **`D`, the overlap `εₒ`, and `H` each fit in FP32's 24 significant bits.**
- **The final result is within FP32's range.**

```lean
theorem scalarCorrected_correct ...   -- check passes ⇒ fast path returns RNE(S)
```

The key lemma is that adding numbers in FP32 is exact when all their bits fit
within one span of 24 bits (`naiveSumBinary_exact_of_bitSpan`).

### The exact fallback: a wide fixed-point register

If the check fails, TC-EFT adds all the bits in a register wide enough to hold
every bit of every term. The reference version uses exact rationals; the
implementation uses a **576-bit** fixed-point word whose lowest bit is
`2^-272`. It then rounds once to FP32. This fallback always gives the right
answer, but it is slower.

```lean
theorem tcEftEncoded_correct ...         -- any returned value is RNE(S)
theorem tcEftEncoded_bits_isSome_iff ... -- a value is returned iff RNE(S) is finite
theorem EFMachine.tcEft_success ...      -- the 576-bit word never overflows on supported inputs
theorem EFMachine.tcEft_agrees ...       -- 576-bit and reference versions return the same bits
theorem EFMachine.tcEftWithLean_eq ...   -- using Lean's native Float32 additions changes nothing
```

## The caveats, plainly

**1. The result doesn't depend on `D` being the Tensor Core's output.**
The proofs work for any finite `D`. So TC-EFT's *correctness* does not rely on
the Tensor Core model matching the hardware: the answer is always the
correctly rounded exact sum of the inputs. What a good `D` buys is
*speed*: when `D` is the real Tensor Core output, `H` and `D` overlap in only
a few bits, so the fast path usually applies.

**2. The fast path doesn't always apply.** How often depends on how spread
out the inputs' exponents are:

| Inputs | Fast path taken |
| --- | --- |
| Recorded GPU vectors from *Accurate Models* | 5,000 / 5,000 on each GPU |
| Values near 1 | 1,000 / 1,000 on each GPU |
| Application-like inputs | 74–99% |
| Uniformly random bit patterns (exponents spread over the whole range) | 86 (V100), 24 (A100), 1 (H100) out of 1,000 |
| The TC-EFT paper's validation suites | 290 of 2,459 finite cases |

When the fast path is not taken, the exact fallback gives the answer.

**3. The fast-path check uses the tightest grid.** To judge whether the low
bits fit in 24 bits, the check measures from the *lowest bit actually set*
in the low parts and ignores zero terms. This is the tightest choice for this
kind of check: any valid grid must lie at or below that bit, and choosing that
bit leaves the most room within the 24 bits. The reference version, the 576-bit
version, and the TC-EFT paper's own test generator (`grid_predicate`) all use
this rule. On the paper's validation suites the reference version now takes
the fast path in exactly the cases the paper's generator does, and the test
suite checks this.

(Earlier versions of the reference check measured from the lowest bit each
term *could* have, given its format, and counted zero terms. That was safe
but stricter than necessary. It disagreed with the paper's generator in 27
cases, and was changed.)

**4. Passing the check guarantees the fast path.** In the 576-bit
implementation the fast path is plain FP32 operations, with no run-time
comparisons against exact values. Lean proves that whenever the check passes,
every FP32 step is exact, so the fast path is taken and returns the correctly
rounded sum (`EFMachine.Components.scalar_of_guard`).

**5. The paper's input-based precondition covers part of the check.** The
TC-EFT paper's inequality (17) bounds the bit span from the inputs alone. For
FP32 correction, `ExtractionGrid.inputGrid_scalarPredicate_fp32` derives five
of the check's nine conditions from it and assumes the other four: a grid no
lower than `2^-149`, the overlap and `H` fitting in FP32, and the sum being in
range. These four depend on the particular sum, not only the input bound. A
concrete block satisfies all of them, checked in Lean.

**6. No answer when the sum is too large for FP32.** If the exact sum rounds
beyond FP32's largest finite value, TC-EFT returns no result rather than
infinity, matching the finite scope of the [model](/MMAlgebra/model/scope/).
