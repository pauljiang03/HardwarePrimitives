---
title: Related work and novelty
description: Where the Lean formalization of the Ozaki schemes sits in the literature on GEMM emulation, correctly rounded and reproducible linear algebra, matrix-multiplier numerics and formal verification, and which of its results are new.
---

This page places the [Ozaki formalization](/MMAlgebra/ozaki/) in the literature.
It is based on a review done in October 2026. For each source it notes how
closely it was read: **full** text, **abstract** only, or a **snippet** or
secondary source. Sources not read in full may contain more than is
credited here.

## The literature

### The Ozaki scheme family and GEMM emulation

- **Ozaki, Ogita, Rump and Oishi, NOLTA 2007** (full),
  [*Accurate matrix multiplication with multiple floating-point numbers*](https://www.tuhh.de/ti3/paper/rump/OzOgRuOi07.pdf).
  Faithfully rounded matrix products from error-free transformations; the
  method works adaptively, generating terms until faithful rounding is
  guaranteed.
- **Ozaki, Ogita, Rump and Oishi, NOLTA 2008** (full),
  [*Accurate matrix multiplication by using level 3 BLAS operation*](https://www.tuhh.de/ti3/paper/rump/OzOgRuOi08.pdf).
  The first splitting of matrices so that products of slices are exact in any
  summation order.
- **Ozaki, Ogita, Oishi and Rump, Numerical Algorithms 59 (2012)** (full, the
  authors' [preprint](https://www.tuhh.de/ti3/paper/rump/OzOgOiRu11.pdf)),
  [*Error-free transformations of matrix multiplication by using fast routines of matrix multiplication and its applications*](https://doi.org/10.1007/s11075-011-9478-1).
  The canonical Ozaki scheme (Ozaki-I), in two forms: a complete split
  followed by an accurate summation that gives signs, faithful or nearest
  results (§2.4), or a fixed number of splits with an a-priori error bound
  (§3–4). Neither stops early or uses its bound to decide a rounded result.
- **Ozaki, Ogita and Oishi, NLAA 2011** (abstract; paywalled) **and 2016**
  (full, accepted manuscript): tight enclosures of matrix products with
  optimized BLAS (2011); in 2016, "a posteriori validation" that every slice
  product was error-free, using deliberate overflow to detect rounding, and
  enclosures compared by width. Neither, as far as read, uses an enclosure to
  decide a rounded result.
- **Ozaki, SWIM 2018** (full, [slides](https://www.com.uni-rostock.de/storages/uni-rostock/Alle_MSF/COM/Bilder/SWIM/Presentations/ozaki.pdf)),
  and **Lange and Rump** (full, [preprint](https://www.tuhh.de/ti3/paper/rump/MatrixResidualsFinal.pdf)):
  midpoint-radius enclosures of a truncated Ozaki product, and remarks that an
  accurate summation of the slices gives correct rounding.
- **Mukunoki, Ozaki, Ogita and Imamura, ISC 2020** (full, formulas not rendered),
  [*DGEMM using Tensor Cores, and its accurate and reproducible versions*](https://pmc.ncbi.nlm.nih.gov/articles/PMC7295351/).
  FP16 Tensor Core GEMM by Ozaki-I, with a correctly rounded mode that splits
  until every split matrix is zero and sums with a correctly rounded summation,
  about four times slower than its FP64-accuracy mode. It has no rounding test
  and no early exit. **OzBLAS** (abstracts:
  [SC18 workshop](https://sc18.supercomputing.org/proceedings/workshops/workshop_pages/ws_cre104.html),
  [project](https://www.r-ccs.riken.jp/labs/lpnctrt/projects/ozblas)) offers
  reproducible BLAS with tunable accuracy, and an HPC Asia 2021 paper
  (abstract) gives correctly rounded, bitwise reproducible inner products across
  CPU and GPU.
- **Integer matrix multipliers** (abstracts): Ootomo, Ozaki and Yokota, IJHPCA 2024
  ([ozIMMU](https://arxiv.org/abs/2306.11975)); Uchino, Ozaki and Imamura,
  IJHPCA 2025 ([arXiv:2409.13313](https://arxiv.org/abs/2409.13313)).
- **Ozaki-II** (keyword search of the full text), Ozaki, Uchino and Imamura,
  [arXiv:2504.08009](https://arxiv.org/abs/2504.08009): CRT reconstruction,
  with a rounding-error analysis left to future work. Follow-ups:
  an [error analysis](https://arxiv.org/abs/2602.02549) (full, machine
  extraction) assuming exact INT8 products,
  [FP8 Ozaki-II](https://arxiv.org/abs/2603.10634),
  and [complex CRT](https://arxiv.org/abs/2512.08321) (full text, relevant
  section), whose CUDA and HIP back ends are argued to be bitwise
  reproducible across runs when the `log2` computation is identical; and the
  [GEMMul8](https://github.com/UCHINO-Yuki/GEMMul8) library (README).
  Kawakami and Takahashi ([arXiv:2606.29129](https://arxiv.org/abs/2606.29129),
  keyword reading) prove a scaling that always satisfies the CRT uniqueness
  condition. Kouya ([arXiv:2609.27831](https://arxiv.org/abs/2609.27831),
  keyword reading) runs Ozaki-II on CPUs with guard bits that make results
  "essentially correctly rounded" (within 1 ulp), with Inf and NaN treated as
  0; there is no rounding test.
- **Abdelfattah, Dongarra, Fasi, Mikaitis and Tisseur** (full, machine
  extraction), [arXiv:2506.11277](https://arxiv.org/abs/2506.11277): error
  analysis of Ozaki-I on integer units, a slice-count estimator, and a note that
  −0, Inf and NaN are not handled.
- **ADP and ESC**, Schwarz et al. (full, machine extraction),
  [arXiv:2511.13778](https://arxiv.org/abs/2511.13778): FP64 emulation on INT8
  with an exponent-span estimate and a native fallback. Grade A (a
  componentwise bound linear in `k`) is established by experiment, and the
  coarsening is argued by a short sketch that does not treat zeros. It ships in
  cuBLAS ([NVIDIA blog](https://developer.nvidia.com/blog/unlocking-tensor-core-performance-with-floating-point-emulation-in-cublas/)),
  and CUDA 13.4 adds Ozaki-II.
- **Mazumder, Calotoiu and Hoefler**, Sept 2026 (full),
  [arXiv:2609.37693](https://arxiv.org/abs/2609.37693),
  *FP64 is all you want, INT8 is all you need, FP4/6/8 is all you have*: CRT
  emulation framed as returning `fl(AB)` when the conversion is lossless, with
  exactness resting on an accumulator bound and a window inequality; a lower
  bound on the window a residue-only decoder needs even for a faithful
  result; and an "exact emulation" that returns `fl(AB)` by widening the
  window, for operands of bounded dynamic range. It notes that exactness may
  rely on undocumented accumulation. Pen and paper, NVIDIA Blackwell only; an
  extended version with proofs is announced.
- **Demmel, Henry, Kozachenko, Langou, Li, Riedy and Vanover**, Sept 2026
  (full), [*How to grade the accuracy of the BLAS*](https://arxiv.org/abs/2609.12307):
  defines Grade A as `|E| ≤ f(n) ε |A||B|`; ozIMMU and GEMMul8 earn B, and
  cuBLAS 13.3 with Ozaki-I emulation earns A empirically, including an
  underflow test, because cuBLAS detects the wide range and uses its FP64
  path. Which exponent-range criterion makes Grade A apply is left open, as
  are exception and subnormal tests.
- **Further emulation work, 2025–26**:
  Mukunoki's [FP8 Tensor Core Ozaki with integer FP64 emulation](https://arxiv.org/abs/2508.00441)
  (full), bitwise identical to FP64 but without overflow, underflow or
  subnormal handling; NVIDIA's [BF16x9 SGEMM](https://arxiv.org/abs/2605.16617)
  (full), which handles subnormals and saturates Inf, with no proof;
  [FP4 limbs](https://arxiv.org/abs/2608.06812) (full);
  [BF16 on Intel AMX](https://arxiv.org/abs/2609.04663) and
  [EmuGEMM](https://arxiv.org/abs/2606.25453) (abstracts); Matsuoka's
  [*FP8 is all you need*](https://arxiv.org/abs/2606.06510) and
  [*Ozaki 2.5*](https://arxiv.org/abs/2609.09095) (keyword reading, and
  *Ozaki 2.5*'s Appendix A in full), which use Grade-A contracts but list the
  truncation-mode accuracy and the ESC/ADP escalation as validation
  obligations rather than results, and whose "machine-checked" means a numeric
  consistency suite.
- **Multiword Tensor Core methods**: Markidis et al. 2018
  ([arXiv:1803.04014](https://arxiv.org/abs/1803.04014), abstract), Henry, Tang
  and Heinecke 2019 (snippet), Ootomo and Yokota 2022
  ([arXiv:2203.03341](https://arxiv.org/abs/2203.03341), abstract), which
  traces Markidis's accuracy loss to round-toward-zero accumulation inside the
  Tensor Core.

### Correctly rounded, faithful and reproducible linear algebra

- **Ogita, Rump and Oishi**, SISC 2005, and **Rump, Ogita and Oishi**, SISC
  2008, Parts [I](https://www.tuhh.de/ti3/paper/rump/RuOgOi07I.pdf) and
  [II](https://www.tuhh.de/ti3/paper/rump/RuOgOi07II.pdf) (full). The 2005
  paper gives accurate dot products with rigorous enclosures, but no rounding
  decision. Part I's AccSum repeats extraction, the splitting Ozaki uses,
  until the sum is provably faithfully rounded (a magnitude criterion, proved
  optimal). Part II's NearSum decides round to nearest from the sign of the
  sum relative to the midpoint next to a faithful result, and stops early
  when that is already decided. These are the closest prior forms of an
  early-exit rounding test, for summation rather than Ozaki products.
- **ExBLAS**, Iakymchuk, Defour, Collange and Graillat (snippet,
  [paper](https://www-pequan.lip6.fr/~graillat/papers/IDCG16.pdf)): GPU GEMM
  with floating-point expansions and a long accumulator, described as correctly
  rounded. **ReproBLAS**, Demmel, Nguyen and Ahrens (snippet): reproducible but
  not correctly rounded. **Kulisch's** long accumulator (snippet).
- **Boldo and Melquiond, IEEE TC 2008** (abstract,
  [HAL](https://hal-ens-lyon.archives-ouvertes.fr/inria-00080427)): correctly
  rounded sums by rounding to odd, proved in Coq.
- **Ziv's rounding test** (Ziv 1991, metadata; de Dinechin, Lauter, Muller and
  Torres 2013, [abstract](https://hal-ens-lyon.archives-ouvertes.fr/ensl-00693317))
  and CORE-MATH (snippet).
- **Cross-vendor reproducibility, 2026**: Yang, Riasanovsky, Deng and Sarkar
  ([arXiv:2609.11356](https://arxiv.org/abs/2609.11356), partial), sound
  static checkers for bitwise equivalence spanning NVIDIA PTX and AMD GCN,
  treating an MMA as one rounding and not covering emulation; and
  [NVIDIA versus AMD logit mismatches](https://arxiv.org/abs/2610.05458)
  (partial), which does not treat Ozaki emulation.
- **Open questions in the field**: a mixed-precision survey
  ([arXiv:2609.37137](https://arxiv.org/abs/2609.37137), keyword reading)
  lists how emulation should detect and propagate infinities, negative zero
  and NaN, and whether it should aim for cross-vendor reproducibility, as
  open.
- **Interval products on Tensor Cores**: Ozaki, Ogita and Mukunoki, REC 2021
  ([paper](https://rec2021.unime.it/papers/REC2021-18.pdf), abstract and
  keyword reading): an enclosure of the product by error-free transformation
  on Tensor Cores, without a rounding decision.

### Matrix-multiplier numerics and models

- **Fasi, Higham, Mikaitis and Pranesh**, PeerJ CS 2021 (snippet,
  [paper](https://peerj.com/articles/cs-330)): truncation, accumulation
  without normalization and the first observation of non-monotonicity. **Blanchard et
  al.**, SISC 2020 (snippet): block-FMA error analysis. **Mikaitis**, IEEE TC 2024
  ([arXiv:2304.01407](https://arxiv.org/abs/2304.01407), snippet): monotonicity
  of multi-term adders.
- **Feature-targeted testing**, Li et al., CCGrid 2024
  ([arXiv:2403.00232](https://arxiv.org/abs/2403.00232), abstract).
- **Valpey, Li, Pai and Gopalakrishnan**, NFM 2025 (full, machine extraction,
  [arXiv:2502.15999](https://arxiv.org/abs/2502.15999)): an SMT model of
  Volta, Turing and Ampere Tensor Cores, and an SMT analysis of the Markidis and
  Ootomo–Yokota correction algorithms; the closest formal work on emulation.
- **Bit-accurate models**: Khattak and Mikaitis for NVIDIA
  ([arXiv:2512.07004](https://arxiv.org/abs/2512.07004)) and Khattak,
  Mikaitis and Graziani for AMD CDNA 1–3
  ([arXiv:2609.14845](https://arxiv.org/abs/2609.14845)), which this
  repository's models follow and which compare multiword emulation across
  vendors by simulation; MMA-Sim for ten architectures
  ([arXiv:2511.10909](https://arxiv.org/abs/2511.10909), abstract).
- **FP8 accumulation**: Khattak and Mikaitis's model (v4) gives FP8
  accumulation as `13` fractional bits on H100 `wgmma` and `25` on B200; the
  DeepSeek-V3 report ([arXiv:2412.19437](https://arxiv.org/abs/2412.19437),
  snippet) observed about 14 bits on H800. None of the bit-accurate model
  papers evaluates Ozaki or ADP slice exactness.
- **Non-monotonicity**: Jiang and Zheng, SC25 poster,
  [*A formal characterization of non-monotonicity in Tensor Cores*](https://sc25.supercomputing.org/proceedings/posters/poster_pages/post148.html)
  (abstract).

### Formal verification of floating point

- **Coq**: Flocq, which proves monotonicity of rounding to nearest from the
  nearest-value property alone (`Rnd_N_pt_monotone`); Gappa; proofs of
  error-free transformations (Boldo, Graillat and Muller, TOMS 2017); and
  double-word arithmetic (Muller and Rideau, TOMS 2022), which found errors in
  published proofs (snippets).
- **Verified linear algebra**: VCFloat2 and
  [LAProof](https://www.cs.princeton.edu/~appel/papers/LAProof.pdf)
  (snippets), machine-checked accuracy bounds for dot and matrix products.
- **Hardware**: HOL Light at Intel and ACL2 (Russinoff), including an ACL2
  proof of the Chinese remainder theorem (snippets).
- **Lean**: FloatLib ([arXiv:2609.19352](https://arxiv.org/abs/2609.19352),
  keyword reading), certified word and limb kernels and exact quire
  accumulation, with nothing on GEMM or matrix multipliers; FLoPS for P3109 formats
  ([arXiv:2602.15965](https://arxiv.org/abs/2602.15965), abstract), which
  studies ExtractScalar, the σ-split; round-to-odd ExtractScalar
  ([arXiv:2601.17198](https://arxiv.org/abs/2601.17198), abstract).
- **The Ozaki schemes, CRT emulation and ADP**: no machine-checked treatment
  was found beyond SMT models, despite searches (October 2026) combining Coq,
  Lean, Isabelle, SMT and "machine-checked" with Ozaki, CRT, ADP and GEMM
  emulation, and the 2026 programs of FMCAD, NFM, Correctness, ARITH and MICRO.
  No paper after Valpey et al. was found from the group behind the SMT models.
  To watch: Hubrecht and Melquiond, *Verifying code that uses error-free
  transformations* (ARITH 2026, title only), and the announced extended
  version of Mazumder, Calotoiu and Hoefler with proofs.

## What is new here

| Contribution | Verdict | Closest prior work | The difference |
| --- | --- | --- | --- |
| Machine-checked Ozaki-I, Ozaki-II and ADP/ESC for every input | New | SMT models; Valpey et al.; pen-and-paper analyses | All-input proofs in an interactive prover with only standard axioms |
| Exactness of the matrix multiplier derived from validated bit-level NVIDIA and AMD models | New as a proof | The exactness condition on paper; the hardware models, which do not treat Ozaki | The schemes' assumption of an exact matrix multiplier is proved from hardware semantics |
| The `2^24` exactness bound comes from the binary32 output | Known rule | Ozaki's slice-width formula; Mukunoki et al. 2020 | Proved per variant; new only relative to a matrix multiplier that rounds every partial sum |
| Full block FMAs of `11`-bit products on A100 and H100 exceed it; bf16 needs `8`-bit slices | Mostly known | The same slice-width formula | Concrete, proved witnesses |
| NVIDIA and AMD give different wrong answers past the exactness bound | Partly new | Cross-vendor studies by testing and simulation | Proved, Ozaki-specific witnesses |
| σ-split remainder exact for every binary32 value and grid; slicing on integer significands for every grid | Modest | ExtractScalar analyses; FLoPS | Machine-checked binary32 statements with explicit ranges |
| Ozaki-I error identity and bounds; Ozaki-II truncation bound; native dot-product bounds | New as machine-checked results | Ozaki 2012; Abdelfattah et al. 2025; Uchino et al. 2026; Jeannerod and Rump 2013 | The sharpest published bounds that apply here, proved: an entrywise Ozaki-I bound of Abdelfattah et al.'s shape, Uchino et al.'s truncation bound without its cross term (truncation toward zero), and Jeannerod–Rump's `k·u` |
| ADP: coarsening for every block size, Grade A for the whole routine, a subnormal counterexample, a guarded fix | New | Schwarz et al. (experiments, sketch) | First proof of a linear componentwise bound for the routine, and a failure the experiments did not exercise |
| Correctly rounded versions: Ziv's rounding test on enclosures, refinement, exact fallback on the matrix multiplier, bounded registers, IEEE special values | Partly new | Mukunoki et al. 2020 (full split); Ozaki et al. 2007 (adaptive faithful); AccSum and NearSum (Rump–Ogita–Oishi 2008, summation); Ziv's test; SWIM 2018 and Lange–Rump enclosures | An early-exit rounding test on truncated Ozaki-I, its extension to Ozaki-II and ADP, and a machine-checked proof on hardware models |
| Identical results on the NVIDIA and AMD models | Partly new | GEMMul8; HPC Asia 2021 (CPU and GPU); ExBLAS | A proved statement over two vendors' matrix-multiplier models |
| The exact condition for a call to the matrix multiplier, with cancellation and per-architecture differences (CDNA 2's pairwise sums) | New as proofs | The slice-width rule; Fasi et al.'s and Khattak–Mikaitis's measurements of alignment and accumulation | Necessary and sufficient on the models, not a scheduling rule |
| The cheapest exact configuration per GPU (`10`-bit slices filling the block FMA on A100, H100 and CDNA 3) | Known rule, proved | The slice-width rule `k · 2^(2b) ≤ 2^24` with the FMA size | Every candidate proved exact; evidence that two passes do not pay by instruction count |
| Fixed-width integer forms of all three correctly rounded schemes, with one theorem bounding every register | New, as far as found | Correctly rounded summation in fixed precision (AccSum, NearSum, long accumulators) | Registers whose widths do not depend on the inputs' exponents, machine-checked |
| Two passes through `C` recover a full block FMA exactly | New, as far as found | TwoProdFMA and Boldo–Muller's exact FMA error (scalar); TC-EFT's analysis of alignment | The matrix-instruction analogue, for a multi-term truncating adder, proved on the model; by instruction count, narrower slices are cheaper |

### How this differs from the most recent work

The papers and tools of 2025–26 closest to this work, what each does, what
this work adds, and what each has that this work does not.

| Work | What it does | What this work adds | What it has that this work does not |
| --- | --- | --- | --- |
| **Ozaki-II** (Ozaki, Uchino and Imamura 2025) and its error analysis (2026) | CRT-based emulation on INT8 matrix multipliers; the analysis assumes exact INT8 products | Ozaki-II machine-checked on fp16, bf16 and tf32 Tensor Cores and AMD matrix cores, with the exactness of the matrix multiplier proved from the hardware models instead of assumed, and a correctly rounded version | Implementations and performance on INT8 hardware; complex, FP8 and improved-scaling variants |
| **GEMMul8** (Uchino et al.) | CUDA and HIP library for Ozaki-II GEMM, bitwise reproducible | A proof that the NVIDIA and AMD models return identical results, which are also the correctly rounded ones, not only reproducible | A working library on real GPUs |
| **ADP** (Schwarz et al. 2025, in cuBLAS) | FP64 emulation on INT8 with an exponent-span estimate and a native fallback; Grade A shown by experiment | Grade A proved for the whole routine; a subnormal counterexample and a guardrail that fixes it; the coarsening for every block size; every Z3 test-level check; Inf and NaN results; a correctly rounded version | The production implementation, on real INT8 Tensor Cores (here an idealized INT8 matrix multiplier, [issue #2](https://github.com/pauljiang03/MMAlgebra/issues/2)) |
| **Abdelfattah, Dongarra, Fasi, Mikaitis and Tisseur** (2025) | Error analysis of Ozaki-I on integer units and a slice-count estimator; −0, Inf and NaN not handled | Machine-checked bounds of the same shape for our splitting; IEEE special values handled, with proofs; correct rounding | A slice-count estimator (here: their accumulation by levels and different slice counts per matrix, proved in our splitting; their spare-carry recursion formalized, with a level's size read as a count of diagonals) |
| **Uchino, Ozaki and Imamura** (2026, Ozaki-II error analysis) | Error bounds for Ozaki-II | Their truncation bound machine-checked, without its cross term for truncation toward zero; correct rounding | Their exhaustively checked scaling slack, taken here as a hypothesis (here: their reconstruction algorithm and constant R64 proved in their setting, and their scaling's Lemma 1) |
| **Mazumder, Calotoiu and Hoefler** (Sept 2026) | CRT emulation targeting `fl(AB)`, a lower bound on the CRT window, and an "exact emulation" for bounded dynamic range by widening the window | Correct rounding for every input, not only bounded dynamic range: a cheap rounding test decides most entries and a proved exact fallback the rest; exactness derived from hardware models rather than assumed; AMD and special values | A lower bound on the window; Blackwell measurements |
| **Demmel et al.** (Sept 2026, grading the BLAS) | Grade A defined; cuBLAS's Ozaki-I emulation earns A empirically, the research codes B; the exponent-range criterion for Grade A left open | Grade A proved for the ADP routine as formalized, the exponent condition it needs, a subnormal input that breaks it, and a guardrail that restores it | Empirical grades of shipping libraries, including cuBLAS, which passes their underflow test |
| **FP8 and FP4 emulation** (2025–26: FP8 Tensor Cores, FP8 Ozaki-II, FP4 limbs, *Ozaki 2.5*) | Emulation on lower-precision matrix multipliers | — | Coverage of FP8 and FP4 matrix multipliers, which this work defers |
| **Valpey, Li, Pai and Gopalakrishnan** (NFM 2025) | SMT models of Volta, Turing and Ampere Tensor Cores; SMT analysis of the Markidis and Ootomo–Yokota corrections | Proofs for every input and every length in an interactive prover, for the Ozaki schemes, on NVIDIA and AMD | SMT automation, and the multiword correction algorithms |
| **Khattak and Mikaitis** (2025, NVIDIA) and **Khattak, Mikaitis and Graziani** (2026, AMD) | Bit-accurate models; multiword emulation compared across vendors by simulation | Theorems on models that follow theirs, for every input, for the Ozaki schemes | Wider architecture coverage, and simulation of multiword methods |
| **Cross-vendor reproducibility** (2026: bitwise-equivalence checking, NVIDIA versus AMD mismatches) | Detecting and measuring result mismatches between vendors | Proved identical correctly rounded Ozaki results on the two vendors' models, and proved witnesses where naive configurations differ (NVIDIA truncates, AMD rounds) | Measurements on real workloads and hardware |
| **Mukunoki, Ozaki, Ogita and Imamura** (ISC 2020), the correctly rounded baseline | Correctly rounded Ozaki GEMM on Tensor Cores by a complete split and correctly rounded summation, about four times slower | An early exit: a proved rounding test decides most entries after a few slices, and only undecided ones take the exact fallback; machine-checked | A GPU implementation and measured performance |

### What this work does not claim

- The first correctly rounded or reproducible Ozaki or GEMM, adaptivity as
  such, or the monotonicity of rounding to nearest.
- The exactness-bound, slice-width or bf16 rules as discoveries.
- Any performance: there is no GPU implementation yet.
- That real GPUs match the models: the models are validated by measurement,
  not proved.
- That cuBLAS's ADP equals the formalized routine, which follows the paper.

## Open questions

- **One unread source.** The 2011 NLAA enclosure paper was read only in
  abstract (paywalled). The 2012 paper, its 2008 precursor, the 2016 follow-up
  and Rump–Ogita–Oishi's summation papers were read in full, and none uses an
  enclosure of a matrix product to decide its rounding or to stop splitting
  early; the closest are AccSum's adaptive stopping and NearSum's midpoint
  test, both for summation.
- **Scale.** The cost claims come from small test matrices; realistic sizes,
  ill-conditioned inputs and the frequency of the exact fallback need measuring.
- **Hardware coverage.** FP8 and FP4 matrix multipliers and Blackwell are not modeled;
  INT8 instruction semantics are out of scope for now
  ([issue #2](https://github.com/pauljiang03/MMAlgebra/issues/2)).
