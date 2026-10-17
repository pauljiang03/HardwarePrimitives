import OzakiTC

/-! # Pinned accumulation: a kernel-checked demonstration

Twenty-eight fp16 products. Natively on H100 the result depends on the order of the two block FMAs
that hold them (`h100_native_order_dependent`). With a cancelling pin pair `±2^α` in every block,
chosen so that the alignment grid is `2^-15` on each GPU, H100, A100 and V100 return the same word
in every order tried (`pinned_agree_v100_a100_h100`). -/

open TensorCore

namespace MMAlgebra.TC.PinnedDemo


/-- The last output word of a chain of block FMAs from `c = 0`. -/
def run (p : Model) (bs : List (List (p.Word × p.Word))) : Option F32 :=
  match runBlocks p 0 bs with
  | .ok ts => ts.getLast?.map (·.output.bits)
  | .error _ => none

/-- Fourteen of the 28 products (fp16 operands between about −2 and 2). -/
def r1 : List (F16 × F16) := [(0x3ba9, 0x3f0c), (0xbcdb, 0x3f34), (0x3e1d, 0x36a0),
    (0xb507, 0xbe57), (0xbf61, 0x3f67), (0xbc2f, 0x3a8c), (0xbbc7, 0x3d2e), (0x362d, 0xba9c),
    (0xbd31, 0x3b0d), (0xbee6, 0xbc58), (0x3399, 0x3da3), (0x3751, 0xbb08), (0x3eae, 0xbcbd),
    (0xbfbc, 0xbb63)]
/-- The other fourteen products. -/
def r2 : List (F16 × F16) := [(0xb2f3, 0xbf08), (0xbd2e, 0xb833), (0x349e, 0xbde5),
    (0xb869, 0x3e41), (0x3fb0, 0x3906), (0x3a1e, 0x3567), (0xbdc1, 0xbf70), (0xbfb7, 0x3e90),
    (0x3a6e, 0x3f68), (0xbfa9, 0x385c), (0xac8c, 0x3b60), (0xb9cc, 0x3ffd), (0xbecc, 0x31e6),
    (0x3b96, 0x3e67)]
/-- Two empty slots. -/
def z2 : List (F16 × F16) := [(0, 0), (0, 0)]
/-- The pin pair on H100: `±2^5 · 2^5 = ±2^10`,
  so `α = 10` and the grid is `2^(10 − 25) = 2^-15`. -/
def pinH : List (F16 × F16) := [(0x5000, 0x5000), (0xD000, 0x5000)]
/-- The pin pair on A100: `±2^4 · 2^5 = ±2^9`, so the grid is `2^(9 − 24) = 2^-15`. -/
def pinA : List (F16 × F16) := [(0x4C00, 0x5000), (0xCC00, 0x5000)]
/-- The pin pair on V100: `±2^4 · 2^4 = ±2^8`, so the grid is `2^(8 − 23) = 2^-15`. -/
def pinV : List (F16 × F16) := [(0x4C00, 0x4C00), (0xCC00, 0x4C00)]
/-- The 28 products in blocks of six for A100 (with the pin pair, eight slots). -/
def a0 : List (F16 × F16) := [(0x3ba9, 0x3f0c), (0xbcdb, 0x3f34), (0x3e1d, 0x36a0),
    (0xb507, 0xbe57), (0xbf61, 0x3f67), (0xbc2f, 0x3a8c)]
def a1 : List (F16 × F16) := [(0xbbc7, 0x3d2e), (0x362d, 0xba9c), (0xbd31, 0x3b0d),
    (0xbee6, 0xbc58), (0x3399, 0x3da3), (0x3751, 0xbb08)]
def a2 : List (F16 × F16) := [(0x3eae, 0xbcbd), (0xbfbc, 0xbb63), (0xb2f3, 0xbf08),
    (0xbd2e, 0xb833), (0x349e, 0xbde5), (0xb869, 0x3e41)]
def a3 : List (F16 × F16) := [(0x3fb0, 0x3906), (0x3a1e, 0x3567), (0xbdc1, 0xbf70),
    (0xbfb7, 0x3e90), (0x3a6e, 0x3f68), (0xbfa9, 0x385c)]
def a4 : List (F16 × F16) := [(0xac8c, 0x3b60), (0xb9cc, 0x3ffd), (0xbecc, 0x31e6),
    (0x3b96, 0x3e67), (0, 0), (0, 0)]
/-- The 28 products in blocks of two for V100 (with the pin pair, four slots). -/
def v0 : List (F16 × F16) := [(0x3ba9, 0x3f0c), (0xbcdb, 0x3f34)]
def v1 : List (F16 × F16) := [(0x3e1d, 0x36a0), (0xb507, 0xbe57)]
def v2 : List (F16 × F16) := [(0xbf61, 0x3f67), (0xbc2f, 0x3a8c)]
def v3 : List (F16 × F16) := [(0xbbc7, 0x3d2e), (0x362d, 0xba9c)]
def v4 : List (F16 × F16) := [(0xbd31, 0x3b0d), (0xbee6, 0xbc58)]
def v5 : List (F16 × F16) := [(0x3399, 0x3da3), (0x3751, 0xbb08)]
def v6 : List (F16 × F16) := [(0x3eae, 0xbcbd), (0xbfbc, 0xbb63)]
def v7 : List (F16 × F16) := [(0xb2f3, 0xbf08), (0xbd2e, 0xb833)]
def v8 : List (F16 × F16) := [(0x349e, 0xbde5), (0xb869, 0x3e41)]
def v9 : List (F16 × F16) := [(0x3fb0, 0x3906), (0x3a1e, 0x3567)]
def v10 : List (F16 × F16) := [(0xbdc1, 0xbf70), (0xbfb7, 0x3e90)]
def v11 : List (F16 × F16) := [(0x3a6e, 0x3f68), (0xbfa9, 0x385c)]
def v12 : List (F16 × F16) := [(0xac8c, 0x3b60), (0xb9cc, 0x3ffd)]
def v13 : List (F16 × F16) := [(0xbecc, 0x31e6), (0x3b96, 0x3e67)]

/-- **Native H100 depends on the order.** The same 28 products in two block FMAs give
`−3.86069369…` (`0xc077159b`) in one block order and the next binary32 value (`0xc077159c`) in
the other. -/
theorem h100_native_order_dependent :
    run hopperF16F32 [r1 ++ z2, r2 ++ z2] = some 0xc077159b ∧
    run hopperF16F32 [r2 ++ z2, r1 ++ z2] = some 0xc077159c := by decide +kernel

/-- **Pinned accumulation agrees across orders and GPUs.** With a pin pair in every block, H100
in both block orders, A100 in both orders and V100 in both orders all return `−3.86065674`
(`0xc0771500`), the products' sum truncated to the grid `2^-15`; each half alone gives
`−4.74682617` and `0.88616943`. -/
theorem pinned_agree_v100_a100_h100 :
    run hopperF16F32 [r1 ++ pinH, r2 ++ pinH] = some 0xc0771500 ∧
    run hopperF16F32 [r2 ++ pinH, r1 ++ pinH] = some 0xc0771500 ∧
    run hopperF16F32 [r1 ++ pinH] = some 0xc097e600 ∧ 
    run hopperF16F32 [r2 ++ pinH] = some 0x3f62dc00 ∧
    run ampereF16F32 [a0 ++ pinA, a1 ++ pinA, a2 ++ pinA, a3 ++ pinA, a4 ++ pinA] = some 0xc0771500 ∧
    run ampereF16F32 [a4 ++ pinA, a3 ++ pinA, a2 ++ pinA, a1 ++ pinA, a0 ++ pinA] = some 0xc0771500 ∧
    run v100F16F32 [v0 ++ pinV, v1 ++ pinV, v2 ++ pinV, v3 ++ pinV, v4 ++ pinV, v5 ++ pinV,
        v6 ++ pinV, v7 ++ pinV, v8 ++ pinV, v9 ++ pinV, v10 ++ pinV, v11 ++ pinV, v12 ++ pinV,
        v13 ++ pinV] = some 0xc0771500 ∧
    run v100F16F32 [v13 ++ pinV, v12 ++ pinV, v11 ++ pinV, v10 ++ pinV, v9 ++ pinV, v8 ++ pinV,
        v7 ++ pinV, v6 ++ pinV, v5 ++ pinV, v4 ++ pinV, v3 ++ pinV, v2 ++ pinV, v1 ++ pinV,
        v0 ++ pinV] = some 0xc0771500 := by decide +kernel

end MMAlgebra.TC.PinnedDemo
