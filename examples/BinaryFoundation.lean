import TensorCore.TC.FusedRounding
import TensorCore.Numerics.Binary.RoundingContract

open TensorCore

-- Every rational in the finite range has a correctly rounded result, in every format and mode.
example (f : Format) (hf : f.WellFormed) (mode : BinaryRoundingMode) (x : ℚ)
    (hr : absQ x ≤ f.maxFinite) :
    ∃ bits, roundBinary f mode x = some bits ∧ BinaryRoundSpec f mode x bits :=
  roundBinary_correct f hf mode x hr

example (f : Format) (hf : f.WellFormed) (b : FiniteBinaryWord f) :
    (signedFiniteBinaryBijection f hf).encode ((signedFiniteBinaryBijection f hf).decode b) = b :=
  (signedFiniteBinaryBijection f hf).encode_decode b

example (f : Format) (hf : f.WellFormed) (v : SignedFiniteValue f) :
    (signedFiniteBinaryBijection f hf).decode ((signedFiniteBinaryBijection f hf).encode v) = v :=
  (signedFiniteBinaryBijection f hf).decode_encode v

-- The canonical representation: a nonnegative significand with an explicit sign.
example (f : Format) (hf : f.WellFormed) (r : BinaryRep f) :
    decodeBinaryRep f hf (encodeBinaryRep f hf r) = r :=
  (finiteBinaryBijection f hf).decode_encode r

def minusZero : FiniteBinaryWord fp16 := ⟨0x8000, ⟨⟨0, 0, 0⟩, by decide +kernel⟩⟩

-- Encoding the signed value preserves -0; rounding its rational projection gives +0.
example : (encodeSignedBinary fp16 (by decide)
    (decodeSignedBinary fp16 (by decide) minusZero)).val = 0x8000 :=
  congrArg Subtype.val (encode_decodeSignedBinary fp16 (by decide) minusZero)

example (mode : BinaryRoundingMode) :
    roundBinary fp16 mode (decodeSignedBinary fp16 (by decide) minusZero).value = some 0 := by
  have hz : (decodeSignedBinary fp16 (by decide) minusZero).value = 0 := by decide +kernel
  rw [hz]
  exact roundBinary_zero fp16 (by decide) mode

-- FP64 DMMA: the four-direction contract is about the exact decoded product plus c.
example {mode : BinaryRoundingMode} {x : InvocationInput (fp64Fma mode)}
    {t : InvocationTrace (fp64Fma mode)} (h : evalInvocation x = .ok t) :
    invocationIdeal x = some t.intermediate.value ∧
    BinaryRoundSpec fp64 mode t.intermediate.value t.output.bits ∧
    binarySign fp64 t.output.bits = decide (t.intermediate.value < 0) :=
  fp64Fma_correct h

example (mode : BinaryRoundingMode) (x : InvocationInput (fp64Fma mode))
    (b : PreparedInvocation (fp64Fma mode)) (hp : prepareInvocation x = some b)
    (hn : x.products.length = 1) (hr : absQ b.exactDot ≤ fp64.maxFinite) :
    ∃ t, evalInvocation x = .ok t :=
  fp64Fma_success mode x b hp hn hr
