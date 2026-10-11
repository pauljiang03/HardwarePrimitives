import OzakiTC.ADPZeroPolicyGeneral

/-! # ADP's unsafe zero policies, for every matrix shape

`OzakiTC/ADPZeroPolicyGeneral.lean` proves the unsafe zero policies wrong on one-row, one-column
products. Here the failure is lifted to every shape, and the condition under which the rest of a
matrix hides it is stated exactly.

* **Every shape fails.** Pad the counterexample with zero rows and zero columns: an `(q+1) × k`
  matrix `A` whose first row is `x = (2^a, 1, 0, …)`, and a `k × (p+1)` matrix `B` whose first
  column is `y = (0, 2^d, 0, …)`. A dot product with a zero vector has no exponent at all, so every
  policy gives it the estimate `0` (`escCoarsePolicy_zero_left`, `escCoarsePolicy_zero_right`), and
  the matrix ESC is the counterexample's (`matrixEscPolicy_zp`). The routine emulates and returns the
  zero matrix (`adpPolicy_zp_shape`), so the entry `x · y = 2^d` is `0` and Grade A fails
  (`gradeA_zp_shape`). Skipping zeros fails this way for every block size `≥ 2`, every
  `2 ≤ k < 2^17` and every `p, q` (`adpPolicy_skip_wrong_shape`); zeros at `−1022` for every block
  size `≥ 1` (`adpPolicy_field0_wrong_shape`).
* **When the rest of the matrix masks it.** The routine with an unsafe policy uses one ESC for the
  whole matrix. If other rows and columns raise that ESC to at least the paper's matrix ESC (zeros
  as `−∞`), every emulated entry meets Grade A, on normal or zero entries
  (`adpPolicy_masked_gradeA`): the width then covers every entry's coarsened ESC, as in
  `adp_accuracy`. This is a sufficient condition; below it the failure appears or not depending on
  the entries' bits. -/

open TensorCore

namespace Ozaki.TC

open ADP

/-! ## Zero vectors -/

/-- A zero vector of length `k`. -/
def zeroVec (k : ℕ) : List ℚ := List.replicate k 0

theorem expsOf_zeroVec (k : ℕ) : expsOf (zeroVec k) = List.replicate k none := by
  simp only [expsOf, zeroVec, List.map_replicate, expOf_zero]

theorem maxE_expsOf_zeroVec (k : ℕ) : maxE (expsOf (zeroVec k)) = none := by
  rw [expsOf_zeroVec]; exact maxE_replicate_none k

/-- **A dot product with a zero vector has estimate `0`**, under every zero policy. -/
theorem escCoarsePolicy_zero_left (pol : ZeroPolicy) (n k : ℕ) (y : List ℚ) :
    escCoarsePolicy pol n (zeroVec k) y = some 0 := by
  unfold escCoarsePolicy
  rw [maxE_expsOf_zeroVec]

theorem escCoarsePolicy_zero_right (pol : ZeroPolicy) (n k : ℕ) (x : List ℚ) :
    escCoarsePolicy pol n x (zeroVec k) = some 0 := by
  unfold escCoarsePolicy
  rw [maxE_expsOf_zeroVec]
  cases maxE (expsOf x) <;> rfl

theorem dotZ_zero_right' : ∀ (x y : List ℤ), (∀ z ∈ y, z = 0) → dotZ x y = 0
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | a :: x, b :: y, h => by
    rw [dotZ_cons, h b (by simp), dotZ_zero_right' x y (fun z hz => h z (by simp [hz]))]; simp

theorem fixedProduct_zero_left (W : ℤ) (k : ℕ) (y : List ℚ) :
    fixedProduct W (zeroVec k) y = 0 := by
  unfold fixedProduct
  rw [dotZ_zero_left _ _ (fixedVec_zero (s := shiftOf W (zeroVec k)) (x := zeroVec k)
    (fun a ha => List.eq_of_mem_replicate ha))]
  simp

theorem fixedProduct_zero_right (W : ℤ) (k : ℕ) (x : List ℚ) :
    fixedProduct W x (zeroVec k) = 0 := by
  unfold fixedProduct
  rw [dotZ_zero_right' _ _ (fixedVec_zero (s := shiftOf W (zeroVec k)) (x := zeroVec k)
    (fun a ha => List.eq_of_mem_replicate ha))]
  simp

theorem rne64_zero' : rne64 0 = some 0 := by decide +kernel

/-- An emulated entry with a zero vector is `0`. -/
theorem emulEntry_zero_left {W s : ℕ} (hs : 0 < s) (hfit : ADP.remapFits W s = true) {k : ℕ}
    (hk : k * (128 * 128) < 2 ^ 31) (y : List ℚ) : emulEntry W s (zeroVec k) y = some 0 := by
  rw [emulEntry_eq hs hfit (by simpa [zeroVec] using hk), fixedProduct_zero_left]
  exact rne64_zero'

theorem emulEntry_zero_right {W s : ℕ} (hs : 0 < s) (hfit : ADP.remapFits W s = true) {k : ℕ}
    {x : List ℚ} (hx : x.length = k) (hk : k * (128 * 128) < 2 ^ 31) :
    emulEntry W s x (zeroVec k) = some 0 := by
  rw [emulEntry_eq hs hfit (by rw [hx]; exact hk), fixedProduct_zero_right]
  exact rne64_zero'

/-! ## The padded family -/

/-- `A`: the row `x = (2^a, 1, 0, …)` followed by `q` zero rows. -/
def zpA (a : ℤ) (k q : ℕ) : List (List ℚ) := zpX a k :: List.replicate q (zeroVec k)

/-- `B` by rows: the column `y = (0, 2^d, 0, …)` followed by `p` zero columns. -/
def zpB (d : ℤ) (k p : ℕ) : List (List ℚ) := (zpY d k).map fun v => v :: List.replicate p 0

/-- The columns of a matrix whose first column is `ys` and whose other `p` columns are zero. -/
theorem transpose_padded (p : ℕ) : ∀ ys : List ℚ, ys ≠ [] →
    transpose (ys.map fun v => v :: List.replicate p 0) =
      ys :: List.replicate p (List.replicate ys.length 0)
  | [], h => absurd rfl h
  | [y], _ => by
    show (y :: List.replicate p 0).map (fun a => [a]) = _
    simp [List.map_replicate]
  | y :: y' :: ys, _ => by
    have ih := transpose_padded p (y' :: ys) (by simp)
    show List.zipWith List.cons (y :: List.replicate p 0)
      (transpose ((y' :: ys).map fun v => v :: List.replicate p 0)) = _
    rw [ih]
    simp only [List.zipWith_cons_cons, List.zipWith_replicate, Nat.min_self, List.length_cons,
      List.replicate_succ]

theorem transpose_zpB (d : ℤ) {k : ℕ} (hk : 2 ≤ k) (p : ℕ) :
    transpose (zpB d k p) = zpY d k :: List.replicate p (zeroVec k) := by
  unfold zpB
  rw [transpose_padded p _ (by simp [zpY]), zpY_length d hk]
  rfl

theorem foldl_maxOpt_zeros : ∀ (l : List (Option ℤ)), (∀ e ∈ l, e = some 0) → ∀ v : ℤ, 0 ≤ v →
    l.foldl maxOpt (some v) = some v
  | [], _, _, _ => rfl
  | e :: l, h, v, hv => by
    rw [h e List.mem_cons_self, List.foldl_cons]
    have : maxOpt (some v) (some 0) = some v := by
      simp only [maxOpt, Option.bind_some, Option.map_some]; congr 1; omega
    rw [this]
    exact foldl_maxOpt_zeros l (fun e he => h e (List.mem_cons_of_mem _ he)) v hv

/-- **The padded matrix's ESC is the counterexample's**: the zero rows and columns contribute `0`. -/
theorem matrixEscPolicy_zp (pol : ZeroPolicy) (n : ℕ) {a d : ℤ} {k : ℕ} (p q : ℕ) {esc : ℤ}
    (hesc : escCoarsePolicy pol n (zpX a k) (zpY d k) = some esc) :
    matrixEscPolicy pol n (zpA a k q) (zpY d k :: List.replicate p (zeroVec k)) =
      some (max 0 esc) := by
  unfold matrixEscPolicy zpA
  simp only [List.flatMap_cons, List.map_cons, List.cons_append, List.foldl_cons, hesc]
  have h0 : maxOpt (some 0) (some esc) = some (max 0 esc) := by
    simp only [maxOpt, Option.bind_some, Option.map_some]
  rw [h0]
  apply foldl_maxOpt_zeros _ _ _ (by omega)
  intro e he
  rcases List.mem_append.mp he with he | he
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp he
    rw [List.eq_of_mem_replicate hy]; exact escCoarsePolicy_zero_right pol n k _
  · obtain ⟨x, hx, he⟩ := List.mem_flatMap.mp he
    rw [List.eq_of_mem_replicate hx] at he
    rcases List.mem_cons.mp he with rfl | he
    · exact escCoarsePolicy_zero_left pol n k _
    · obtain ⟨y, _, rfl⟩ := List.mem_map.mp he
      exact escCoarsePolicy_zero_left pol n k y

theorem mapM_const {α β : Type} {f : α → Option β} {c : β} :
    ∀ (l : List α), (∀ a ∈ l, f a = some c) → l.mapM f = some (List.replicate l.length c)
  | [], _ => rfl
  | a :: l, h => by
    rw [List.mapM_cons, h a List.mem_cons_self,
      mapM_const l (fun b hb => h b (List.mem_cons_of_mem _ hb))]
    rfl

/-- **The routine on the padded family.** If a zero policy's ESC for the counterexample is at most
`24` and `a ≥ 78`, ADP emulates and returns the zero matrix. -/
theorem adpPolicy_zp_shape (cfg : ADPConfig) (hratio : 100 ≤ cfg.speedRatio) (pol : ZeroPolicy)
    {a d : ℤ} (ha : 78 ≤ a) (hd : -1022 ≤ d) {k : ℕ} (hk1 : 2 ≤ k)
    (hk2 : k * (128 * 128) < 2 ^ 31) (p q : ℕ) {esc : ℤ}
    (hesc : escCoarsePolicy pol cfg.block (zpX a k) (zpY d k) = some esc) (h24 : esc ≤ 24)
    {A B : List (List (BitVec 64))} (hA : decodeMatrix64 A = some (zpA a k q))
    (hB : decodeMatrix64 B = some (zpB d k p)) :
    adpPolicy cfg pol A B =
      (.emulated, some (List.replicate (q + 1) (List.replicate (p + 1) 0))) := by
  unfold adpPolicy
  rw [hA, hB]
  simp only
  rw [transpose_zpB d hk1 p, matrixEscPolicy_zp pol cfg.block p q hesc]
  simp only
  obtain ⟨m, hmle, hmeq⟩ : ∃ m : ℕ, m ≤ 24 ∧ (m : ℤ) = max 0 esc :=
    ⟨(max 0 esc).toNat, by omega, by omega⟩
  have hW : adpWidth (max 0 esc) = 54 + m := by unfold adpWidth; omega
  rw [hW]
  have hsl := slicesNeeded_le_ten ⟨m, by omega⟩
  obtain ⟨hs1, hfit, _⟩ := slicesNeeded_spec (54 + m)
  have hsq : slicesNeeded (54 + m) * slicesNeeded (54 + m) ≤ cfg.speedRatio := by
    have := Nat.mul_le_mul hsl hsl
    simp only at this
    omega
  rw [if_pos hsq]
  have hent : ∀ x ∈ zpA a k q, ∀ y ∈ zpY d k :: List.replicate p (zeroVec k),
      emulEntry (54 + m) (slicesNeeded (54 + m)) x y = some 0 := by
    intro x hx y hy
    rcases List.mem_cons.mp hx with rfl | hx
    · rcases List.mem_cons.mp hy with rfl | hy
      · exact emulEntry_zp hs1 hfit (by omega) hd (by omega) hk1 hk2
      · rw [List.eq_of_mem_replicate hy]
        exact emulEntry_zero_right hs1 hfit (zpX_length a hk1) hk2
    · rw [List.eq_of_mem_replicate hx]
      exact emulEntry_zero_left hs1 hfit hk2 y
  rw [mapM_const (c := List.replicate (p + 1) 0) _ (fun x hx => by
    rw [mapM_const (c := (0 : ℚ)) _ (fun y hy => hent x hx y hy)]
    simp)]
  simp [zpA]

/-- **Grade A fails on the padded family**: its first entry is `0` where `x · y = 2^d`. -/
theorem gradeA_zp_shape {a d : ℤ} (hd : -1022 ≤ d) {k : ℕ} (hk1 : 2 ≤ k)
    (hk2 : k * (128 * 128) < 2 ^ 31) (p q : ℕ) :
    gradeA (zpA a k q) (zpB d k p) (List.replicate (q + 1) (List.replicate (p + 1) 0)) = false := by
  unfold gradeA
  rw [transpose_zpB d hk1 p]
  simp only [zpA, List.replicate_succ, List.zip_cons_cons, List.all_cons,
    gradeAEntry_zp_zero hd hk1 hk2, Bool.false_and]

/-! ## Binary64 words -/

theorem exists_word64_zero : ∃ w, value64 w = some 0 := exists_word64 binary64Value_zero

theorem exists_padded_columns64 (p : ℕ) : ∀ (y : List ℚ), (∀ a ∈ y, Binary64Value a) →
    ∃ B : List (List (BitVec 64)), decodeMatrix64 B = some (y.map fun v => v :: List.replicate p 0)
  | [], _ => ⟨[], rfl⟩
  | a :: y, h => by
    obtain ⟨w, hw⟩ := exists_word64 (h a List.mem_cons_self)
    obtain ⟨w0, hw0⟩ := exists_word64_zero
    obtain ⟨B, hB⟩ := exists_padded_columns64 p y (fun b hb => h b (List.mem_cons_of_mem _ hb))
    refine ⟨(w :: List.replicate p w0) :: B, ?_⟩
    unfold decodeMatrix64 at hB ⊢
    rw [List.mapM_cons, hB, List.mapM_cons, hw,
      mapM_const (c := (0 : ℚ)) _ (fun b hb => by rw [List.eq_of_mem_replicate hb]; exact hw0)]
    simp

/-- **The padded family's binary64 words exist.** -/
theorem exists_decode_zp_shape {a d : ℤ} (ha1 : -1022 ≤ a) (ha2 : a ≤ 1023) (hd1 : -1022 ≤ d)
    (hd2 : d ≤ 1023) (k p q : ℕ) :
    ∃ A B : List (List (BitVec 64)), decodeMatrix64 A = some (zpA a k q) ∧
      decodeMatrix64 B = some (zpB d k p) := by
  obtain ⟨ws, hws⟩ := exists_words64 (zpX a k) (by
    intro v hv
    simp only [zpX, List.mem_cons, List.mem_replicate] at hv
    rcases hv with rfl | rfl | ⟨_, rfl⟩
    · exact binary64Value_two_pow ha1 ha2
    · exact binary64Value_two_pow (e := 0) (by decide) (by decide)
    · exact binary64Value_zero)
  obtain ⟨w0, hw0⟩ := exists_word64_zero
  obtain ⟨B, hB⟩ := exists_padded_columns64 p (zpY d k) (by
    intro v hv
    simp only [zpY, List.mem_cons, List.mem_replicate] at hv
    rcases hv with rfl | rfl | ⟨_, rfl⟩
    · exact binary64Value_zero
    · exact binary64Value_two_pow hd1 hd2
    · exact binary64Value_zero)
  refine ⟨ws :: List.replicate q (List.replicate k w0), B, ?_, hB⟩
  unfold decodeMatrix64
  rw [List.mapM_cons, hws,
    mapM_const (c := zeroVec k) _ (fun r hr => by
      rw [List.eq_of_mem_replicate hr,
        mapM_const (c := (0 : ℚ)) _ (fun b hb => by rw [List.eq_of_mem_replicate hb]; exact hw0)]
      simp [zeroVec])]
  simp [zpA]

/-! ## The general statements -/

/-- **Skipping zeros is unsafe for every matrix shape**: for every block size `≥ 2`, every
`2 ≤ k < 2^17` and every `p, q`, there are `(q+1) × k` and `k × (p+1)` binary64 matrices on which
ADP with zeros skipped emulates, returns the zero matrix, and breaks Grade A on the entry
`x · y = 2^d`. -/
theorem adpPolicy_skip_wrong_shape (cfg : ADPConfig) (hblock : 2 ≤ cfg.block)
    (hratio : 100 ≤ cfg.speedRatio) {a d : ℤ} (ha1 : 78 ≤ a) (ha2 : a ≤ 1023) (hd1 : -1022 ≤ d)
    (hd2 : d ≤ 1023) {k : ℕ} (hk1 : 2 ≤ k) (hk2 : k * (128 * 128) < 2 ^ 31) (p q : ℕ) :
    ∃ A B : List (List (BitVec 64)), decodeMatrix64 A = some (zpA a k q) ∧
      decodeMatrix64 B = some (zpB d k p) ∧
      adpPolicy cfg .skip A B =
        (.emulated, some (List.replicate (q + 1) (List.replicate (p + 1) 0))) ∧
      gradeA (zpA a k q) (zpB d k p)
        (List.replicate (q + 1) (List.replicate (p + 1) 0)) = false := by
  obtain ⟨esc, hesc, hle⟩ := escCoarsePolicy_skip_zp hblock (show 0 ≤ a by omega) hd1 k
  obtain ⟨A, B, hA, hB⟩ := exists_decode_zp_shape (by omega) ha2 hd1 hd2 k p q
  exact ⟨A, B, hA, hB, adpPolicy_zp_shape cfg hratio .skip ha1 hd1 hk1 hk2 p q hesc (by omega) hA hB,
    gradeA_zp_shape hd1 hk1 hk2 p q⟩

/-- **Zeros at `−1022` are unsafe for every matrix shape**: for every block size `≥ 1`, every
`2 ≤ k < 2^17` and every `p, q`, with `−1022 ≤ d ≤ −998`. -/
theorem adpPolicy_field0_wrong_shape (cfg : ADPConfig) (hblock : 1 ≤ cfg.block)
    (hratio : 100 ≤ cfg.speedRatio) {a d : ℤ} (ha1 : 78 ≤ a) (ha2 : a ≤ 1023) (hd1 : -1022 ≤ d)
    (hd2 : d ≤ -998) {k : ℕ} (hk1 : 2 ≤ k) (hk2 : k * (128 * 128) < 2 ^ 31) (p q : ℕ) :
    ∃ A B : List (List (BitVec 64)), decodeMatrix64 A = some (zpA a k q) ∧
      decodeMatrix64 B = some (zpB d k p) ∧
      adpPolicy cfg .field0 A B =
        (.emulated, some (List.replicate (q + 1) (List.replicate (p + 1) 0))) ∧
      gradeA (zpA a k q) (zpB d k p)
        (List.replicate (q + 1) (List.replicate (p + 1) 0)) = false := by
  obtain ⟨esc, hesc, hle⟩ := escCoarsePolicy_field0_zp hblock (show 0 ≤ a by omega) hd1 k
  obtain ⟨A, B, hA, hB⟩ := exists_decode_zp_shape (by omega) ha2 hd1 (by omega) k p q
  exact ⟨A, B, hA, hB,
    adpPolicy_zp_shape cfg hratio .field0 ha1 hd1 hk1 hk2 p q hesc (by omega) hA hB,
    gradeA_zp_shape hd1 hk1 hk2 p q⟩

/-! ## When the rest of the matrix masks the failure -/

/-- **Masking.** If ADP with any zero policy emulates, and its matrix ESC is at least the paper's
matrix ESC (zeros as `−∞`), then every entry meets Grade A, on normal or zero entries of matching
shapes with `k · 2^14 < 2^31`: the width covers every entry's coarsened ESC. -/
theorem adpPolicy_masked_gradeA {cfg : ADPConfig} {pol : ZeroPolicy}
    {A B : List (List (BitVec 64))} {C : List (List ℚ)}
    (h : adpPolicy cfg pol A B = (.emulated, some C)) {Aq Bq : List (List ℚ)}
    (hA : decodeMatrix64 A = some Aq) (hB : decodeMatrix64 B = some Bq)
    (hshape : ∀ x ∈ Aq, ∀ y ∈ transpose Bq, x.length = y.length)
    (hnA : ∀ x ∈ Aq, ∀ a ∈ x, ADP.Normal64 a) (hnB : ∀ r ∈ Bq, ∀ b ∈ r, ADP.Normal64 b)
    (hk : ∀ x ∈ Aq, x.length * (128 * 128) < 2 ^ 31) {e e0 : ℤ}
    (he : matrixEscPolicy pol cfg.block Aq (transpose Bq) = some e)
    (he0 : matrixEsc cfg.block Aq (transpose Bq) = some e0) (hmask : e0 ≤ e) :
    C.length = Aq.length ∧ ∀ i (hi : i < Aq.length) (hiC : i < C.length),
      C[i].length = (transpose Bq).length ∧
      ∀ j (hj : j < (transpose Bq).length) (hjC : j < C[i].length),
        Rat.abs (C[i][j] - dot Aq[i] (transpose Bq)[j]) ≤
          (4 * Aq[i].length + 1) * 2 ^ (-53 : ℤ) *
            ((List.zipWith (· * ·) Aq[i] (transpose Bq)[j]).map Rat.abs).sum + 2 ^ (-1075 : ℤ) := by
  have gA := decode_onGrid hA
  have gB := decode_onGrid hB
  have gcol : ∀ y ∈ transpose Bq, ∀ b ∈ y, ADP.OnGrid64 b := fun y hy b hb => by
    obtain ⟨r, hr, hbr⟩ := mem_transpose Bq y hy b hb; exact gB r hr b hbr
  have ncol : ∀ y ∈ transpose Bq, ∀ b ∈ y, ADP.Normal64 b := fun y hy b hb => by
    obtain ⟨r, hr, hbr⟩ := mem_transpose Bq y hy b hb; exact hnB r hr b hbr
  unfold adpPolicy at h
  rw [hA, hB] at h
  simp only at h
  rw [he] at h
  simp only at h
  split at h
  · simp only [Prod.mk.injEq] at h
    obtain ⟨_, hC⟩ := h
    obtain ⟨hl, hrows⟩ := mapM_some_index Aq C hC
    refine ⟨hl, fun i hi hiC => ?_⟩
    obtain ⟨hl2, hents⟩ := mapM_some_index (transpose Bq) C[i] (hrows i hi hiC)
    refine ⟨hl2, fun j hj hjC => ?_⟩
    have hx := List.getElem_mem (l := Aq) hi
    have hy := List.getElem_mem (l := transpose Bq) hj
    obtain ⟨c0, hc0, hle⟩ := matrixEsc_ge he0 _ hx _ hy
    obtain ⟨hs1, hfit, _⟩ := slicesNeeded_spec (adpWidth e)
    have hW : 54 + c0 ≤ ((adpWidth e : ℕ) : ℤ) := by unfold adpWidth; omega
    exact emulEntry_gradeA hs1 hfit (hshape _ hx _ hy) (gA _ hx) (gcol _ hy) (hnA _ hx)
      (ncol _ hy) hc0 hW (hk _ hx) (hents j hj hjC)
  · simp at h

end Ozaki.TC
