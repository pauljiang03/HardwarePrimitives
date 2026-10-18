import MatrixCore.Numerics.Exact

/-! # List lemmas -/

namespace MatrixCore

theorem mapM_append_option (f : α → Option β) (l₁ l₂ : List α) :
    (l₁ ++ l₂).mapM f = (l₁.mapM f).bind fun a => (l₂.mapM f).map (a ++ ·) := by
  induction l₁ with
  | nil => simp
  | cons x xs ih =>
    simp only [List.cons_append, List.mapM_cons, ih]
    cases f x <;> simp
    cases xs.mapM f <;> simp
    cases l₂.mapM f <;> simp

theorem mapM_length_option {f : α → Option β} {l : List α} {l' : List β}
    (h : l.mapM f = some l') : l'.length = l.length := by
  induction l generalizing l' with
  | nil => simp at h; subst h; rfl
  | cons x xs ih =>
    simp only [List.mapM_cons] at h
    cases hx : f x <;> simp [hx] at h
    cases hxs : xs.mapM f <;> simp [hxs] at h
    subst h; simp [ih hxs]

theorem mapM_map_option (f : β → Option γ) (g : α → β) (l : List α) :
    (l.map g).mapM f = l.mapM (f ∘ g) := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [List.mapM_cons, ih]

theorem mapM_some_mem {f : α → Option β} {l : List α} {l' : List β} (h : l.mapM f = some l') :
    ∀ x ∈ l, ∃ y, f x = some y := by
  induction l generalizing l' with
  | nil => simp
  | cons x xs ih =>
    simp only [List.mapM_cons] at h
    cases hx : f x <;> simp [hx] at h
    cases hxs : xs.mapM f <;> simp [hxs] at h
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact ⟨_, hx⟩
    · exact ih hxs z hz

theorem mapM_mem_option {f : α → Option β} {l : List α} {l' : List β} (h : l.mapM f = some l') :
    ∀ y ∈ l', ∃ x ∈ l, f x = some y := by
  induction l generalizing l' with
  | nil => simp at h; subst h; simp
  | cons x xs ih =>
    simp only [List.mapM_cons] at h
    cases hx : f x <;> simp [hx] at h
    cases hxs : xs.mapM f <;> simp [hxs] at h
    subst h
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨x, by simp, hx⟩
    · obtain ⟨z, hz, hfz⟩ := ih hxs y hy
      exact ⟨z, by simp [hz], hfz⟩

theorem mem_zipWith' {f : α → β → γ} {as : List α} {bs : List β} {v : γ}
    (h : v ∈ List.zipWith f as bs) : ∃ a ∈ as, ∃ b ∈ bs, v = f a b := by
  induction as generalizing bs with
  | nil => simp at h
  | cons a as ih =>
    cases bs with
    | nil => simp at h
    | cons b bs =>
      simp only [List.zipWith_cons_cons, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨a, by simp, b, by simp, rfl⟩
      · obtain ⟨a', ha', b', hb', rfl⟩ := ih h
        exact ⟨a', by simp [ha'], b', by simp [hb'], rfl⟩

theorem sumQ_perm {xs ys : List ℚ} (h : xs.Perm ys) : sumQ xs = sumQ ys := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp [sumQ, ih]
  | swap x y l => simp only [sumQ]; grind
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end MatrixCore
