import NlsGge.Birkhoff.H03Diagonal38

/-! H03 (review REVIEW_H03 finding F1): the diagonal hierarchy order is monotone and at most `max 2 N`. -/

namespace NlsGge.Birkhoff
theorem monotone_diagOrder38 (Nk : ℕ → ℕ) : Monotone (diagOrder38 Nk) := by
  classical
  intro a b hab
  unfold diagOrder38
  refine max_le_max le_rfl ?_
  by_cases h : ∃ k ≤ a, 2 ≤ k ∧ Nk k ≤ a
  · obtain ⟨k, hk, h2, hN⟩ := h
    have : k ≤ Nat.findGreatest (fun k => 2 ≤ k ∧ Nk k ≤ a) a := Nat.le_findGreatest hk ⟨h2, hN⟩
    refine le_trans ?_ (Nat.findGreatest_mono (P := fun k => 2 ≤ k ∧ Nk k ≤ a) (Q := fun k => 2 ≤ k ∧ Nk k ≤ b) (fun k hk => ⟨hk.1, hk.2.trans hab⟩) hab)
    exact le_rfl
  · push_neg at h
    have : Nat.findGreatest (fun k => 2 ≤ k ∧ Nk k ≤ a) a = 0 := by
      apply Nat.findGreatest_eq_zero_iff.2
      intro k hk0 hk hP
      exact absurd hP.2 (not_le.2 (h k hk hP.1))
    rw [this]; exact Nat.zero_le _
theorem diagOrder38_le (Nk : ℕ → ℕ) (N : ℕ) : diagOrder38 Nk N ≤ max 2 N := by
  unfold diagOrder38
  exact max_le_max le_rfl (Nat.findGreatest_le N)

end NlsGge.Birkhoff
