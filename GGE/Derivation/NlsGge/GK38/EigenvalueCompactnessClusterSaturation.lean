import NlsGge.GK38.EigenvalueCompactnessClusters

/-! # S7: exact multiplicity saturates the actual periodic endpoint pair -/
set_option autoImplicit false
open Set Metric
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

theorem endpoint_cluster_le_pair38 (u : PhysicalL2) (n : ℤ) (c : ℂ) (r : ℝ)
    (hindex : ∀ z ∈ ball c r, perChar (realSlice u) z = 0 →
      z = (actualGapLowerAllE02_38 u n : ℂ) ∨ z = (actualGapUpperAllE02_38 u n : ℂ)) :
    Lib.zeroMultiset (perChar (realSlice u)) (ball c r) ≤
      ((actualGapLowerAllE02_38 u n : ℂ) ::ₘ (actualGapUpperAllE02_38 u n : ℂ) ::ₘ 0) := by
  classical
  apply Multiset.le_iff_count.mpr
  intro z
  have ha := (analyticOnNhd_perChar_z (realSlice u)).mono (subset_univ (closedBall c r))
  by_cases hz : z ∈ Lib.zeroMultiset (perChar (realSlice u)) (ball c r)
  · have hzm := (Lib.mem_zeroMultiset_ball ha).mp hz
    have hr := apply_eq_zero_of_analyticOrderNatAt_ne_zero hzm.2
    rcases hindex z hzm.1 hr with hl | hu
    · subst z
      rw [Lib.count_zeroMultiset_ball ha, if_pos hzm.1]
      have ho := endpoint_order38 u n (actualGapLowerAllE02_38 u n) (Or.inl rfl)
      simp only [analyticOrderNatAt, ho]
      by_cases hc : actualGapLowerAllE02_38 u n = actualGapUpperAllE02_38 u n
      · simp [hc]
      · have hne : (actualGapLowerAllE02_38 u n : ℂ) ≠ (actualGapUpperAllE02_38 u n : ℂ) :=
          fun h => hc (Complex.ofReal_injective h)
        simp [hc, hne, hne.symm]
    · subst z
      rw [Lib.count_zeroMultiset_ball ha, if_pos hzm.1]
      have ho := endpoint_order38 u n (actualGapUpperAllE02_38 u n) (Or.inr rfl)
      simp only [analyticOrderNatAt, ho]
      by_cases hc : actualGapLowerAllE02_38 u n = actualGapUpperAllE02_38 u n
      · simp [hc]
      · have hne : (actualGapLowerAllE02_38 u n : ℂ) ≠ (actualGapUpperAllE02_38 u n : ℂ) :=
          fun h => hc (Complex.ofReal_injective h)
        simp [hc, hne, hne.symm]
  · rw [Multiset.count_eq_zero.mpr hz]
    exact Nat.zero_le _

theorem endpoint_cluster_card_two_pair38 (u : PhysicalL2) (n : ℤ) (c : ℂ) (r : ℝ)
    (hindex : ∀ z ∈ ball c r, perChar (realSlice u) z = 0 →
      z = (actualGapLowerAllE02_38 u n : ℂ) ∨ z = (actualGapUpperAllE02_38 u n : ℂ))
    (hcard : Multiset.card (Lib.zeroMultiset (perChar (realSlice u)) (ball c r)) = 2) :
    (actualGapLowerAllE02_38 u n : ℂ) ∈ ball c r ∧
      (actualGapUpperAllE02_38 u n : ℂ) ∈ ball c r := by
  have he := Multiset.eq_of_le_of_card_le (endpoint_cluster_le_pair38 u n c r hindex)
    (by simpa only [Multiset.card_cons, Multiset.card_zero] using hcard.ge)
  have ha := (analyticOnNhd_perChar_z (realSlice u)).mono (subset_univ (closedBall c r))
  have hl : (actualGapLowerAllE02_38 u n : ℂ) ∈ Lib.zeroMultiset (perChar (realSlice u)) (ball c r) := by rw [he]; simp
  have hu : (actualGapUpperAllE02_38 u n : ℂ) ∈ Lib.zeroMultiset (perChar (realSlice u)) (ball c r) := by rw [he]; simp
  exact ⟨((Lib.mem_zeroMultiset_ball ha).mp hl).1, ((Lib.mem_zeroMultiset_ball ha).mp hu).1⟩

end
end NlsGge.GK38
