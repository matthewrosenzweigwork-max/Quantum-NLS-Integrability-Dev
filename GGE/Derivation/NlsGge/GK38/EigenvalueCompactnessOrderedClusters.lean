import NlsGge.GK38.EigenvalueCompactnessClusters

/-! # S7: two ordered nonempty clusters identify the lower and upper labels -/
set_option autoImplicit false
open Set Metric
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

theorem endpoint_cluster_has_pair38 (u : PhysicalL2) (n : ℤ) (c r : ℝ)
    (hindex : ∀ z ∈ ball (c : ℂ) r, perChar (realSlice u) z = 0 →
      z = (actualGapLowerAllE02_38 u n : ℂ) ∨ z = (actualGapUpperAllE02_38 u n : ℂ))
    (hcard : 0 < Multiset.card (Lib.zeroMultiset (perChar (realSlice u)) (ball (c : ℂ) r))) :
    ∃ y : ℝ, |y - c| < r ∧
      (y = actualGapLowerAllE02_38 u n ∨ y = actualGapUpperAllE02_38 u n) := by
  obtain ⟨z, hz⟩ := Multiset.card_pos_iff_exists_mem.mp hcard
  have ha := (analyticOnNhd_perChar_z (realSlice u)).mono (subset_univ (closedBall (c : ℂ) r))
  have hm := (Lib.mem_zeroMultiset_ball ha).mp hz
  have hr := apply_eq_zero_of_analyticOrderNatAt_ne_zero hm.2
  refine ⟨z.re, ?_, ?_⟩
  · have hb := (Complex.abs_re_le_norm (z - (c : ℂ))).trans_lt (mem_ball_iff_norm.mp hm.1)
    simpa only [Complex.sub_re, Complex.ofReal_re] using hb
  · rcases hindex z hm.1 hr with hl | hu
    · exact Or.inl (by simpa only [Complex.ofReal_re] using congrArg Complex.re hl)
    · exact Or.inr (by simpa only [Complex.ofReal_re] using congrArg Complex.re hu)

theorem endpoint_two_ordered_clusters38 (u : PhysicalL2) (n : ℤ) (L U r s : ℝ)
    (hsep : r + s < U - L)
    (hL : ∃ y : ℝ, |y - L| < r ∧ (y = actualGapLowerAllE02_38 u n ∨ y = actualGapUpperAllE02_38 u n))
    (hU : ∃ y : ℝ, |y - U| < s ∧ (y = actualGapLowerAllE02_38 u n ∨ y = actualGapUpperAllE02_38 u n)) :
    |actualGapLowerAllE02_38 u n - L| < r ∧ |actualGapUpperAllE02_38 u n - U| < s := by
  obtain ⟨y, hy, he⟩ := hL
  obtain ⟨z, hz, hf⟩ := hU
  have hlt : y < z := by
    have hy' := (abs_lt.mp hy).2
    have hz' := (abs_lt.mp hz).1
    linarith
  rcases he with rfl | rfl <;> rcases hf with rfl | rfl
  · exact False.elim (lt_irrefl _ hlt)
  · exact ⟨hy, hz⟩
  · exact False.elim ((not_lt_of_ge (gap_endpoint_levels38 u n).1) hlt)
  · exact False.elim (lt_irrefl _ hlt)

end
end NlsGge.GK38
