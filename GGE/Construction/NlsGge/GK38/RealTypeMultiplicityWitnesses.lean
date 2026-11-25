import NlsGge.GK38.RealTypeMultiplicityOrders
import NlsGge.GK38.RealTypeMultiplicityRealDeriv

/-! # S6: actual real critical witnesses in every gap

GK I.6/I.7. Open gaps use Rolle; closed gaps use the exact order-two characteristic.
-/
set_option autoImplicit false
open Filter Topology Set Metric
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

theorem perChar_order_discrim_shift38 (φ : PotPair) (z : ℂ) (hz : perChar φ z = 0) :
    analyticOrderAt (fun w => discrim φ w - discrim φ z) z = analyticOrderAt (perChar φ) z := by
  have ha := analyticOnNhd_discrim_z φ z (mem_univ z)
  have hsq : discrim φ z ^ 2 = 4 := by simpa only [perChar_eq, sub_eq_zero] using hz
  have hn : discrim φ z ≠ 0 := by intro h; rw [h] at hsq; norm_num at hsq
  have hb : AnalyticAt ℂ (fun w => discrim φ w + discrim φ z) z := ha.add analyticAt_const
  have hbn : discrim φ z + discrim φ z ≠ 0 := by
    intro h; apply hn; linear_combination (1 / 2 : ℂ) * h
  have he : perChar φ = (fun w => discrim φ w - discrim φ z) *
      (fun w => discrim φ w + discrim φ z) := by
    funext w
    simp only [Pi.mul_apply, perChar_eq]
    linear_combination hsq
  have hg : AnalyticAt ℂ (fun w => discrim φ w - discrim φ z) z := ha.sub analyticAt_const
  rw [he, analyticOrderAt_mul hg hb,
    hb.analyticOrderAt_eq_zero.mpr hbn, add_zero]

theorem discrim_shift_deriv38 (φ : PotPair) (z : ℂ) :
    deriv (fun w => discrim φ w - discrim φ z) = deriv (discrim φ) := by
  funext w
  exact ((analyticOnNhd_discrim_z φ w (mem_univ w)).differentiableAt.hasDerivAt.sub_const
    (discrim φ z)).deriv

theorem perChar_order_two_critical38 (φ : PotPair) (z : ℂ)
    (hz : perChar φ z = 0) (ho : analyticOrderAt (perChar φ) z = 2) :
    deriv (discrim φ) z = 0 ∧ analyticOrderAt (deriv (discrim φ)) z = 1 := by
  have ha := analyticOnNhd_discrim_z φ z (mem_univ z)
  have hs : analyticOrderAt (fun w => discrim φ w - discrim φ z) z = (1 : ℕ) + 1 := by
    rw [perChar_order_discrim_shift38 φ z hz, ho]; norm_num
  have hd := analyticOrderAt_deriv_of_pos (ha.sub analyticAt_const) hs
  change analyticOrderAt (deriv (fun w => discrim φ w - discrim φ z)) z = _ at hd
  rw [discrim_shift_deriv38] at hd
  refine ⟨apply_eq_zero_of_analyticOrderAt_ne_zero ?_, hd⟩
  rw [hd]; norm_num

theorem perChar_order_one_noncritical38 (φ : PotPair) (z : ℂ)
    (hz : perChar φ z = 0) (ho : analyticOrderAt (perChar φ) z = 1) :
    deriv (discrim φ) z ≠ 0 := by
  have ha := analyticOnNhd_discrim_z φ z (mem_univ z)
  have hs : analyticOrderAt (fun w => discrim φ w - discrim φ z) z = (0 : ℕ) + 1 := by
    rw [perChar_order_discrim_shift38 φ z hz, ho]; norm_num
  have hd := analyticOrderAt_deriv_of_pos (ha.sub analyticAt_const) hs
  change analyticOrderAt (deriv (fun w => discrim φ w - discrim φ z)) z = _ at hd
  rw [discrim_shift_deriv38] at hd
  exact ha.deriv.analyticOrderAt_eq_zero.mp hd

theorem gap_critical_witness38 (u : PhysicalL2) (n : ℤ) :
    ∃ x : ℝ, x ∈ Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) ∧
      deriv (discrim (realSlice u)) (x : ℂ) = 0 := by
  by_cases ho : actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n
  · have hf : Differentiable ℂ (discrim (realSlice u)) := fun z =>
      (analyticOnNhd_discrim_z (realSlice u) z (mem_univ z)).differentiableAt
    obtain ⟨x, hx, hd⟩ := rolle_complex_real38 _ hf (discrim_real_restriction38 u) _ _ ho
      ((gap_discrim_endpoint_values38 u n).1.trans (gap_discrim_endpoint_values38 u n).2.symm)
    exact ⟨x, ⟨hx.1.le, hx.2.le⟩, hd⟩
  · have hc : actualGapLowerAllE02_38 u n = actualGapUpperAllE02_38 u n :=
      le_antisymm (gap_endpoint_levels38 u n).1 (le_of_not_gt ho)
    refine ⟨actualGapLowerAllE02_38 u n, ⟨le_rfl, hc.le⟩, ?_⟩
    apply (perChar_order_two_critical38 _ _ (gap_endpoint_roots38 u n).1 ?_).1
    simpa only [ho, ite_false] using order_at_gapEnd u n

theorem gap_critical_witnesses38 (u : PhysicalL2) : ∃ ν : ℤ → ℝ,
    ∀ n : ℤ, ν n ∈ Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) ∧
      deriv (discrim (realSlice u)) (ν n : ℂ) = 0 := by
  exact Classical.skolem.mp (gap_critical_witness38 u)

end
end NlsGge.GK38
