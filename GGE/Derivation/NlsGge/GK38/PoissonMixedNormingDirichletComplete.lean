import NlsGge.GK38.PoissonMixedNormingDirichlet

set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.GK38 NlsGge.GK38.GradEigen38 NlsGge.GK38.PoissonDirichlet38
namespace NlsGge.GK38.PoissonMixed38
noncomputable section

theorem scalar_norming_dirichlet38 (q d u e a j : ℂ)
    (hd : d ≠ 0) (hu : u ≠ 0) (he : e ≠ 0)
    (hq : q = 2*d*u) (h : -4*Complex.I*a*u^2 = 2*Complex.I*e*j) :
    2*(-Complex.I)*(((2*Complex.I)⁻¹*q⁻¹)*j) = u*(a/(e*d)) := by
  have hi : (2 : ℂ)*Complex.I ≠ 0 := mul_ne_zero (by norm_num) Complex.I_ne_zero
  have hj : j = (-2*a*u^2)/e := by
    apply (eq_div_iff he).mpr
    apply mul_left_cancel₀ hi
    calc
      (2*Complex.I)*(j*e) = 2*Complex.I*e*j := by ring
      _ = -4*Complex.I*a*u^2 := h.symm
      _ = (2*Complex.I)*(-2*a*u^2) := by ring
  rw [hq,hj]
  field_simp

theorem norming_dirichlet_mixed_off_base38 (φ : PotPair) (z ζ : ℂ)
    (hr : dirichletChar φ z = 0) (hs : deriv (dirichletChar φ) z ≠ 0)
    (hne : ζ ≠ z) :
    2*kernelPoisson38 (normingKernel38 φ ζ) (dirEigenKernel38 φ z) =
      normingFactor φ z * dirInterpolation38 φ z ζ := by
  have hU := normingFactor_ne_zero_at_dirichlet_root38 φ z hr
  have _hQ := dirichlet_Q_ne_zero φ z hr hs
  have _hi := intervalIntegrable_kernelWedge38 (normingKernel38 φ ζ) (dirEigenKernel38 φ z)
  have h := norming_dir_integral_identity38 φ z ζ hr
  rw [dirInterpolation_off_root38 φ z ζ hr hne]
  unfold kernelPoisson38
  simp only [norming_dir_wedge_eq_raw38,intervalIntegral.integral_const_mul]
  rw [← mul_assoc]
  exact scalar_norming_dirichlet38 _ _ _ _ _ _ hs hU (sub_ne_zero.mpr hne)
    (norming_Q_at_dirichlet_root38 φ z hr) h

theorem normingDirichletMixedTarget : NormingDirichletMixedTarget := by
  intro φ z ζ hr hs
  refine ⟨normingFactor_ne_zero_at_dirichlet_root38 φ z hr,
    dirichlet_Q_ne_zero φ z hr hs,?_⟩
  by_cases he : ζ = z
  · subst ζ
    let L : ℂ → ℂ := fun w =>
      2*kernelPoisson38 (normingKernel38 φ w) (dirEigenKernel38 φ z)
    let R : ℂ → ℂ := fun w => normingFactor φ z * dirInterpolation38 φ z w
    have hL : Continuous L := continuous_const.mul (continuous_normingPoisson38 φ _)
    have hR : Continuous R := continuous_const.mul
      (continuousOn_univ.mp (dirichletInterpolationTarget φ z hr hs).1.continuousOn)
    have hEq : L =ᶠ[𝓝[≠] z] R := by
      filter_upwards [self_mem_nhdsWithin] with w hw
      exact norming_dirichlet_mixed_off_base38 φ z w hr hs hw
    exact tendsto_nhds_unique
      (hL.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      ((hR.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' hEq.symm)
  · exact norming_dirichlet_mixed_off_base38 φ z ζ hr hs he

end
end NlsGge.GK38.PoissonMixed38
