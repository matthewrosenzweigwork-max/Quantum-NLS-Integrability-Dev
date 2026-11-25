import NlsGge.GK38.GradEigenPeriodicSpectral
import NlsGge.GK38.GradEigenClosedBoundary
import NlsGge.GK38.RealTypeMultiplicityWitnesses
import NlsGge.GK38.GradEigenRealPeriodicLabels
import NlsGge.GK38.GradEigenRealPeriodicConst
import NlsGge.GK38.GradEigenClosedInitial
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38.GradEigen38
noncomputable section

theorem dirichlet_spectral_Q_of_anti_zero (φ : PotPair) (z : ℂ)
    (hD : dirichletChar φ z=0) (hA : antiDiscrim φ z=0) :
    deriv (discrim φ) z=(Complex.I*monodromyPair φ z 0 1)*Q (state φ z ![1,1]) := by
  let M := monodromyPair φ z
  let F : ℝ → PairMat38 := ext38 (fundContP φ z)
  let w := state φ z (![1,1] : PairVec38)
  have hboundary := dirichlet_boundary_sum φ z hD
  change M 0 1+M 1 0=0 at hA
  have hsum : 2*M 0 1*(1 : ℂ)=M 1 1-M 0 0 := by
    linear_combination -hboundary+hA
  have hprod : M 0 1*(1 : ℂ)*1= -M 1 0 := by
    linear_combination hA
  have hw (s : ℝ) (i : Fin 2) : pairKernelExt38 w s i=F s i 0+(1 : ℂ)*F s i 1 := by
    rw [state_ext]
    simp [w,F]
  have _hQ := (kernel_integrability w).1
  have he : (∫ s in (0 : ℝ)..1,
      (M*((F s).adjugate*spectralCoeff38*F s)) 0 0+
      (M*((F s).adjugate*spectralCoeff38*F s)) 1 1)=
      (2*Complex.I*M 0 1)*∫ s in (0 : ℝ)..1,
        pairKernelExt38 w s 0*pairKernelExt38 w s 1 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s _
    have hp := periodic_spectral_chart01_algebra M (F s) 1 hsum hprod
    simpa only [hw,mul_assoc] using hp
  rw [periodic_discrim_deriv_trace_integral]
  change (∫ s in (0 : ℝ)..1,
    (M*((F s).adjugate*spectralCoeff38*F s)) 0 0+
    (M*((F s).adjugate*spectralCoeff38*F s)) 1 1)=_
  rw [he]
  change (2*Complex.I*M 0 1)*(∫ s in (0 : ℝ)..1,
    pairKernelExt38 w s 0*pairKernelExt38 w s 1)=
    (Complex.I*M 0 1)*(2*∫ s in (0 : ℝ)..1,
      pairKernelExt38 w s 0*pairKernelExt38 w s 1)
  ring

theorem closed_mu_eq_lower (u : PhysicalL2) (n : ℤ) (hc : u ∈ Z n) :
    gkMu u n=actualGapLowerAllE02_38 u n := by
  have hm := gkMu_mem_gap38 u n
  change actualGapLowerAllE02_38 u n=actualGapUpperAllE02_38 u n at hc
  apply le_antisymm
  · simpa only [hc] using hm.2
  · exact hm.1

theorem closed_dirichlet_anti_and_deriv_zero (u : PhysicalL2) (n : ℤ) (hc : u ∈ Z n) :
    antiDiscrim (realSlice u) (gkMu u n : ℂ)=0 ∧
    deriv (discrim (realSlice u)) (gkMu u n : ℂ)=0 := by
  have he := closed_mu_eq_lower u n hc
  have hr : perChar (realSlice u) (gkMu u n : ℂ)=0 := by
    rw [he]
    simpa only [endpoint,Bool.false_eq_true,ite_false] using endpoint_root u n false
  have hsq := dirichlet_perChar_eq_anti_sq38 (realSlice u) (gkMu u n : ℂ) (gkMu_root38 u n)
  rw [hr] at hsq
  have hA : antiDiscrim (realSlice u) (gkMu u n : ℂ)=0 := eq_zero_of_pow_eq_zero hsq.symm
  refine ⟨hA,?_⟩
  apply (perChar_order_two_critical38 _ _ hr ?_).1
  rw [he,order_at_gapEnd]
  change actualGapLowerAllE02_38 u n=actualGapUpperAllE02_38 u n at hc
  simp [hc]

theorem closed_offdiag_zero (u : PhysicalL2) (n : ℤ) (hc : u ∈ Z n) :
    monodromyPair (realSlice u) (gkMu u n : ℂ) 0 1=0 := by
  obtain ⟨hA,hd⟩ := closed_dirichlet_anti_and_deriv_zero u n hc
  have htrace := dirichlet_spectral_Q_of_anti_zero (realSlice u) (gkMu u n : ℂ)
    (gkMu_root38 u n) hA
  change deriv (discrim (realSlice u)) (gkMu u n : ℂ)=
    (Complex.I*monodromyPair (realSlice u) (gkMu u n : ℂ) 0 1)*Q (dirState u n) at htrace
  have hQ : Q (dirState u n) ≠ 0 := by
    rw [real_denominator _ (dirState_real_symmetry u n)]
    exact_mod_cast ne_of_gt (dirState_energy_positive u n)
  rw [hd] at htrace
  exact (mul_eq_zero.mp ((mul_eq_zero.mp htrace.symm).resolve_right hQ)).resolve_left Complex.I_ne_zero

end
end NlsGge.GK38.GradEigen38
