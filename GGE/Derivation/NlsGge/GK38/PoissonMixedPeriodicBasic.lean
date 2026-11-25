import NlsGge.GK38.PoissonMixedComplexKappaLocal

set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.GK38 NlsGge.GK38.GradEigen38 NlsGge.GK38.PoissonDirichlet38
namespace NlsGge.GK38.PoissonMixed38
noncomputable section

theorem periodic_kernel_CLM38 (φ : PotPair) (z : ℂ) :
    integralPairCLM38 (periodicKernel38 φ z) t1 = perImplicitGradient φ z := by
  rw [periodicKernel38,integralPairCLM38_kernelSmul]
  rfl

theorem periodicRootKernelTarget : PeriodicRootKernelTarget := by
  intro φ z hr hs
  have hd := periodic_simple_discrim_nonzero φ z hs
  have hpartial : (fderiv ℂ (fun p : PotPair × ℂ => perChar p.1 p.2) (φ,z)) (0,1) ≠ 0 := by
    rw [periodic_joint_spectral_partial]
    exact hs
  have hA : AnalyticAt ℂ (fun p : PotPair × ℂ => perChar p.1 p.2) (φ,z) :=
    ((analyticOnNhd_discrim.pow 2).sub analyticOnNhd_const) (φ,z) (mem_univ _)
  obtain ⟨U,ρ,hU,hbase,hρ,hvalue,heq,hder⟩ := simple_root_branch_target
    (fun p : PotPair × ℂ => perChar p.1 p.2) φ z hA hr hpartial
  have hΔ : discrim φ z ≠ 0 := by
    intro hz
    apply hs
    rw [periodic_perChar_deriv,hz,mul_zero,zero_mul]
  have hinv : -((2*discrim φ z)*deriv (discrim φ) z)⁻¹*(2*discrim φ z) =
      -(deriv (discrim φ) z)⁻¹ := by field_simp [hΔ,hd]
  rw [periodic_joint_potential_partial,periodic_joint_spectral_partial,
    periodic_perChar_deriv,smul_smul,hinv] at hder
  change HasFDerivAt ρ (perImplicitGradient φ z) φ at hder
  rw [← periodic_kernel_CLM38] at hder
  exact ⟨hd,periodic_kernel_CLM38 φ z,U,ρ,hU,hbase,hρ,hvalue,heq,hder⟩

theorem kernelPoisson_discrim_discrim38 (φ : PotPair) (z w : ℂ) :
    kernelPoisson38 (gradDiscrimCont38 φ z) (gradDiscrimCont38 φ w) = 0 := by
  calc
    kernelPoisson38 (gradDiscrimCont38 φ z) (gradDiscrimCont38 φ w) =
        NlsGge.GK38.PoissonSpectral38.spectralDiscrimPoisson38 φ z w := by
      unfold kernelPoisson38 NlsGge.GK38.PoissonSpectral38.spectralDiscrimPoisson38
      congr 1
      apply intervalIntegral.integral_congr
      intro s hs
      have hs' : s ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using hs
      simp only [kernelWedge38,pairKernelExt38_of_mem _ hs',
        gradDiscrimCont38,ContinuousMap.coe_mk,NlsGge.GK38.PoissonSpectral38.spectralGradientWedge38]
    _ = 0 := (NlsGge.GK38.PoissonSpectral38.spectralDiscrimCommuteTarget φ z w).2.1

theorem periodicMutualTarget : PeriodicMutualTarget := by
  intro φ z w _hrz _hrw hsz hsw
  have hdz := periodic_simple_discrim_nonzero φ z hsz
  have hdw := periodic_simple_discrim_nonzero φ w hsw
  refine ⟨hdz,hdw,?_⟩
  rw [periodicKernel38,periodicKernel38,kernelPoisson_smul_left38,
    kernelPoisson_smul_right38,kernelPoisson_discrim_discrim38,mul_zero,mul_zero]

end
end NlsGge.GK38.PoissonMixed38
