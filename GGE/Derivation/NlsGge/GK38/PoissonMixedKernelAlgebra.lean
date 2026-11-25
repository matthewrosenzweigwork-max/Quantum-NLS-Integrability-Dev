import NlsGge.GK38.PoissonMixedNormingDirichletComplete

set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.GK38 NlsGge.GK38.GradEigen38 NlsGge.GK38.PoissonDirichlet38
namespace NlsGge.GK38.PoissonMixed38
noncomputable section

theorem kernelWedge_smul_left38 (c : ℂ) (g h : PairKernelCont38) (s : ℝ) :
    kernelWedge38 (c • g) h s = c * kernelWedge38 g h s := by
  simp only [kernelWedge38,pairKernelExt38,Set.IccExtend,Function.comp_apply,
    ContinuousMap.smul_apply,Pi.smul_apply,smul_eq_mul]
  ring

theorem kernelWedge_add_left38 (g k h : PairKernelCont38) (s : ℝ) :
    kernelWedge38 (g+k) h s = kernelWedge38 g h s + kernelWedge38 k h s := by
  simp only [kernelWedge38,pairKernelExt38,Set.IccExtend,Function.comp_apply,
    ContinuousMap.add_apply,Pi.add_apply]
  ring

theorem kernelWedge_swap38 (g h : PairKernelCont38) (s : ℝ) :
    kernelWedge38 h g s = -kernelWedge38 g h s := by
  unfold kernelWedge38
  ring

theorem kernelPoisson_smul_left38 (c : ℂ) (g h : PairKernelCont38) :
    kernelPoisson38 (c • g) h = c * kernelPoisson38 g h := by
  have _hi := intervalIntegrable_kernelWedge38 g h
  simp only [kernelPoisson38,kernelWedge_smul_left38,intervalIntegral.integral_const_mul]
  ring

theorem kernelPoisson_add_left38 (g k h : PairKernelCont38) :
    kernelPoisson38 (g+k) h = kernelPoisson38 g h + kernelPoisson38 k h := by
  have hg := intervalIntegrable_kernelWedge38 g h
  have hk := intervalIntegrable_kernelWedge38 k h
  simp only [kernelPoisson38,kernelWedge_add_left38,intervalIntegral.integral_add hg hk]
  ring

theorem kernelPoisson_swap38 (g h : PairKernelCont38) :
    kernelPoisson38 h g = -kernelPoisson38 g h := by
  have _hi := intervalIntegrable_kernelWedge38 g h
  simp only [kernelPoisson38,kernelWedge_swap38 g h,intervalIntegral.integral_neg]
  ring

theorem kernelPoisson_smul_right38 (c : ℂ) (g h : PairKernelCont38) :
    kernelPoisson38 g (c • h) = c * kernelPoisson38 g h := by
  rw [kernelPoisson_swap38,kernelPoisson_smul_left38,kernelPoisson_swap38 h g]
  ring

theorem kernelPoisson_add_right38 (g h k : PairKernelCont38) :
    kernelPoisson38 g (h+k) = kernelPoisson38 g h + kernelPoisson38 g k := by
  rw [kernelPoisson_swap38,kernelPoisson_add_left38,kernelPoisson_swap38 h g,
    kernelPoisson_swap38 k g]
  ring

theorem kernelPoisson_dir_dir38 (φ : PotPair) (z w : ℂ)
    (hz : dirichletChar φ z = 0) (hw : dirichletChar φ w = 0)
    (hsz : deriv (dirichletChar φ) z ≠ 0) (hsw : deriv (dirichletChar φ) w ≠ 0) :
    kernelPoisson38 (dirEigenKernel38 φ z) (dirEigenKernel38 φ w) = 0 :=
  dirEigenPoisson38_eq_zero φ z w hz hw hsz hsw

end
end NlsGge.GK38.PoissonMixed38
