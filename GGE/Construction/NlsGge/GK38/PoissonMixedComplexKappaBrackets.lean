import NlsGge.GK38.PoissonMixedKernelAlgebra

set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.GK38 NlsGge.GK38.GradEigen38 NlsGge.GK38.PoissonDirichlet38
namespace NlsGge.GK38.PoissonMixed38
noncomputable section

theorem norming_dirichlet_distinct_roots38 (φ : PotPair) (z w : ℂ)
    (hz : dirichletChar φ z = 0) (hw : dirichletChar φ w = 0)
    (hsw : deriv (dirichletChar φ) w ≠ 0) (hne : z ≠ w) :
    kernelPoisson38 (normingKernel38 φ z) (dirEigenKernel38 φ w) = 0 := by
  have hm := (normingDirichletMixedTarget φ w z hw hsw).2.2
  rw [(dirichletInterpolationTarget φ w hw hsw).2.2.2 z hz,if_neg hne,mul_zero] at hm
  linear_combination hm/2

theorem kappa_dirichlet_bracket38 (φ : PotPair) (z w : ℂ)
    (hz : dirichletChar φ z = 0) (hw : dirichletChar φ w = 0)
    (hsz : deriv (dirichletChar φ) z ≠ 0) (hsw : deriv (dirichletChar φ) w ≠ 0) :
    kernelPoisson38 (kappaKernel38 φ z) (dirEigenKernel38 φ w) =
      if z=w then 1 else 0 := by
  have hu := normingFactor_ne_zero_at_dirichlet_root38 φ z hz
  have _hQ := dirichlet_Q_ne_zero φ z hz hsz
  simp only [kappaKernel38,kernelPoisson_smul_left38,kernelPoisson_add_left38,
    kernelPoisson_dir_dir38 φ z w hz hw hsz hsw,mul_zero,zero_add]
  by_cases he : z=w
  · subst w
    rw [if_pos rfl]
    have hm := (normingDirichletMixedTarget φ z z hz hsz).2.2
    rw [(dirichletInterpolationTarget φ z hz hsz).2.1,mul_one] at hm
    field_simp
    linear_combination hm
  · rw [if_neg he,norming_dirichlet_distinct_roots38 φ z w hz hw hsw he,mul_zero]

theorem complexKappaBracketsTarget : ComplexKappaBracketsTarget := by
  intro φ z w hz hw hsz hsw
  have hUz := normingFactor_ne_zero_at_dirichlet_root38 φ z hz
  have hUw := normingFactor_ne_zero_at_dirichlet_root38 φ w hw
  have hQz := dirichlet_Q_ne_zero φ z hz hsz
  have hQw := dirichlet_Q_ne_zero φ w hw hsw
  refine ⟨hUz,hUw,hQz,hQw,kappa_dirichlet_bracket38 φ z w hz hw hsz hsw,?_,?_⟩
  · rw [kernelPoisson_swap38,kappa_dirichlet_bracket38 φ w z hw hz hsw hsz]
    by_cases he : z=w
    · subst w; simp
    · simp only [if_neg he,if_neg (Ne.symm he)]
  · by_cases he : z=w
    · subst w
      have h := kernelPoisson_swap38 (kappaKernel38 φ z) (kappaKernel38 φ z)
      linear_combination h/2
    · have hzw := norming_dirichlet_distinct_roots38 φ z w hz hw hsw he
      have hwz := norming_dirichlet_distinct_roots38 φ w z hw hz hsz (Ne.symm he)
      have hswap : kernelPoisson38 (dirEigenKernel38 φ z) (normingKernel38 φ w) = 0 := by
        rw [kernelPoisson_swap38,hwz,neg_zero]
      simp only [kappaKernel38,kernelPoisson_smul_left38,kernelPoisson_smul_right38,
        kernelPoisson_add_left38,kernelPoisson_add_right38,
        kernelPoisson_dir_dir38 φ z w hz hw hsz hsw,hswap,hzw,
        normingSpectralMutualTarget φ z w,mul_zero,zero_add,add_zero]

end
end NlsGge.GK38.PoissonMixed38
