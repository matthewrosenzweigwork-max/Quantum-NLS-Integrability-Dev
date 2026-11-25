import NlsGge.GK38.PoissonDirichletODE

/-! Q-normalized actual Dirichlet brackets and their actual L2 realization. -/
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.GK38 NlsGge.GK38.GradEigen38
namespace NlsGge.GK38.PoissonDirichlet38
noncomputable section

theorem continuous_dirEigenWedge38 (φ : PotPair) (z w : ℂ) :
    Continuous (dirEigenWedge38 φ z w) :=
  ((continuous_component (dirEigenKernel38 φ z) 0).mul
    (continuous_component (dirEigenKernel38 φ w) 1)).sub
      ((continuous_component (dirEigenKernel38 φ z) 1).mul
        (continuous_component (dirEigenKernel38 φ w) 0))

theorem intervalIntegrable_dirEigenWedge38 (φ : PotPair) (z w : ℂ) :
    IntervalIntegrable (dirEigenWedge38 φ z w) volume 0 1 :=
  (continuous_dirEigenWedge38 φ z w).intervalIntegrable 0 1

theorem dirEigenWedge38_eq_raw (φ : PotPair) (z w : ℂ) (s : ℝ) :
    dirEigenWedge38 φ z w s =
      ((Q (state φ z ![1,1]))⁻¹ * (Q (state φ w ![1,1]))⁻¹) *
        pairBracket38
          (starProd38 (pairKernelExt38 (state φ z ![1,1]) s)
            (pairKernelExt38 (state φ z ![1,1]) s))
          (starProd38 (pairKernelExt38 (state φ w ![1,1]) s)
            (pairKernelExt38 (state φ w ![1,1]) s)) := by
  simp only [dirEigenWedge38, dirEigenKernel38, pairKernelExt38, Set.IccExtend, Function.comp_apply,
    ContinuousMap.smul_apply, Pi.smul_apply, smul_eq_mul, square,
    ContinuousMap.coe_mk, pairBracket38, starProd38,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring

theorem dirEigenPoisson38_eq_zero (φ : PotPair) (z w : ℂ)
    (hz : dirichletChar φ z = 0) (hw : dirichletChar φ w = 0)
    (hsz : deriv (dirichletChar φ) z ≠ 0) (hsw : deriv (dirichletChar φ) w ≠ 0) :
    dirEigenPoisson38 φ z w = 0 := by
  have _hQz := dirichlet_Q_ne_zero φ z hz hsz
  have _hQw := dirichlet_Q_ne_zero φ w hw hsw
  have _hi := intervalIntegrable_dirEigenWedge38 φ z w
  unfold dirEigenPoisson38
  simp only [dirEigenWedge38_eq_raw, intervalIntegral.integral_const_mul,
    integral_dirState_starBracket38_eq_zero φ z w hz hw, mul_zero]

theorem dirEigenHamField38_rep (φ : PotPair) (w : ℂ) :
    ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1),
      potRepFst38 (dirEigenHamField38 φ w) s =
        -Complex.I * pairKernelExt38 (dirEigenKernel38 φ w) s 1 ∧
      potRepSnd38 (dirEigenHamField38 φ w) s =
        Complex.I * pairKernelExt38 (dirEigenKernel38 φ w) s 0 := by
  filter_upwards [pairKernelL2Class38_rep (dirEigenKernel38 φ w),
    ae_restrict_of_ae (coverRep38_smul_ae (-Complex.I)
      (pairKernelL2Class38 (dirEigenKernel38 φ w)).2),
    ae_restrict_of_ae (coverRep38_smul_ae Complex.I
      (pairKernelL2Class38 (dirEigenKernel38 φ w)).1)] with s hr h0 h1
  constructor
  · change coverRep38 (-Complex.I • (pairKernelL2Class38 (dirEigenKernel38 φ w)).2) s = _
    exact h0.trans (congrArg (fun a : ℂ => -Complex.I * a) hr.2)
  · change coverRep38 (Complex.I • (pairKernelL2Class38 (dirEigenKernel38 φ w)).1) s = _
    exact h1.trans (congrArg (fun a : ℂ => Complex.I * a) hr.1)

theorem dirEigenHamPairing38_eq_wedge_ae (φ : PotPair) (z w : ℂ) :
    (fun s => pairKernelExt38 (dirEigenKernel38 φ z) s 0 *
        potRepFst38 (dirEigenHamField38 φ w) s +
      pairKernelExt38 (dirEigenKernel38 φ z) s 1 *
        potRepSnd38 (dirEigenHamField38 φ w) s)
      =ᵐ[volume.restrict (uIoc (0 : ℝ) 1)]
        (fun s => -Complex.I * dirEigenWedge38 φ z w s) := by
  rw [uIoc_of_le zero_le_one, restrict_Ioc_eq_restrict_Icc]
  filter_upwards [dirEigenHamField38_rep φ w] with s hs
  rw [hs.1,hs.2]
  unfold dirEigenWedge38
  ring

theorem intervalIntegrable_dirEigenHamPairing38 (φ : PotPair) (z w : ℂ) :
    IntervalIntegrable (fun s => pairKernelExt38 (dirEigenKernel38 φ z) s 0 *
        potRepFst38 (dirEigenHamField38 φ w) s +
      pairKernelExt38 (dirEigenKernel38 φ z) s 1 *
        potRepSnd38 (dirEigenHamField38 φ w) s) volume 0 1 :=
  intervalIntegrable_pairKernel38 (dirEigenKernel38 φ z) t1 (dirEigenHamField38 φ w)

theorem dirImplicitGradient_eq_kernel38 (φ : PotPair) (z : ℂ)
    (hz : dirichletChar φ z = 0) (hsz : deriv (dirichletChar φ) z ≠ 0) :
    dirImplicitGradient φ z = integralPairCLM38 (dirEigenKernel38 φ z) t1 := by
  have _hQ := dirichlet_Q_ne_zero φ z hz hsz
  rw [complex_dirichlet_gradient_identity φ z hz hsz, dirEigenKernel38,
    integralPairCLM38_kernelSmul]
  rfl

theorem dirImplicitGradient_dirEigenHamField38 (φ : PotPair) (z w : ℂ)
    (hz : dirichletChar φ z = 0) (hsz : deriv (dirichletChar φ) z ≠ 0) :
    dirImplicitGradient φ z (dirEigenHamField38 φ w) = dirEigenPoisson38 φ z w := by
  have _hi := intervalIntegrable_dirEigenHamPairing38 φ z w
  rw [dirImplicitGradient_eq_kernel38 φ z hz hsz]
  change pairIntegral38 (dirEigenKernel38 φ z) t1 (dirEigenHamField38 φ w) = _
  rw [pairIntegral38,dirEigenPoisson38, ← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_congr_ae_restrict (dirEigenHamPairing38_eq_wedge_ae φ z w)

theorem dirichletMutualCommuteTarget : DirichletMutualCommuteTarget := by
  intro φ z w hz hw hsz hsw
  exact ⟨dirichlet_Q_ne_zero φ z hz hsz,dirichlet_Q_ne_zero φ w hw hsw,
    intervalIntegrable_dirEigenWedge38 φ z w,dirEigenPoisson38_eq_zero φ z w hz hw hsz hsw,
    dirImplicitGradient_dirEigenHamField38 φ z w hz hsz⟩

end
end NlsGge.GK38.PoissonDirichlet38
