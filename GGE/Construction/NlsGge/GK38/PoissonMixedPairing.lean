import NlsGge.GK38.PoissonMixedInterpolation

set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.GK38 NlsGge.GK38.GradEigen38 NlsGge.GK38.PoissonDirichlet38
namespace NlsGge.GK38.PoissonMixed38
noncomputable section

theorem intervalIntegrable_kernelWedge38 (g h : PairKernelCont38) :
    IntervalIntegrable (kernelWedge38 g h) volume 0 1 :=
  (((continuous_component g 0).mul (continuous_component h 1)).sub
    ((continuous_component g 1).mul (continuous_component h 0))).intervalIntegrable 0 1

theorem kernelHamField38_rep (h : PairKernelCont38) :
    ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1),
      potRepFst38 (kernelHamField38 h) s = -Complex.I * pairKernelExt38 h s 1 ∧
      potRepSnd38 (kernelHamField38 h) s = Complex.I * pairKernelExt38 h s 0 := by
  filter_upwards [pairKernelL2Class38_rep h,
    ae_restrict_of_ae (coverRep38_smul_ae (-Complex.I) (pairKernelL2Class38 h).2),
    ae_restrict_of_ae (coverRep38_smul_ae Complex.I (pairKernelL2Class38 h).1)] with s hr h0 h1
  constructor
  · change coverRep38 (-Complex.I • (pairKernelL2Class38 h).2) s = _
    exact h0.trans (congrArg (fun a : ℂ => -Complex.I*a) hr.2)
  · change coverRep38 (Complex.I • (pairKernelL2Class38 h).1) s = _
    exact h1.trans (congrArg (fun a : ℂ => Complex.I*a) hr.1)

theorem kernelHamPairing38_eq_wedge_ae (g h : PairKernelCont38) :
    (fun s => pairKernelExt38 g s 0 * potRepFst38 (kernelHamField38 h) s +
      pairKernelExt38 g s 1 * potRepSnd38 (kernelHamField38 h) s)
      =ᵐ[volume.restrict (uIoc (0 : ℝ) 1)]
        (fun s => -Complex.I * kernelWedge38 g h s) := by
  rw [uIoc_of_le zero_le_one,restrict_Ioc_eq_restrict_Icc]
  filter_upwards [kernelHamField38_rep h] with s hs
  rw [hs.1,hs.2]
  unfold kernelWedge38
  ring

theorem kernelPairingTarget : KernelPairingTarget := by
  intro g h
  have hw := intervalIntegrable_kernelWedge38 g h
  have hp := intervalIntegrable_pairKernel38 g t1 (kernelHamField38 h)
  refine ⟨hw,hp,?_⟩
  change pairIntegral38 g t1 (kernelHamField38 h) = _
  rw [pairIntegral38,kernelPoisson38,← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_congr_ae_restrict (kernelHamPairing38_eq_wedge_ae g h)

end
end NlsGge.GK38.PoissonMixed38
