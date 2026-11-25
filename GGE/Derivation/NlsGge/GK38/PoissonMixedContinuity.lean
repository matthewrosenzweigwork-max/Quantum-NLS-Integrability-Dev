import NlsGge.GK38.PoissonMixedNormingMutual
import Mathlib.Analysis.Calculus.FDeriv.Analytic

set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.GK38 NlsGge.GK38.GradEigen38 NlsGge.GK38.PoissonDirichlet38
namespace NlsGge.GK38.PoissonMixed38
noncomputable section

theorem continuous_normingCLM_apply38 (φ : PotPair) (h : PotPair) :
    Continuous (fun z : ℂ => normingCLM38 φ z h) := by
  let f : PotPair × ℂ → ℂ := fun p => normingFactor p.1 p.2
  have hD : Continuous (fderiv ℂ f) :=
    continuousOn_univ.mp ((analyticOnNhd_normingFactor38.fderiv_of_isOpen isOpen_univ).continuousOn)
  have he : (fun z : ℂ => normingCLM38 φ z h) =
      (fun z : ℂ => (fderiv ℂ f (φ,z)) (potentialInclusion h)) := by
    funext z
    exact (congrArg (fun L : PotPair →L[ℂ] ℂ => L h)
      (norming_joint_potential_partial38 φ z)).symm
  rw [he]
  exact (hD.comp (continuous_const.prodMk continuous_id)).clm_apply continuous_const

theorem continuous_normingPoisson38 (φ : PotPair) (h : PairKernelCont38) :
    Continuous (fun z : ℂ => kernelPoisson38 (normingKernel38 φ z) h) := by
  have he : (fun z : ℂ => kernelPoisson38 (normingKernel38 φ z) h) =
      (fun z : ℂ => normingCLM38 φ z (kernelHamField38 h)) := by
    funext z
    exact (kernelPairingTarget (normingKernel38 φ z) h).2.2.symm
  rw [he]
  exact continuous_normingCLM_apply38 φ (kernelHamField38 h)

end
end NlsGge.GK38.PoissonMixed38
