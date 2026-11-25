import NlsGge.GK38.GradEigenClosedCharacterizationProbe
import NlsGge.GK38.GradEigenClosedAnalytic
import NlsGge.GK38.GradEigenRealGradientProbe
import NlsGge.GK38.RealTypeMultiplicityRealDeriv
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38.GradEigen38
noncomputable section

theorem realKernelCLM_add (g k : PairKernelCont38) :
    realKernelCLM (g+k)=realKernelCLM g+realKernelCLM k := by
  ext h
  change (integralPairCLM38 (g+k) t1 (realSlice h)).re=
    (integralPairCLM38 g t1 (realSlice h)).re+(integralPairCLM38 k t1 (realSlice h)).re
  rw [integralPairCLM38_kernelAdd]
  rfl

theorem realKernelCLM_sub (g k : PairKernelCont38) :
    realKernelCLM (g-k)=realKernelCLM g-realKernelCLM k := by
  ext h
  change (integralPairCLM38 (g-k) t1 (realSlice h)).re=
    (integralPairCLM38 g t1 (realSlice h)).re-(integralPairCLM38 k t1 (realSlice h)).re
  rw [integralPairCLM38_kernelSub]
  rfl

theorem realKernelCLM_real_smul (r : ℝ) (g : PairKernelCont38) :
    realKernelCLM ((r : ℂ) • g)=r • realKernelCLM g := by
  ext h
  change (integralPairCLM38 ((r : ℂ) • g) t1 (realSlice h)).re=
    r*(integralPairCLM38 g t1 (realSlice h)).re
  rw [integralPairCLM38_kernelSmul]
  simp

theorem realEnergyGradient_eq_realKernel (w : PairKernelCont38) :
    realEnergyGradient w=realKernelCLM (normalizedSquare w) := by
  rw [normalizedSquare,← Complex.ofReal_inv,realKernelCLM_real_smul]
  rfl

theorem anti_joint_potential_partial (φ : PotPair) (z : ℂ) :
    (fderiv ℂ (fun p : PotPair × ℂ => antiDiscrim p.1 p.2) (φ,z)).comp potentialInclusion=
      gradAntiDiscrimCLM φ z := by
  let f : PotPair × ℂ → ℂ := fun p => antiDiscrim p.1 p.2
  have hf : HasFDerivAt f (fderiv ℂ f (φ,z)) (φ,z) :=
    (analyticOnNhd_antiDiscrim (φ,z) (mem_univ _)).differentiableAt.hasFDerivAt
  have hcurve : HasFDerivAt (fun ψ : PotPair => (ψ,z)) potentialInclusion φ :=
    hasFDerivAt_prodMk_left (𝕜 := ℂ) φ z
  have hp := hf.comp φ hcurve
  change HasFDerivAt (fun ψ : PotPair => antiDiscrim ψ z)
    ((fderiv ℂ f (φ,z)).comp potentialInclusion) φ at hp
  exact hp.unique (hasFDerivAt_gradAntiDiscrimCLM φ z)

theorem anti_joint_spectral_partial (φ : PotPair) (z : ℂ) :
    (fderiv ℂ (fun p : PotPair × ℂ => antiDiscrim p.1 p.2) (φ,z)) (0,1)=
      spectralAntiDiscrimIntegral38 φ z := by
  let f : PotPair × ℂ → ℂ := fun p => antiDiscrim p.1 p.2
  have hf : HasFDerivAt f (fderiv ℂ f (φ,z)) (φ,z) :=
    (analyticOnNhd_antiDiscrim (φ,z) (mem_univ _)).differentiableAt.hasFDerivAt
  have hcurve : HasDerivAt (fun w : ℂ => (φ,w)) ((0 : PotPair),(1 : ℂ)) z :=
    (hasDerivAt_const z φ).prodMk (hasDerivAt_id z)
  have hs : HasDerivAt (antiDiscrim φ) ((fderiv ℂ f (φ,z)) (0,1)) z :=
    hf.comp_hasDerivAt z hcurve
  exact hs.unique (hasDerivAt_antiDiscrim_spectral38 φ z)

theorem spectralAnti_real (u : PhysicalL2) (x : ℝ) :
    (spectralAntiDiscrimIntegral38 (realSlice u) (x : ℂ)).im=0 := by
  have hf : Differentiable ℂ (antiDiscrim (realSlice u)) := fun z =>
    (analyticOnNhd_antiDiscrim_z (realSlice u) z (mem_univ _)).differentiableAt
  have hr := (realRestriction_deriv38 _ hf
    (fun y => (dirichlet_real_characteristic38 u y).2.1) x).2.1
  rw [deriv_antiDiscrim_spectral38] at hr
  exact hr

end
end NlsGge.GK38.GradEigen38
