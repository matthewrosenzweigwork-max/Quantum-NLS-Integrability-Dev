import NlsGge.GK38.GradTauGammaLocalKernels

/-! Literal pointwise selector gluing and the two-component contour masses.
The squared-gap gradient has the genuine square factor 64. -/
set_option autoImplicit false
open Set Metric
namespace NlsGge.GK38
noncomputable section

theorem k4aTau_selected_eq38 (φ : PotPair) (hφ : φ ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hf : IsolatingFamily38 φ C R) (n : ℤ)
    (t : Icc (0 : ℝ) 1) : gradTau38 φ n t = k4aTauContOnCircle38 φ C R n t := by
  calc
    _ = k4aTauContOnCircle38 φ (discC φ) (discR φ) n t := (gradTauCont38_apply φ hφ n t).symm
    _ = _ := congrArg (fun g : PairKernelCont38 => g t)
      (k4aTauContOnCircle_independent38 φ hφ _ C _ R (isolating_family38 φ hφ) hf n)

theorem k4aGamma_selected_eq38 (φ : PotPair) (hφ : φ ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hf : IsolatingFamily38 φ C R) (n : ℤ)
    (t : Icc (0 : ℝ) 1) : gradGamma2_38 φ n t = k4aGammaContOnCircle38 φ C R n t := by
  calc
    _ = k4aGammaContOnCircle38 φ (discC φ) (discR φ) n t := (gradGamma2Cont38_apply φ hφ n t).symm
    _ = _ := congrArg (fun g : PairKernelCont38 => g t)
      (k4aGammaContOnCircle_independent38 φ hφ _ C _ R (isolating_family38 φ hφ) hf n)

theorem k4aTauCont_component38 (φ : PotPair)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hf : IsolatingFamily38 φ C R) (n : ℤ)
    (t : Icc (0 : ℝ) 1) (i : Fin 2) :
    k4aTauContOnCircle38 φ C R n t i =
      -k4aDiscrimContourVec38 φ (fun z => discrim φ z / perChar φ z) (C n) (R n) t i := by
  let ev : PairKernelCont38 →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) i).comp
      (ContinuousMap.evalCLM ℂ t)
  have hi := k4aQuotientKernelCont_circleIntegrable38 φ C R hf n
  have he := k4aCLM_circleIntegral38 ev (k4aQuotientKernelCont38 φ) (C n) (R n) hi
  change circleIntegral (k4aQuotientKernelCont38 φ) (C n) (R n) t i =
    circleIntegral (fun z => (discrim φ z / perChar φ z) * gradDiscrim38 φ z t i) (C n) (R n) at he
  change -((2 * (Real.pi : ℂ) * Complex.I)⁻¹) *
    circleIntegral (k4aQuotientKernelCont38 φ) (C n) (R n) t i = _
  rw [he]
  change -((2 * (Real.pi : ℂ) * Complex.I)⁻¹) * _ = -((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * _)
  ring

theorem k4aGammaCont_component38 (φ : PotPair)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hf : IsolatingFamily38 φ C R) (n : ℤ)
    (t : Icc (0 : ℝ) 1) (i : Fin 2) :
    k4aGammaContOnCircle38 φ C R n t i =
      -8 * k4aDiscrimContourVec38 φ
        (fun z => (z - tauN φ n) * (discrim φ z / perChar φ z)) (C n) (R n) t i := by
  let ev : PairKernelCont38 →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) i).comp
      (ContinuousMap.evalCLM ℂ t)
  have hi := k4aWeightedKernel_circleIntegrable38 φ C R hf n (tauN φ n)
  have he := k4aCLM_circleIntegral38 ev
    (fun z => (z - tauN φ n) • k4aQuotientKernelCont38 φ z) (C n) (R n) hi
  change circleIntegral (fun z => (z - tauN φ n) • k4aQuotientKernelCont38 φ z)
      (C n) (R n) t i =
    circleIntegral (fun z => (z - tauN φ n) *
      ((discrim φ z / perChar φ z) * gradDiscrim38 φ z t i)) (C n) (R n) at he
  change (-8 * (2 * (Real.pi : ℂ) * Complex.I)⁻¹) *
    circleIntegral (fun z => (z - tauN φ n) • k4aQuotientKernelCont38 φ z) (C n) (R n) t i = _
  rw [he]
  simp only [k4aDiscrimContourVec38, mul_assoc]

theorem k4aPairPointMass_smul38 (a : ℂ) (v : PairVec38) :
    pairPointMass38 (a • v) = ‖a‖ ^ 2 * pairPointMass38 v := by
  simp only [pairPointMass38, Pi.smul_apply, norm_smul, mul_pow]
  ring

theorem k4aTau_gradient_mass_eq38 (φ : PotPair) (hφ : φ ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hf : IsolatingFamily38 φ C R) (n : ℤ)
    (t : Icc (0 : ℝ) 1) :
    pairPointMass38 (gradTau38 φ n t) =
      pairPointMass38 (k4aDiscrimContourVec38 φ
        (fun z => discrim φ z / perChar φ z) (C n) (R n) t) := by
  rw [k4aTau_selected_eq38 φ hφ C R hf n t]
  simp only [pairPointMass38, k4aTauCont_component38 φ C R hf n t, norm_neg]

theorem k4aGamma_gradient_mass_eq38 (φ : PotPair) (hφ : φ ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hf : IsolatingFamily38 φ C R) (n : ℤ)
    (t : Icc (0 : ℝ) 1) :
    pairPointMass38 (gradGamma2_38 φ n t) =
      64 * pairPointMass38 (k4aDiscrimContourVec38 φ
        (fun z => (z - tauN φ n) * (discrim φ z / perChar φ z)) (C n) (R n) t) := by
  rw [k4aGamma_selected_eq38 φ hφ C R hf n t]
  simp only [pairPointMass38, k4aGammaCont_component38 φ C R hf n t, norm_mul, norm_neg,
    Complex.norm_ofNat, mul_pow]
  ring

end
end NlsGge.GK38
