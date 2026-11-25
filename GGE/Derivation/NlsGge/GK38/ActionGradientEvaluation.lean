import NlsGge.GK38.ActionGradientQuotient

set_option autoImplicit false
open Set Metric Filter Topology MeasureTheory
open NlsGge.GK38 NlsGge.Pilot
namespace NlsGge.GK38.ActionGradient
noncomputable section

theorem circleIntegral_gradRootQuotient_apply (φ : PotPair) (hφ : φ ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hf : IsolatingFamily38 φ C R) (n : ℤ) (h : PotPair) :
    (circleIntegral (gradRootQuotient φ) (C n) (R n)) h =
      circleIntegral (fun z => gradDiscrimCLM φ z h / canonRoot38 φ z) (C n) (R n) := by
  have hi := gradRootQuotient_circle_integrable φ hφ C R hf n
  have hih := gradRootQuotient_direction_circle_integrable φ hφ C R hf n h
  unfold circleIntegral
  rw [ContinuousLinearMap.intervalIntegral_apply hi.out h]
  apply intervalIntegral.integral_congr
  intro θ _
  change deriv (circleMap (C n) (R n)) θ *
      ((canonRoot38 φ (circleMap (C n) (R n) θ))⁻¹ *
        gradDiscrimCLM φ (circleMap (C n) (R n) θ) h) =
    deriv (circleMap (C n) (R n)) θ *
      (gradDiscrimCLM φ (circleMap (C n) (R n) θ) h /
        canonRoot38 φ (circleMap (C n) (R n) θ))
  rw [div_eq_mul_inv]
  ring

theorem actionGradientCLM_apply (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) (h : PotPair) :
    actionGradientCLM38 φ n h = -(1 / (Real.pi : ℂ)) *
      circleIntegral (fun z => gradDiscrimCLM φ z h / canonRoot38 φ z)
        (discC φ n) (discR φ n) := by
  change -(1 / (Real.pi : ℂ)) *
    (circleIntegral (gradRootQuotient φ) (discC φ n) (discR φ n)) h = _
  rw [circleIntegral_gradRootQuotient_apply φ hφ _ _ (isolating_family38 φ hφ) n h]

end
end NlsGge.GK38.ActionGradient
