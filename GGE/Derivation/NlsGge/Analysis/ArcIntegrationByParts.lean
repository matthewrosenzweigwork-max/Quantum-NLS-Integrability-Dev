import NlsGge.Analysis.EllipseDeformation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

set_option autoImplicit false
open Set Metric MeasureTheory
namespace NlsGge.Analysis.ArcIntegrationByParts
noncomputable section

/-- Interior complex primitive derivatives suffice; the endpoints only need continuity. -/
theorem arc_integration_by_parts {γ γ' : ℝ → ℂ} {F f : ℂ → ℂ} {a b : ℝ}
    (hγ : ∀ θ, HasDerivAt γ (γ' θ) θ) (hγ' : Continuous γ')
    (hF : ContinuousOn (fun θ => F (γ θ)) (uIcc a b))
    (hf : ContinuousOn (fun θ => f (γ θ)) (uIcc a b))
    (hd : ∀ θ ∈ Ioo (min a b) (max a b), HasDerivAt F (f (γ θ)) (γ θ)) :
    IntervalIntegrable (fun θ => γ' θ * (γ θ * f (γ θ))) volume a b ∧
      IntervalIntegrable (fun θ => γ' θ * F (γ θ)) volume a b ∧
      (∫ θ in a..b, γ' θ * (γ θ * f (γ θ))) =
        γ b * F (γ b) - γ a * F (γ a) - ∫ θ in a..b, γ' θ * F (γ θ) := by
  have hγc : Continuous γ := continuous_iff_continuousAt.mpr (fun θ => (hγ θ).continuousAt)
  have hi : IntervalIntegrable (fun θ => γ' θ * f (γ θ)) volume a b :=
    (hγ'.continuousOn.mul hf).intervalIntegrable
  have hv : ∀ θ ∈ Ioo (min a b) (max a b),
      HasDerivAt (fun θ => F (γ θ)) (γ' θ * f (γ θ)) θ := by
    intro θ hθ
    have h := (hd θ hθ).scomp θ (hγ θ)
    simpa only [Function.comp_def, smul_eq_mul, mul_comm] using h
  have he := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hγc.continuousOn hF (fun θ _ => hγ θ) hv (hγ'.intervalIntegrable a b) hi
  have hiL : IntervalIntegrable (fun θ => γ' θ * (γ θ * f (γ θ))) volume a b :=
    (hγ'.continuousOn.mul (hγc.continuousOn.mul hf)).intervalIntegrable
  refine ⟨hiL, (hγ'.continuousOn.mul hF).intervalIntegrable, ?_⟩
  convert he using 1
  apply intervalIntegral.integral_congr
  intro θ _
  ring

end
end NlsGge.Analysis.ArcIntegrationByParts
