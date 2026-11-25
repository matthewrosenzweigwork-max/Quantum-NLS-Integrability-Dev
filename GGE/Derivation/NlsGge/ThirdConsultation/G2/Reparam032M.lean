import Mathlib

/- G2-032 B3 (proof development, AUTHOR; SUPPORTING lemma, not a packet; NOT self-reviewed). Mathlib-only.
   Annulus constancy of circle integrals about 0: if F is complex-differentiable at every u with
   a < ‖u‖ < b and 0 ≤ a < r₁ ≤ r₂ < b, the circle integrals of radii r₁ and r₂ agree.
   No continuity or differentiability is assumed on the circles beyond this open annulus. -/
set_option autoImplicit false

open Set Metric
open scoped Real

namespace NlsGge.GKDefinitionDesign
namespace G2032Annulus
noncomputable section

theorem circleIntegral_const_on_annulus (F : ℂ → ℂ) (a b r₁ r₂ : ℝ) (ha : 0 ≤ a)
    (h1 : a < r₁) (h12 : r₁ ≤ r₂) (h2 : r₂ < b)
    (hF : ∀ u : ℂ, a < ‖u‖ → ‖u‖ < b → DifferentiableAt ℂ F u) :
    circleIntegral F 0 r₁ = circleIntegral F 0 r₂ := by
  have hr₁ : 0 < r₁ := lt_of_le_of_lt ha h1
  have hc : ContinuousOn F (Metric.closedBall (0 : ℂ) r₂ \ Metric.ball (0 : ℂ) r₁) := by
    intro u hu
    have hu1 : r₁ ≤ ‖u‖ := by
      have h := hu.2
      rw [mem_ball_zero_iff, not_lt] at h
      exact h
    have hu2 : ‖u‖ ≤ r₂ := by
      have h := hu.1
      rw [mem_closedBall_zero_iff] at h
      exact h
    exact (hF u (lt_of_lt_of_le h1 hu1) (lt_of_le_of_lt hu2 h2)).continuousAt.continuousWithinAt
  have hd : ∀ z ∈ (Metric.ball (0 : ℂ) r₂ \ Metric.closedBall (0 : ℂ) r₁) \ (∅ : Set ℂ),
      DifferentiableAt ℂ F z := by
    intro z hz
    have hz1 : r₁ < ‖z‖ := by
      have h := hz.1.2
      rw [mem_closedBall_zero_iff, not_le] at h
      exact h
    have hz2 : ‖z‖ < r₂ := by
      have h := hz.1.1
      rw [mem_ball_zero_iff] at h
      exact h
    exact hF z (lt_trans h1 hz1) (lt_trans hz2 h2)
  exact (Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable hr₁ h12
    Set.countable_empty hc hd).symm

end
end G2032Annulus
end NlsGge.GKDefinitionDesign
