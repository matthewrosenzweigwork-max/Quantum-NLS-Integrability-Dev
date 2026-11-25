import Mathlib

                                                                                                
                                                                                
                                                                             
                                                              
                                                                                             
                                                                                     
set_option autoImplicit false

open Set Metric
open scoped Real

namespace NlsGge.GKDefinitionDesign
namespace G2032Chain
noncomputable section

/-- The ellipse parametrization `t ↦ p e^{it} + q e^{-it}` (same expression as `G2032Ellipse.ellF`). -/
def ellP (p q : ℂ) (t : ℝ) : ℂ :=
  p * Complex.exp ((t : ℂ) * Complex.I) + q * Complex.exp (-((t : ℂ) * Complex.I))

theorem hasDerivAt_ellP (p q : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ellP p q s)
      (p * Complex.exp ((t : ℂ) * Complex.I) * Complex.I -
        q * Complex.exp (-((t : ℂ) * Complex.I)) * Complex.I) t := by
  have hc : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
    simpa using (hasDerivAt_id' t).ofReal_comp
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) * Complex.I) (1 * Complex.I) t :=
    hc.mul_const Complex.I
  have h2 : HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * Complex.I))
      (Complex.exp ((t : ℂ) * Complex.I) * (1 * Complex.I)) t := h1.cexp
  have h3 : HasDerivAt (fun s : ℝ => -((s : ℂ) * Complex.I)) (-(1 * Complex.I)) t := h1.neg
  have h4 : HasDerivAt (fun s : ℝ => Complex.exp (-((s : ℂ) * Complex.I)))
      (Complex.exp (-((t : ℂ) * Complex.I)) * (-(1 * Complex.I))) t := h3.cexp
  exact ((h2.const_mul p).add (h4.const_mul q)).congr_deriv (by ring)

theorem deriv_ellP (p q : ℂ) (t : ℝ) :
    deriv (fun s : ℝ => ellP p q s) t =
      p * Complex.exp ((t : ℂ) * Complex.I) * Complex.I -
        q * Complex.exp (-((t : ℂ) * Complex.I)) * Complex.I :=
  (hasDerivAt_ellP p q t).deriv

/-- Pointwise Joukowski identity on the ray `u = ρ e^{it}` (with `ρ ≠ 0`). -/
theorem joukowski_pointwise (γ : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (t : ℝ) :
    γ / 4 * (ρ : ℂ) * Complex.exp ((t : ℂ) * Complex.I) * Complex.I -
        γ / 4 * ((ρ : ℂ))⁻¹ * (Complex.exp ((t : ℂ) * Complex.I))⁻¹ * Complex.I =
      (ρ : ℂ) * Complex.exp ((t : ℂ) * Complex.I) * Complex.I *
        (γ / 4 * (1 - (((ρ : ℂ) * Complex.exp ((t : ℂ) * Complex.I)) ^ 2)⁻¹)) := by
  have hρc : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hρ.ne'
  have hE : Complex.exp ((t : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  generalize Complex.exp ((t : ℂ) * Complex.I) = E at hE ⊢
  field_simp

/-- Ellipse chain rule: the curve integral along the ellipse equals the circle integral in the
Joukowski variable `u`, for every function `f : ℂ → ℂ` (no analyticity needed). -/
theorem ellipse_chain (f : ℂ → ℂ) (τ γ : ℂ) (ρ : ℝ) (hρ : 0 < ρ) :
    (∫ t in (0 : ℝ)..(2 * π),
        f (τ + ellP (γ / 4 * (ρ : ℂ)) (γ / 4 * ((ρ⁻¹ : ℝ) : ℂ)) t) *
          deriv (fun s : ℝ => ellP (γ / 4 * (ρ : ℂ)) (γ / 4 * ((ρ⁻¹ : ℝ) : ℂ)) s) t) =
      circleIntegral (fun u : ℂ => f (τ + γ / 4 * (u + u⁻¹)) * (γ / 4 * (1 - (u ^ 2)⁻¹))) 0 ρ := by
  unfold circleIntegral
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  dsimp only
  simp only [deriv_circleMap, circleMap_zero, smul_eq_mul]
  rw [deriv_ellP]
  have hρinv : ((ρ⁻¹ : ℝ) : ℂ) = (ρ : ℂ)⁻¹ := Complex.ofReal_inv ρ
  have hEinv : Complex.exp (-((t : ℂ) * Complex.I)) =
      (Complex.exp ((t : ℂ) * Complex.I))⁻¹ := Complex.exp_neg _
  unfold ellP
  rw [hρinv, hEinv]
  have harg : τ + (γ / 4 * (ρ : ℂ) * Complex.exp ((t : ℂ) * Complex.I) +
      γ / 4 * (ρ : ℂ)⁻¹ * (Complex.exp ((t : ℂ) * Complex.I))⁻¹) =
      τ + γ / 4 * ((ρ : ℂ) * Complex.exp ((t : ℂ) * Complex.I) +
        ((ρ : ℂ) * Complex.exp ((t : ℂ) * Complex.I))⁻¹) := by
    rw [mul_inv]; ring
  rw [harg, joukowski_pointwise γ ρ hρ t]
  ring

end
end G2032Chain
end NlsGge.GKDefinitionDesign
