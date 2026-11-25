import Mathlib
import NlsGge.ThirdConsultation.G2.Reparam032B
import NlsGge.ThirdConsultation.G2.Reparam032C
import NlsGge.ThirdConsultation.G2.Reparam032D

                                                                                                         
                                                                                                
                                                   
                                                           
                                                                                                        
                                                                                           
set_option autoImplicit false
open scoped Real

namespace NlsGge.GKDefinitionDesign
namespace G2032Theta
noncomputable section

open NlsGge.GKDefinitionDesign.G2032Lift NlsGge.GKDefinitionDesign.G2032Homotopy

/-- Direction of the circle lift: `f(θ)/‖f(θ)‖ = exp(i·liftAngle θ)`. This is the last component of
`lift_circle`, stated for the specific angle function `liftAngle`. -/
theorem liftF_dir (w : ℂ) (R : ℝ) (hR : 0 < R) (hw : ‖w‖ < R) (θ : ℝ) :
    liftF w R θ / ((‖liftF w R θ‖ : ℝ) : ℂ) =
      Complex.exp (((liftAngle w R θ : ℝ) : ℂ) * Complex.I) := by
  have hG1 : liftG w R θ = 1 := (hasDerivAt_liftG_const w R hR hw θ).trans (liftG_zero w R hR hw)
  have hρpos : 0 < liftRho w R θ := Real.sqrt_pos.2 (normSq_liftF_pos w R hR hw θ)
  have hρne : ((liftRho w R θ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hρpos.ne'
  unfold liftG at hG1
  rw [div_eq_one_iff_eq hρne] at hG1
  have hinv : Complex.exp (-(Complex.I * ((liftAngle w R θ : ℝ) : ℂ))) *
      Complex.exp (((liftAngle w R θ : ℝ) : ℂ) * Complex.I) = 1 := by
    rw [← Complex.exp_add, show -(Complex.I * ((liftAngle w R θ : ℝ) : ℂ)) +
      ((liftAngle w R θ : ℝ) : ℂ) * Complex.I = 0 by ring, Complex.exp_zero]
  have hFeq : liftF w R θ = ((liftRho w R θ : ℝ) : ℂ) *
      Complex.exp (((liftAngle w R θ : ℝ) : ℂ) * Complex.I) := by
    have h : liftF w R θ = (liftF w R θ * Complex.exp (-(Complex.I * ((liftAngle w R θ : ℝ) : ℂ)))) *
        Complex.exp (((liftAngle w R θ : ℝ) : ℂ) * Complex.I) := by
      rw [mul_assoc, hinv, mul_one]
    rw [hG1] at h
    exact h
  rw [← liftRho_eq_norm w R θ, hFeq, mul_div_cancel_left₀ _ hρne]

/-- The circle point seen from `τ`: `C + R e^{iθ} = τ + ‖f(θ)‖ e^{i·liftAngle θ}`, where
`f = liftF (C − τ) R`. -/
theorem circle_point (τ C : ℂ) (R : ℝ) (hR : 0 < R) (hw' : ‖C - τ‖ < R) (θ : ℝ) :
    C + (R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) =
      τ + ((‖liftF (C - τ) R θ‖ : ℝ) : ℂ) *
        Complex.exp (((liftAngle (C - τ) R θ : ℝ) : ℂ) * Complex.I) := by
  have hne : ((‖liftF (C - τ) R θ‖ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (liftF_norm_pos (C - τ) R hR hw' θ).ne'
  have hF : liftF (C - τ) R θ = ((‖liftF (C - τ) R θ‖ : ℝ) : ℂ) *
      Complex.exp (((liftAngle (C - τ) R θ : ℝ) : ℂ) * Complex.I) := by
    rw [← liftF_dir (C - τ) R hR hw' θ]
    field_simp
  have hlift : liftF (C - τ) R θ = (C - τ) + (R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := rfl
  rw [← hF, hlift]
  ring

/-- Uniqueness of the positive exit radius: a positive `r` with `‖w + r e^{iα}‖ = R` equals `rayR`. -/
theorem rayR_eq_of_normSq (w : ℂ) (R : ℝ) (α r : ℝ) (hwR : w.re ^ 2 + w.im ^ 2 < R ^ 2)
    (hr : 0 < r)
    (h : Complex.normSq (w + (r : ℂ) * Complex.exp ((α : ℂ) * Complex.I)) = R ^ 2) :
    r = rayR w R α := by
  rw [normSq_point] at h
  have hs : Real.sqrt (rayD w R α) ^ 2 = rayD w R α := Real.sq_sqrt (rayD_nonneg w R α hwR)
  have hb := abs_rayB_lt_sqrt w R α hwR
  have hlow := (abs_lt.mp hb).1
  unfold rayD at hs
  have hprod : (r + rayB w α - Real.sqrt (rayD w R α)) *
      (r + rayB w α + Real.sqrt (rayD w R α)) = 0 := by
    unfold rayD
    linear_combination h - hs
  rcases mul_eq_zero.mp hprod with h1 | h1
  · unfold rayR
    linarith
  · exfalso
    linarith

/-- The exit relation for one parameter: if `τ + r e^{ix} = C + R e^{iθ}` with `r > 0`,
then `r = rayR (τ − C) R x`. -/
theorem relation_at (τ C : ℂ) (R : ℝ) (hR : 0 < R) (hwR : (τ - C).re ^ 2 + (τ - C).im ^ 2 < R ^ 2)
    (θ x r : ℝ) (hr : 0 < r) (hcp : C + (R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) =
      τ + ((r : ℝ) : ℂ) * Complex.exp ((x : ℂ) * Complex.I)) :
    C + (R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) =
      τ + ((rayR (τ - C) R x : ℝ) : ℂ) * Complex.exp ((x : ℂ) * Complex.I) := by
  have hn : Complex.normSq ((τ - C) + ((r : ℝ) : ℂ) * Complex.exp ((x : ℂ) * Complex.I)) = R ^ 2 := by
    have hz : (τ - C) + ((r : ℝ) : ℂ) * Complex.exp ((x : ℂ) * Complex.I) =
        (R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
      linear_combination (-1 : ℂ) * hcp
    rw [hz, Complex.normSq_eq_norm_sq, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
      Complex.norm_real, Real.norm_of_nonneg hR.le]
  have hreq := rayR_eq_of_normSq (τ - C) R x r hwR hr hn
  rw [← hreq]
  exact hcp

/-- THETA032: the angle `θ = β_c ∘ β` lifts the ray angle of the ellipse to the circle. -/
theorem theta_exists (τ C : ℂ) (R : ℝ) (hw : ‖τ - C‖ < R) (β : ℝ → ℝ)
    (hβ : ContDiff ℝ 1 β) (hβm : StrictMono β) (hβp : ∀ t, β (t + 2 * π) = β t + 2 * π) :
    ∃ θ : ℝ → ℝ, ContDiff ℝ 1 θ ∧ StrictMono θ ∧ (∀ t, θ (t + 2 * π) = θ t + 2 * π) ∧
      ∀ t, C + (R : ℂ) * Complex.exp (((θ t : ℝ) : ℂ) * Complex.I) =
        τ + ((rayR (τ - C) R (β t) : ℝ) : ℂ) * Complex.exp (((β t : ℝ) : ℂ) * Complex.I) := by
  have hR : 0 < R := lt_of_le_of_lt (norm_nonneg _) hw
  have hw' : ‖C - τ‖ < R := by rwa [norm_sub_rev]
  have hwR : (τ - C).re ^ 2 + (τ - C).im ^ 2 < R ^ 2 := by
    have h1 : (τ - C).re ^ 2 + (τ - C).im ^ 2 = ‖τ - C‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    rw [h1]
    nlinarith [norm_nonneg (τ - C)]
  obtain ⟨βc, hβc1, hβc2, hβcm, hβcd, hβcp, hβcc⟩ := lift_inverse (C - τ) R hR hw'
  have hβcC1 : ContDiff ℝ 1 βc := by
    rw [contDiff_one_iff_deriv]
    refine ⟨fun x => (hβcd x).differentiableAt, ?_⟩
    have hder : deriv βc = fun x => 1 / liftRate (C - τ) R (βc x) :=
      funext fun x => (hβcd x).deriv
    rw [hder]
    exact Continuous.div continuous_const
      ((liftRate_continuous (C - τ) R hR hw').comp hβcc)
      (fun x => (liftRate_pos (C - τ) R hR hw' (βc x)).ne')
  refine ⟨fun t => βc (β t), hβcC1.comp hβ, hβcm.comp hβm, ?_, ?_⟩
  · intro t
    show βc (β (t + 2 * π)) = βc (β t) + 2 * π
    rw [hβp, hβcp]
  · intro t
    have hr : 0 < ‖liftF (C - τ) R (βc (β t))‖ := liftF_norm_pos (C - τ) R hR hw' _
    have hcp := circle_point τ C R hR hw' (βc (β t))
    rw [hβc1 (β t)] at hcp
    exact relation_at τ C R hR hwR (βc (β t)) (β t) _ hr hcp

/-- Selftest: the hypotheses are satisfiable (τ = C = 0, R = 1, β = id), so the conclusion is not vacuous. -/
example : ∃ θ : ℝ → ℝ, ContDiff ℝ 1 θ ∧ StrictMono θ := by
  obtain ⟨θ, h1, h2, -⟩ := theta_exists 0 0 1 (by simp) id contDiff_id strictMono_id
    (fun t => rfl)
  exact ⟨θ, h1, h2⟩

end
end G2032Theta
end NlsGge.GKDefinitionDesign

