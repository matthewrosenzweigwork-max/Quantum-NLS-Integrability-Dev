import NlsGge.GK38.AbelianComplexCurveParameter
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! SOURCE ONLY: genuine complex-valued arctan curve substitution.
Both scalar CIs are earned BEFORE substitution. Actual circle curves will
realize this generic C1 primitive. Exact target+English preceded proof.
UNCOMPILED; no new scientific native scope. -/
set_option autoImplicit false
open Set MeasureTheory
open scoped Interval
namespace NlsGge.GK38
noncomputable section

theorem p6Complex_arctan_curve_substitution38 (g : ℝ → ℂ) (hg : ContDiff ℝ 1 g)
    (f : ℂ → ℂ)
    (hf : ContinuousOn f (g '' Set.Icc (-Real.pi/4) (Real.pi/4))) :
    IntervalIntegrable (fun y : ℝ => f ((g ∘ Real.arctan) y)*deriv (g ∘ Real.arctan) y)
      volume (-1) 1 ∧
    IntervalIntegrable (fun θ : ℝ => f (g θ)*deriv g θ)
      volume (-Real.pi/4) (Real.pi/4) ∧
    (∫ y : ℝ in (-1 : ℝ)..1,
      f ((g ∘ Real.arctan) y)*deriv (g ∘ Real.arctan) y) =
      ∫ θ : ℝ in (-Real.pi/4)..(Real.pi/4), f (g θ)*deriv g θ := by
  have hangle : -(Real.pi)/4 ≤ Real.pi/4 := by linarith [Real.pi_pos]
  have hmap : MapsTo Real.arctan (Set.Icc (-1 : ℝ) 1)
      (Set.Icc (-Real.pi/4) (Real.pi/4)) := by
    intro y hy
    have hl := Real.arctan_mono hy.1
    have hu := Real.arctan_mono hy.2
    simpa [Real.arctan_neg, Real.arctan_one, neg_div] using And.intro hl hu
  have hfg : ContinuousOn (fun θ : ℝ => f (g θ)) (Set.Icc (-Real.pi/4) (Real.pi/4)) :=
    hf.comp hg.continuous.continuousOn (fun θ hθ => mem_image_of_mem g hθ)
  have hG : ContinuousOn (fun θ : ℝ => f (g θ)*deriv g θ)
      (Set.Icc (-Real.pi/4) (Real.pi/4)) :=
    hfg.mul hg.continuous_deriv_one.continuousOn
  have hcomp : ContDiff ℝ 1 (g ∘ Real.arctan) := hg.comp Real.contDiff_arctan
  have hCIy : IntervalIntegrable
      (fun y : ℝ => f ((g ∘ Real.arctan) y)*deriv (g ∘ Real.arctan) y) volume (-1) 1 :=
    ((hfg.comp Real.continuous_arctan.continuousOn hmap).mul
      hcomp.continuous_deriv_one.continuousOn).intervalIntegrable_of_Icc (by norm_num)
  have hCIθ : IntervalIntegrable (fun θ : ℝ => f (g θ)*deriv g θ)
      volume (-Real.pi/4) (Real.pi/4) := hG.intervalIntegrable_of_Icc hangle
  refine ⟨hCIy,hCIθ,?_⟩
  have hchange := intervalIntegral.integral_deriv_smul_comp'
    (a := (-1 : ℝ)) (b := 1) (fun y _ => Real.hasDerivAt_arctan y)
    (show ContinuousOn (fun y : ℝ => 1/(1+y^2)) (Set.uIcc (-1 : ℝ) 1) from
      (continuous_const.div (continuous_const.add (continuous_id.pow 2))
        (fun y : ℝ => ne_of_gt (by positivity : 0 < 1+y^2))).continuousOn)
    (g := fun θ : ℝ => f (g θ)*deriv g θ) (by
      apply hG.mono
      rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
      exact hmap.image_subset)
  have hderiv (y : ℝ) : deriv (g ∘ Real.arctan) y =
      (1/(1+y^2)) • deriv g (Real.arctan y) :=
    ((hg.differentiable (by norm_num) (Real.arctan y)).hasDerivAt.scomp y
      (Real.hasDerivAt_arctan y)).deriv
  calc
    _ = ∫ y : ℝ in (-1 : ℝ)..1,
        (1/(1+y^2)) • (f (g (Real.arctan y))*deriv g (Real.arctan y)) := by
      apply intervalIntegral.integral_congr
      intro y hy
      change f (g (Real.arctan y))*deriv (g ∘ Real.arctan) y =
        (1/(1+y^2)) • (f (g (Real.arctan y))*deriv g (Real.arctan y))
      rw [hderiv, mul_smul_comm]
    _ = _ := by simpa [Real.arctan_neg, Real.arctan_one, neg_div] using hchange

end
end NlsGge.GK38
