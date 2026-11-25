import NlsGge.GK38.AbelianComplexCurveParameter
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.Linarith

/-! SOURCE ONLY: normalizedunitparameter to actual[-1,1] complexcurve.
Both scalar CIs precede the genuine vector-valued substitution. No contour
identity or derivative-factor oracle. Exact target+English preceded proof.
UNCOMPILED, outside current next4 scope. -/
set_option autoImplicit false
open Set MeasureTheory
open scoped Interval
namespace NlsGge.GK38
noncomputable section

theorem p6Complex_affine_curve_substitution38 (g : ℝ → ℂ) (hg : ContDiff ℝ 1 g)
    (f : ℂ → ℂ) (hf : ContinuousOn f (g '' Set.Icc (-1 : ℝ) 1)) :
    IntervalIntegrable (fun u : ℝ => f (g (2*u-1))*deriv (fun v : ℝ => g (2*v-1)) u)
      volume 0 1 ∧
    IntervalIntegrable (fun y : ℝ => f (g y)*deriv g y) volume (-1) 1 ∧
    (∫ u : ℝ in (0 : ℝ)..1, f (g (2*u-1))*deriv (fun v : ℝ => g (2*v-1)) u) =
      ∫ y : ℝ in (-1 : ℝ)..1, f (g y)*deriv g y := by
  have hmap : MapsTo (fun u : ℝ => 2*u-1) (Set.Icc (0 : ℝ) 1) (Set.Icc (-1 : ℝ) 1) := by
    intro u hu
    constructor <;> linarith [hu.1,hu.2]
  have hσ (u : ℝ) : HasDerivAt (fun v : ℝ => 2*v-1) 2 u := by
    simpa using (((hasDerivAt_id u).const_mul (2 : ℝ)).sub_const 1)
  have hfg : ContinuousOn (fun y : ℝ => f (g y)) (Set.Icc (-1 : ℝ) 1) :=
    hf.comp hg.continuous.continuousOn (fun y hy => mem_image_of_mem g hy)
  have hG : ContinuousOn (fun y : ℝ => f (g y)*deriv g y) (Set.Icc (-1 : ℝ) 1) :=
    hfg.mul hg.continuous_deriv_one.continuousOn
  have hcomp : ContDiff ℝ 1 (fun v : ℝ => g (2*v-1)) :=
    hg.comp (show ContDiff ℝ 1 (fun v : ℝ => 2*v-1) from by fun_prop)
  have hCIu : IntervalIntegrable
      (fun u : ℝ => f (g (2*u-1))*deriv (fun v : ℝ => g (2*v-1)) u) volume 0 1 :=
    ((hfg.comp (show ContinuousOn (fun u : ℝ => 2*u-1) (Set.Icc (0 : ℝ) 1) from by fun_prop)
      hmap).mul hcomp.continuous_deriv_one.continuousOn).intervalIntegrable_of_Icc zero_le_one
  have hCIy : IntervalIntegrable (fun y : ℝ => f (g y)*deriv g y) volume (-1) 1 :=
    hG.intervalIntegrable_of_Icc (by norm_num : (-1 : ℝ) ≤ 1)
  refine ⟨hCIu,hCIy,?_⟩
  have hchange := intervalIntegral.integral_deriv_smul_comp'
    (a := (0 : ℝ)) (b := 1) (fun u _ => hσ u) continuousOn_const
    (g := fun y : ℝ => f (g y)*deriv g y) (by
      apply hG.mono
      rw [Set.uIcc_of_le zero_le_one]
      exact hmap.image_subset)
  have hderiv (u : ℝ) : deriv (fun v : ℝ => g (2*v-1)) u =
      (2 : ℝ) • deriv g (2*u-1) :=
    ((hg.differentiable_one (2*u-1)).hasDerivAt.scomp u (hσ u)).deriv
  calc
    _ = ∫ u : ℝ in (0 : ℝ)..1, (2 : ℝ) • (f (g (2*u-1))*deriv g (2*u-1)) := by
      apply intervalIntegral.integral_congr
      intro u hu
      change f (g (2*u-1))*deriv (fun v : ℝ => g (2*v-1)) u =
        (2 : ℝ) • (f (g (2*u-1))*deriv g (2*u-1))
      rw [hderiv,mul_smul_comm]
    _ = _ := by simpa [show (2 : ℝ)-1=1 by norm_num] using hchange

end
end NlsGge.GK38
