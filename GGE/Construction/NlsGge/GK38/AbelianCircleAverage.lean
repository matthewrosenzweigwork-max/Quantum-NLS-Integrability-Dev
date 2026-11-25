import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! Ordinary Cauchy/Fubini prerequisites for P2, with integrability earned first.
UNCOMPILED prospective proof source; no standard-root averaging identity is assumed. -/
set_option autoImplicit false
open Set Metric MeasureTheory
namespace NlsGge.GK38
noncomputable section

/-- A continuous two-parameter integrand on the actual compact circle rectangle is
integrable before the order of integration is changed. -/
theorem p2Circle_interval_swap38 (c : ℂ) (r a b : ℝ) (hr : 0 ≤ r) (hab : a ≤ b)
    (g : ℝ → ℂ → ℂ)
    (hg : ContinuousOn (fun p : ℝ × ℂ => g p.1 p.2) (Icc a b ×ˢ sphere c r)) :
    (∀ θ ∈ Icc a b, CircleIntegrable (g θ) c r) ∧
    (∀ z ∈ sphere c r, IntervalIntegrable (fun θ => g θ z) volume a b) ∧
    circleIntegral (fun z => ∫ θ in a..b, g θ z) c r =
      ∫ θ in a..b, circleIntegral (g θ) c r := by
  have hcircle : ∀ θ ∈ Icc a b, CircleIntegrable (g θ) c r := by
    intro θ hθ
    apply ContinuousOn.circleIntegrable hr
    exact hg.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun z hz => ⟨hθ,hz⟩)
  have hinterval : ∀ z ∈ sphere c r,
      IntervalIntegrable (fun θ => g θ z) volume a b := by
    intro z hz
    exact (hg.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun θ hθ => ⟨hθ,hz⟩)).intervalIntegrable_of_Icc hab
  let F : ℝ → ℝ → ℂ := fun α θ =>
    deriv (circleMap c r) α * g θ (circleMap c r α)
  have hF : ContinuousOn F.uncurry (Icc (0:ℝ) (2*Real.pi) ×ˢ Icc a b) := by
    apply ContinuousOn.mul
    · simp only [deriv_circleMap]
      exact ((continuous_circleMap 0 r).comp continuous_fst).mul_const Complex.I
        |>.continuousOn
    · exact hg.comp
        (continuous_snd.prodMk ((continuous_circleMap c r).comp continuous_fst)).continuousOn
        (fun p hp => ⟨hp.2,circleMap_mem_sphere c hr p.1⟩)
  have hInt : IntegrableOn F.uncurry
      (uIoc (0:ℝ) (2*Real.pi) ×ˢ uIoc a b) := by
    apply (hF.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    rw [uIoc_of_le (by positivity),uIoc_of_le hab]
    exact Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self
  refine ⟨hcircle,hinterval,?_⟩
  simp only [circleIntegral,smul_eq_mul]
  simp_rw [← intervalIntegral.integral_const_mul]
  exact intervalIntegral_intervalIntegral_swap hInt

/-- Cauchy at every actual interior point of a continuous path, then genuine compact
Fubini. Complex paths and complex-valued f are retained; there is no mean-value point. -/
theorem p2Cauchy_circle_interval38 (c : ℂ) (r a b : ℝ) (hr : 0 < r) (hab : a ≤ b)
    (x : ℝ → ℂ) (hx : ContinuousOn x (Icc a b))
    (hxb : ∀ θ ∈ Icc a b, x θ ∈ ball c r)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (closedBall c r)) :
    (∀ θ ∈ Icc a b, CircleIntegrable (fun z => f z/(z-x θ)) c r) ∧
    circleIntegral (fun z => ∫ θ in a..b, f z/(z-x θ)) c r =
      (2*(Real.pi:ℂ)*Complex.I)*(∫ θ in a..b, f (x θ)) := by
  have hj : ContinuousOn (fun p : ℝ × ℂ => f p.2/(p.2-x p.1))
      (Icc a b ×ˢ sphere c r) := by
    apply ContinuousOn.div
    · exact hf.continuousOn.comp continuous_snd.continuousOn
        (fun p hp => sphere_subset_closedBall hp.2)
    · exact continuous_snd.continuousOn.sub
        (hx.comp continuous_fst.continuousOn (fun p hp => hp.1))
    · intro p hp he
      have hEq := sub_eq_zero.mp he
      have hd := hxb p.1 hp.1
      rw [← hEq,mem_ball] at hd
      exact (ne_of_lt hd) (mem_sphere.mp hp.2)
  have hpath : ContinuousOn (fun θ => f (x θ)) (Icc a b) :=
    hf.continuousOn.comp hx (fun θ hθ => ball_subset_closedBall (hxb θ hθ))
  have _hpathIntegrable : IntervalIntegrable (fun θ => f (x θ)) volume a b :=
    hpath.intervalIntegrable_of_Icc hab
  have hswap := p2Circle_interval_swap38 c r a b hr.le hab
    (fun θ z => f z/(z-x θ)) hj
  refine ⟨hswap.1,hswap.2.2.trans ?_⟩
  calc
    (∫ θ in a..b, circleIntegral (fun z => f z/(z-x θ)) c r) =
        ∫ θ in a..b, (2*(Real.pi:ℂ)*Complex.I)*f (x θ) := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      rw [uIcc_of_le hab] at hθ
      simpa only [div_eq_inv_mul,smul_eq_mul] using
        hf.differentiableOn.circleIntegral_sub_inv_smul (hxb θ hθ)
    _ = _ := intervalIntegral.integral_const_mul _ _

#print axioms p2Circle_interval_swap38
#print axioms p2Cauchy_circle_interval38
end
end NlsGge.GK38
