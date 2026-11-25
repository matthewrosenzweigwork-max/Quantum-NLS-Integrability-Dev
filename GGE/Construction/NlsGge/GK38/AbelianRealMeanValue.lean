import NlsGge.GK38.AbelianStdRootAverage
import Mathlib.MeasureTheory.Integral.IntervalIntegral.MeanValue

/-! The standard-root singlepoint mean value is ONLY a real theorem.
UNCOMPILED prospective source; no corresponding complex-valued assertion. -/
set_option autoImplicit false
open Set Metric MeasureTheory
namespace NlsGge.GK38
noncomputable section

/-- The path traverses the actual closed real interval, including a=b. -/
theorem p2RealCosine_mem38 (a b θ : ℝ) (hab : a ≤ b) :
    (a+b)/2+((b-a)/2)*Real.cos θ ∈ Icc a b := by
  have hd : 0 ≤ b-a := sub_nonneg.mpr hab
  have hl := mul_le_mul_of_nonneg_left (Real.neg_one_le_cos θ)
    (div_nonneg hd (by norm_num : 0 ≤ (2:ℝ)))
  have hu := mul_le_mul_of_nonneg_left (Real.cos_le_one θ)
    (div_nonneg hd (by norm_num : 0 ≤ (2:ℝ)))
  constructor <;> nlinarith

/-- A REAL-valued analytic numerator has a REAL mean-value point in the closed gap.
The ambient circle centre remains arbitrary complex. -/
theorem p2StdRoot_real_mean_value38 (a b : ℝ) (hab : a ≤ b) (c : ℂ) (r : ℝ)
    (hr : 0 < r) (hcut : segment ℝ (a:ℂ) (b:ℂ) ⊆ ball c r)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (closedBall c r))
    (hfReal : ∀ x ∈ Icc a b, (f (x:ℂ)).im=0) :
    ∃ x ∈ Icc a b,
      (1/(2*(Real.pi:ℂ)*Complex.I))*
        circleIntegral (fun z => f z/stdRoot38 (((a:ℂ)+b)/2) (((b:ℂ)-a)^2) z) c r =
      -f (x:ℂ) := by
  let x : ℝ → ℝ := fun θ => (a+b)/2+((b-a)/2)*Real.cos θ
  have hx : Continuous x := continuous_const.add (continuous_const.mul Real.continuous_cos)
  have hxi : ∀ θ : ℝ, x θ ∈ Icc a b := fun θ => p2RealCosine_mem38 a b θ hab
  have hxC : ∀ θ : ℝ, (x θ:ℂ)=((a:ℂ)+b)/2+(((b:ℂ)-a)/2)*(Real.cos θ:ℂ) := by
    intro θ
    dsimp [x]
    push_cast
    ring
  have hxb : ∀ θ : ℝ, (x θ:ℂ) ∈ ball c r := by
    intro θ
    rw [hxC]
    exact hcut (p2Cosine_mem_segment38 (a:ℂ) (b:ℂ) θ)
  let g : ℝ → ℝ := fun θ => (f (x θ:ℂ)).re
  have hgc : ContinuousOn g (Icc (0:ℝ) (2*Real.pi)) := by
    exact Complex.continuous_re.continuousOn.comp
      (hf.continuousOn.comp (Complex.continuous_ofReal.comp hx).continuousOn
        (fun θ _ => ball_subset_closedBall (hxb θ))) (fun _ _ => mem_univ _)
  have _hgi : IntervalIntegrable g volume 0 (2*Real.pi) :=
    hgc.intervalIntegrable_of_Icc (by positivity)
  obtain ⟨θ,hθ,hmean⟩ := exists_eq_const_mul_intervalIntegral_of_nonneg (μ := volume)
    (a := (0:ℝ)) (b := 2*Real.pi) (f := g) (g := fun _ => (1:ℝ))
    (by simpa only [uIcc_of_le (by positivity : (0:ℝ) ≤ 2*Real.pi)] using hgc)
    (intervalIntegrable_const) (fun _ _ => zero_le_one)
  simp only [mul_one,intervalIntegral.integral_const,sub_zero,smul_eq_mul] at hmean
  have hre : ∀ θ : ℝ, ((g θ:ℝ):ℂ)=f (x θ:ℂ) := by
    intro θ
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using (hfReal (x θ) (hxi θ)).symm
  have hi : (∫ t in (0:ℝ)..2*Real.pi,f (x t:ℂ))=
      (2*(Real.pi:ℂ))*f (x θ:ℂ) := by
    simp_rw [← hre]
    rw [intervalIntegral.integral_ofReal,hmean]
    push_cast
    ring
  have havg := p2StdRoot_cosine_average38 (a:ℂ) (b:ℂ) c r hr hcut f hf
  refine ⟨x θ,hxi θ,?_⟩
  rw [havg.2.2]
  simp_rw [← hxC]
  rw [hi]
  field_simp [show (Real.pi:ℂ) ≠ 0 by exact_mod_cast Real.pi_ne_zero,Complex.I_ne_zero]

#print axioms p2RealCosine_mem38
#print axioms p2StdRoot_real_mean_value38
end
end NlsGge.GK38
