import NlsGge.GK38.AbelianResolvent
import NlsGge.GK38.AbelianCircleAverage

/-! Exact standard-root cosine average and complex norm estimate.
UNCOMPILED prospective source. Endpoints are arbitrary complex, including collapse. -/
set_option autoImplicit false
open Set Metric MeasureTheory
namespace NlsGge.GK38
noncomputable section

/-- Off the actual cut, continuity follows from the actual slit branch. -/
theorem p2StdRoot_continuousOn_offcut38 (a b : ℂ) :
    ContinuousOn (stdRoot38 ((a+b)/2) ((b-a)^2)) (segment ℝ a b)ᶜ := by
  intro z hz
  have hs := stdRoot_slit38 a b z hz
  have ha : AnalyticAt ℂ (stdRoot38 ((a+b)/2) ((b-a)^2)) z :=
    stdRoot_analyticAt38 analyticAt_const analyticAt_const analyticAt_id hs.1 hs.2
  exact ha.continuousAt.continuousWithinAt

/-- The full complex contour average, with genuine circle/interval integrability first.
There is no complex singlepoint mean-value claim. -/
theorem p2StdRoot_cosine_average38 (a b c : ℂ) (r : ℝ) (hr : 0 < r)
    (hcut : segment ℝ a b ⊆ ball c r) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (closedBall c r)) :
    CircleIntegrable (fun z : ℂ => f z/stdRoot38 ((a+b)/2) ((b-a)^2) z) c r ∧
    IntervalIntegrable (fun θ : ℝ => f ((a+b)/2+((b-a)/2)*(Real.cos θ:ℂ)))
      volume 0 (2*Real.pi) ∧
    circleIntegral (fun z : ℂ => f z/stdRoot38 ((a+b)/2) ((b-a)^2) z) c r =
      -Complex.I*(∫ θ in (0:ℝ)..2*Real.pi, f ((a+b)/2+((b-a)/2)*(Real.cos θ:ℂ))) := by
  let x : ℝ → ℂ := fun θ => (a+b)/2+((b-a)/2)*(Real.cos θ:ℂ)
  let R : ℂ → ℂ := stdRoot38 ((a+b)/2) ((b-a)^2)
  have hx : Continuous x := continuous_const.add
    (continuous_const.mul (Complex.continuous_ofReal.comp Real.continuous_cos))
  have hxb : ∀ θ : ℝ, x θ ∈ ball c r := fun θ => hcut (p2Cosine_mem_segment38 a b θ)
  have hzs : sphere c r ⊆ (segment ℝ a b)ᶜ := by
    intro z hz hzc
    exact (not_lt.mpr (mem_sphere.mp hz).ge) (mem_ball.mp (hcut hzc))
  have hci : CircleIntegrable (fun z : ℂ => f z/R z) c r := by
    apply ContinuousOn.circleIntegrable hr.le
    apply ContinuousOn.div
    · exact hf.continuousOn.mono sphere_subset_closedBall
    · exact (p2StdRoot_continuousOn_offcut38 a b).mono hzs
    · intro z hz
      exact stdRoot_ne_zero38 a b z (hzs hz)
  have hfx : ContinuousOn (fun θ => f (x θ)) (Icc (0:ℝ) (2*Real.pi)) :=
    hf.continuousOn.comp hx.continuousOn
      (fun θ _ => ball_subset_closedBall (hxb θ))
  have hifx : IntervalIntegrable (fun θ => f (x θ)) volume 0 (2*Real.pi) :=
    hfx.intervalIntegrable_of_Icc (by positivity)
  have hC := p2Cauchy_circle_interval38 c r 0 (2*Real.pi) hr (by positivity)
    x hx.continuousOn (fun θ _ => hxb θ) f hf
  have he : EqOn (fun z => f z/R z)
      (fun z => (-(1/(2*(Real.pi:ℂ))))*(∫ θ in (0:ℝ)..2*Real.pi,f z/(z-x θ)))
      (sphere c r) := by
    intro z hz
    have hs := p2StdRoot_cosine_resolvent38 a b z (hzs hz)
    have hfct : (∫ θ in (0:ℝ)..2*Real.pi,f z/(z-x θ)) =
        f z*(∫ θ in (0:ℝ)..2*Real.pi,1/(z-(a+b)/2-((b-a)/2)*(Real.cos θ:ℂ))) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro θ _
      dsimp [x]
      ring
    change f z/R z = (-(1/(2*(Real.pi:ℂ))))*(∫ θ in (0:ℝ)..2*Real.pi,f z/(z-x θ))
    rw [hfct,hs.2]
    dsimp [R]
    field_simp [show (Real.pi:ℂ) ≠ 0 by exact_mod_cast Real.pi_ne_zero,
      stdRoot_ne_zero38 a b z (hzs hz)]
  refine ⟨hci,hifx,?_⟩
  calc
    circleIntegral (fun z => f z/R z) c r =
        circleIntegral (fun z => (-(1/(2*(Real.pi:ℂ))))*
          (∫ θ in (0:ℝ)..2*Real.pi,f z/(z-x θ))) c r :=
      circleIntegral.integral_congr hr.le he
    _ = (-(1/(2*(Real.pi:ℂ))))*
        ((2*(Real.pi:ℂ)*Complex.I)*(∫ θ in (0:ℝ)..2*Real.pi,f (x θ))) := by
      rw [circleIntegral.integral_const_mul,hC.2]
    _ = -Complex.I*(∫ θ in (0:ℝ)..2*Real.pi,f (x θ)) := by
      field_simp [show (Real.pi:ℂ) ≠ 0 by exact_mod_cast Real.pi_ne_zero]

/-- The bound is valid for complex f and complex unordered endpoints, including collapse. -/
theorem p2StdRoot_integral_norm_bound38 (a b c : ℂ) (r B : ℝ) (hr : 0 < r)
    (hcut : segment ℝ a b ⊆ ball c r) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (closedBall c r))
    (_hB : 0 ≤ B) (hfB : ∀ z ∈ segment ℝ a b, ‖f z‖ ≤ B) :
    CircleIntegrable (fun z : ℂ => f z/stdRoot38 ((a+b)/2) ((b-a)^2) z) c r ∧
    ‖circleIntegral (fun z : ℂ => f z/stdRoot38 ((a+b)/2) ((b-a)^2) z) c r‖ ≤
      2*Real.pi*B := by
  have ha := p2StdRoot_cosine_average38 a b c r hr hcut f hf
  refine ⟨ha.1,?_⟩
  rw [ha.2.2,norm_mul,norm_neg,Complex.norm_I,one_mul]
  have hn := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := 2*Real.pi)
    (f := fun θ => f ((a+b)/2+((b-a)/2)*(Real.cos θ:ℂ)))
    (fun θ _ => hfB _ (p2Cosine_mem_segment38 a b θ))
  simpa only [sub_zero,abs_of_pos (by positivity : 0 < 2*Real.pi),mul_comm B] using hn

#print axioms p2StdRoot_continuousOn_offcut38
#print axioms p2StdRoot_cosine_average38
#print axioms p2StdRoot_integral_norm_bound38
end
end NlsGge.GK38
