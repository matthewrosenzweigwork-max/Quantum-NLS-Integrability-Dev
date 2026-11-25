import NlsGge.GK38.AnglePeriodCosineCentering
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Actual cut Taylor and cosine cancellation estimates. The mean value
inequality is a NORM inequality on a convex complex segment, never a complex
single mean-value point. Integrabilities precede all integral identities. -/
set_option autoImplicit false
open Set Metric MeasureTheory
namespace NlsGge.GK38
noncomputable section

theorem angleWeighted_cut_cosine_deviation38
    (φ : PotPair) (hφ : φ ∈ gkW) (n m : ℤ) (s : Lib.L2Seq) (b : ℝ) (hb : 0 ≤ b)
    (hder : ∀ z ∈ segment ℝ (lamMinus φ m) (lamPlus φ m),
      DifferentiableAt ℂ (fun w => angleRegularFactor38 n m ((φ,s),w)) z ∧
      ‖(((n-m : ℤ) : ℂ))*deriv (fun w => angleRegularFactor38 n m ((φ,s),w)) z‖ ≤ b)
    (θ : ℝ) :
    ‖(((n-m : ℤ) : ℂ))*(
      angleRegularFactor38 n m ((φ,s),(lamMinus φ m+lamPlus φ m)/2+
        ((lamPlus φ m-lamMinus φ m)/2)*(Real.cos θ : ℂ))-
      angleRegularFactor38 n m ((φ,s),tauN φ m))‖ ≤
      b*‖(lamPlus φ m-lamMinus φ m)/2‖ := by
  let F : ℂ → ℂ := fun z => (((n-m : ℤ) : ℂ))*angleRegularFactor38 n m ((φ,s),z)
  have hF (z : ℂ) (hz : z ∈ segment ℝ (lamMinus φ m) (lamPlus φ m)) :
      HasDerivAt F ((((n-m : ℤ) : ℂ))*
        deriv (fun w => angleRegularFactor38 n m ((φ,s),w)) z) z :=
    (hder z hz).1.hasDerivAt.const_mul _
  have hτ : tauN φ m=(lamMinus φ m+lamPlus φ m)/2 := by
    rw [tauN_value38 φ hφ m]
    ring
  have ht : tauN φ m ∈ segment ℝ (lamMinus φ m) (lamPlus φ m) := by
    rw [hτ]
    simpa only [Real.cos_pi_div_two,Complex.ofReal_zero,mul_zero,add_zero] using
      p2Cosine_mem_segment38 (lamMinus φ m) (lamPlus φ m) (Real.pi/2)
  let x : ℂ := (lamMinus φ m+lamPlus φ m)/2+
    ((lamPlus φ m-lamMinus φ m)/2)*(Real.cos θ : ℂ)
  have hx : x ∈ segment ℝ (lamMinus φ m) (lamPlus φ m) :=
    p2Cosine_mem_segment38 (lamMinus φ m) (lamPlus φ m) θ
  have hbound := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z hz => (hF z hz).differentiableAt)
    (fun z hz => by rw [(hF z hz).deriv]; exact (hder z hz).2)
    (convex_segment (𝕜 := ℝ) (lamMinus φ m) (lamPlus φ m)) ht hx
  have hdist : ‖x-tauN φ m‖ ≤ ‖(lamPlus φ m-lamMinus φ m)/2‖ := by
    have he : x-tauN φ m=((lamPlus φ m-lamMinus φ m)/2)*(Real.cos θ : ℂ) := by
      rw [hτ]
      dsimp only [x]
      ring
    have hc : ‖(Real.cos θ : ℂ)‖ ≤ (1 : ℝ) := by
      simpa only [Complex.norm_real,Real.norm_eq_abs] using Real.abs_cos_le_one θ
    rw [he,norm_mul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hc (norm_nonneg _)
  have hh := hbound.trans (mul_le_mul_of_nonneg_left hdist hb)
  simpa only [F,mul_sub] using hh

theorem angleWeighted_actual_cosine_moment_bound38
    (φ : PotPair) (hφ : φ ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hfam : IsolatingFamily38 φ C R)
    (n m : ℤ) (hnm : n ≠ m) (s : Lib.L2Seq)
    (hσ : Lib.sigmaOf s n ∈ closedBall (C n) (R n))
    (b : ℝ) (hb : 0 ≤ b)
    (hder : ∀ z ∈ segment ℝ (lamMinus φ m) (lamPlus φ m),
      DifferentiableAt ℂ (fun w => angleRegularFactor38 n m ((φ,s),w)) z ∧
      ‖(((n-m : ℤ) : ℂ))*deriv (fun w => angleRegularFactor38 n m ((φ,s),w)) z‖ ≤ b) :
    let x : ℝ → ℂ := fun θ => (lamMinus φ m+lamPlus φ m)/2+
      ((lamPlus φ m-lamMinus φ m)/2)*(Real.cos θ : ℂ)
    IntervalIntegrable (fun θ : ℝ => (Real.cos θ : ℂ)*
      ((((n-m : ℤ) : ℂ))*angleRegularFactor38 n m ((φ,s),x θ))) volume 0 (2*Real.pi) ∧
    ‖∫ θ : ℝ in (0 : ℝ)..2*Real.pi, (Real.cos θ : ℂ)*
      ((((n-m : ℤ) : ℂ))*angleRegularFactor38 n m ((φ,s),x θ))‖ ≤
      (2*Real.pi)*b*‖(lamPlus φ m-lamMinus φ m)/2‖ := by
  let x : ℝ → ℂ := fun θ => (lamMinus φ m+lamPlus φ m)/2+
    ((lamPlus φ m-lamMinus φ m)/2)*(Real.cos θ : ℂ)
  let F : ℝ → ℂ := fun θ => (((n-m : ℤ) : ℂ))*angleRegularFactor38 n m ((φ,s),x θ)
  let c : ℂ := (((n-m : ℤ) : ℂ))*angleRegularFactor38 n m ((φ,s),tauN φ m)
  have ha := angleRegularFactor_own_disc_analytic38 φ hφ C R hfam n m hnm s hσ
  have hpath (θ : ℝ) : x θ ∈ closedBall (C m) (R m) := by
    have hfamily := hfam
    obtain ⟨_c,_N,_hg,hsp⟩ := hfamily
    exact ball_subset_closedBall ((hsp.1 m).1
      (p2Cosine_mem_segment38 (lamMinus φ m) (lamPlus φ m) θ))
  have hcont : Continuous F := by
    apply continuous_iff_continuousAt.mpr
    intro θ
    exact continuousAt_const.mul ((ha (x θ) (hpath θ)).continuousAt.comp
      (by fun_prop : ContinuousAt x θ))
  have hcos : Continuous (fun θ : ℝ => (Real.cos θ : ℂ)) :=
    Complex.continuous_ofReal.comp Real.continuous_cos
  have hi : IntervalIntegrable (fun θ : ℝ => (Real.cos θ : ℂ)*F θ)
      volume 0 (2*Real.pi) := (hcos.mul hcont).intervalIntegrable _ _
  have hc : IntervalIntegrable (fun θ : ℝ => (Real.cos θ : ℂ)*c)
      volume 0 (2*Real.pi) := (hcos.intervalIntegrable _ _).mul_const c
  have he (θ : ℝ) : (Real.cos θ : ℂ)*(F θ-c)=
      (Real.cos θ : ℂ)*F θ-(Real.cos θ : ℂ)*c := by ring
  have hzero : (∫ θ : ℝ in (0 : ℝ)..2*Real.pi, (Real.cos θ : ℂ))=0 := by
    rw [intervalIntegral.integral_ofReal]
    simp
  have hint : (∫ θ : ℝ in (0 : ℝ)..2*Real.pi, (Real.cos θ : ℂ)*F θ)=
      ∫ θ : ℝ in (0 : ℝ)..2*Real.pi, (Real.cos θ : ℂ)*(F θ-c) := by
    simp_rw [he]
    rw [intervalIntegral.integral_sub hi hc,intervalIntegral.integral_mul_const,
      hzero,zero_mul,sub_zero]
  have hbound : ∀ θ ∈ Set.uIoc (0 : ℝ) (2*Real.pi),
      ‖(Real.cos θ : ℂ)*(F θ-c)‖ ≤ b*‖(lamPlus φ m-lamMinus φ m)/2‖ := by
    intro θ _hθ
    have hd := angleWeighted_cut_cosine_deviation38 φ hφ n m s b hb hder θ
    have hd' : ‖F θ-c‖ ≤ b*‖(lamPlus φ m-lamMinus φ m)/2‖ := by
      simpa only [F,c,← mul_sub] using hd
    have hcosnorm : ‖(Real.cos θ : ℂ)‖ ≤ (1 : ℝ) := by
      simpa only [Complex.norm_real,Real.norm_eq_abs] using Real.abs_cos_le_one θ
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right hcosnorm (norm_nonneg _)).trans
      (by simpa only [one_mul] using hd')
  refine ⟨hi,?_⟩
  rw [hint]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  have hlen : |2*Real.pi-(0 : ℝ)|=2*Real.pi := by
    rw [sub_zero,abs_of_pos (by positivity)]
  rw [hlen] at hh
  exact hh.trans_eq (by ring)

end
end NlsGge.GK38
