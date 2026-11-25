import Armstrong.Work.RawEtaSameFamily
import NlsGge.GK38.AbelianStdRootAverage
import NlsGge.GK38.AngleRatioSpectralDerivativeAllCuts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Own-period normalization and zeta deviation

The project omitted ratio is the sign-normalized own-gap zeta factor: its
cosine average is exactly one when the own period is 2 pi. A uniform spectral
derivative bound then gives O(gap) deviation on the whole cut.
-/
set_option autoImplicit false
open Set Metric Filter Topology MeasureTheory
namespace NlsGge.GK38
noncomputable section

theorem gk16_own_ratio_cosine_average38
    (phi : PotPair) (hphi : phi ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hfam : IsolatingFamily38 phi C R)
    (n : ℤ) (s : Lib.L2Seq)
    (hperiod : abelianPeriod38 n phi (p2FullNumerator38 n s) =
      2 * (Real.pi : ℂ)) :
    let x : ℝ → ℂ := fun theta =>
      (lamMinus phi n + lamPlus phi n)/2 +
        ((lamPlus phi n-lamMinus phi n)/2)*(Real.cos theta : ℂ)
    IntervalIntegrable
      (fun theta : ℝ => p2OmittedRatio38 n ((phi,s),x theta))
      volume 0 (2*Real.pi) ∧
    (∫ theta : ℝ in (0:ℝ)..2*Real.pi,
      p2OmittedRatio38 n ((phi,s),x theta)) =
        2 * (Real.pi : ℂ) := by
  let x : ℝ → ℂ := fun theta =>
    (lamMinus phi n + lamPlus phi n)/2 +
      ((lamPlus phi n-lamMinus phi n)/2)*(Real.cos theta : ℂ)
  let f : ℂ → ℂ := fun z => p2OmittedRatio38 n ((phi,s),z)
  let S : ℂ → ℂ :=
    stdRoot38 ((lamMinus phi n+lamPlus phi n)/2)
      ((lamPlus phi n-lamMinus phi n)^2)
  have hr : 0 < R n := isolating_radius_pos38 hfam n
  have hcut : segment ℝ (lamMinus phi n) (lamPlus phi n) ⊆
      ball (C n) (R n) := by
    obtain ⟨c,N,hgeom,hspec⟩ := hfam
    exact (hspec.1 n).1
  have hf : AnalyticOnNhd ℂ f (closedBall (C n) (R n)) :=
    gk16_own_ratio_analytic38 n phi hphi C R hfam s
  have havg := p2StdRoot_cosine_average38
    (lamMinus phi n) (lamPlus phi n) (C n) (R n)
    hr hcut f hf
  have htau : tauN phi n =
      (lamMinus phi n+lamPlus phi n)/2 := by
    rw [tauN_value38 phi hphi n]
    ring
  have hgamma := gamma2_value38 phi hphi n
  have hEq : EqOn
      (fun z => p2FullNumerator38 n s z / canonRoot38 phi z)
      (fun z => Complex.I * f z / S z)
      (sphere (C n) (R n)) := by
    intro z hz
    have hroot : (phi,z) ∈ rootDomain38 := by
      obtain ⟨c,N,hgeom,hspec⟩ := hfam
      exact ⟨hphi, fixed_sphere_subset phi C R
        ⟨c,N,hgeom,hspec⟩ n hz⟩
    change p2FullNumerator38 n s z / canonRoot38 phi z =
      Complex.I * f z / S z
    rw [gk16_own_factorization38 n s phi z hroot, htau, hgamma]
  have hfamily := abelianPeriod_fullfamily_realization38
    phi hphi (discC phi) C (discR phi) R
    (isolating_family38 phi hphi) hfam n
    (p2FullNumerator38 n s) (p2FullNumerator_entire38 n s)
  refine ⟨havg.2.1, ?_⟩
  have hcircle :
      circleIntegral (fun z => p2FullNumerator38 n s z /
          canonRoot38 phi z) (C n) (R n) =
        circleIntegral (fun z => Complex.I * (f z / S z))
          (C n) (R n) :=
    circleIntegral.integral_congr hr.le
      (fun z hz => by simpa only [mul_div_assoc] using hEq hz)
  have hperiodC :
      circleIntegral (fun z => p2FullNumerator38 n s z /
          canonRoot38 phi z) (C n) (R n) =
        2 * (Real.pi : ℂ) := by
    unfold abelianPeriod38 at hperiod
    exact hfamily.2.2 ▸ hperiod
  have hmul :
      circleIntegral (fun z => Complex.I * (f z / S z))
          (C n) (R n) =
        Complex.I * circleIntegral (fun z => f z / S z)
          (C n) (R n) := by
    exact circleIntegral.integral_const_mul _ _ _ _
  rw [hcircle, hmul, havg.2.2] at hperiodC
  dsimp only [f, x] at *
  have hscalar : Complex.I * (-Complex.I) = (1 : ℂ) := by
    rw [mul_neg, Complex.I_mul_I]
    ring
  rw [← mul_assoc, hscalar, one_mul] at hperiodC
  exact hperiodC

/-- Abstract cosine-average estimate used for GK Lemma 16.3. Keeping the
spectral objects out of this proof prevents large elaboration terms. -/
theorem gk16_cosine_average_deriv_bound38
    (a b : ℂ) (f : ℂ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (havgInt : IntervalIntegrable
      (fun theta : ℝ => f ((a+b)/2 + ((b-a)/2)*(Real.cos theta : ℂ)))
      volume 0 (2*Real.pi))
    (havg : (∫ theta : ℝ in (0:ℝ)..2*Real.pi,
      f ((a+b)/2 + ((b-a)/2)*(Real.cos theta : ℂ))) =
        2 * (Real.pi : ℂ))
    (hder : ∀ z ∈ segment ℝ a b,
      DifferentiableAt ℂ f z ∧ ‖deriv f z‖ ≤ B) :
    ∀ z ∈ segment ℝ a b, ‖f z - 1‖ ≤ 2 * B * ‖b-a‖ := by
  let x : ℝ → ℂ := fun theta =>
    (a+b)/2 + ((b-a)/2)*(Real.cos theta : ℂ)
  have hfdiff : ∀ w ∈ segment ℝ a b, DifferentiableAt ℂ f w :=
    fun w hw => (hder w hw).1
  have hfder : ∀ w ∈ segment ℝ a b, ‖deriv f w‖ ≤ B :=
    fun w hw => (hder w hw).2
  intro z hz
  have hpoint (theta : ℝ) : ‖f z - f (x theta)‖ ≤ 2 * B * ‖b-a‖ := by
    have hx : x theta ∈ segment ℝ a b := p2Cosine_mem_segment38 _ _ theta
    have hmv := Convex.norm_image_sub_le_of_norm_deriv_le
      hfdiff hfder (convex_segment (𝕜 := ℝ) a b) hz hx
    have hzdist : ‖z-a‖ ≤ ‖b-a‖ := norm_sub_le_of_mem_segment hz
    have hxdist : ‖x theta-a‖ ≤ ‖b-a‖ := norm_sub_le_of_mem_segment hx
    have htri := norm_sub_le (x theta-a) (z-a)
    have he : (x theta-a)-(z-a)=x theta-z := by ring
    rw [he] at htri
    have hdist : ‖x theta-z‖ ≤ 2*‖b-a‖ := by linarith
    have hmv' : ‖f z-f (x theta)‖ ≤ B*‖x theta-z‖ := by
      simpa only [norm_sub_rev] using hmv
    calc
      _ ≤ B*‖x theta-z‖ := hmv'
      _ ≤ B*(2*‖b-a‖) := mul_le_mul_of_nonneg_left hdist hB
      _ = 2*B*‖b-a‖ := by ring
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := 2*Real.pi)
    (f := fun theta : ℝ => f z - f (x theta))
    (fun theta _ => hpoint theta)
  have hidentity :
      ∫ theta : ℝ in (0:ℝ)..2*Real.pi, (f z-f (x theta)) =
        (2*(Real.pi:ℂ))*(f z-1) := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const havgInt,
      intervalIntegral.integral_const, havg]
    simp only [sub_zero, Complex.real_smul]
    push_cast
    ring
  rw [hidentity,norm_mul] at hint
  have hpinorm : ‖(2*(Real.pi:ℂ))‖=2*Real.pi := by
    rw [norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hpinorm] at hint
  have habs : |2*Real.pi-0|=2*Real.pi := by
    rw [sub_zero, abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
  rw [habs] at hint
  have hp : 0 < 2*Real.pi := by positivity
  nlinarith

/-- Quantitative version of GK Lemma 16.3 from period normalization plus a
spectral derivative bound. -/
theorem gk16_own_ratio_cut_error_of_deriv38
    (phi : PotPair) (hphi : phi ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hfam : IsolatingFamily38 phi C R)
    (n : ℤ) (s : Lib.L2Seq) (B : ℝ) (hB : 0 ≤ B)
    (hperiod : abelianPeriod38 n phi (p2FullNumerator38 n s) =
      2 * (Real.pi : ℂ))
    (hder : ∀ z ∈ segment ℝ (lamMinus phi n) (lamPlus phi n),
      DifferentiableAt ℂ (fun w => p2OmittedRatio38 n ((phi,s),w)) z ∧
      ‖deriv (fun w => p2OmittedRatio38 n ((phi,s),w)) z‖ ≤ B) :
    ∀ z ∈ segment ℝ (lamMinus phi n) (lamPlus phi n),
      ‖p2OmittedRatio38 n ((phi,s),z)-1‖ ≤
        2*B*‖lamPlus phi n-lamMinus phi n‖ := by
  have havg := gk16_own_ratio_cosine_average38
    phi hphi C R hfam n s hperiod
  exact gk16_cosine_average_deriv_bound38
    (lamMinus phi n) (lamPlus phi n)
    (fun w => p2OmittedRatio38 n ((phi,s),w)) B hB havg.1 havg.2 hder

end
end NlsGge.GK38
