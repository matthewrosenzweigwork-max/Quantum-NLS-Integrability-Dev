import Armstrong.Work.CartesianContinuationSpec
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Literal fixed-circle bound for the own correction coefficient

The two compact integrals are the existing rawBetaStdCauchyCoefficient38,
with the actual positive omitted quotient minus one and the actual Dirichlet
terminal. Numerical data concern the same full circle, not merely the own cut.
The actual spectral family supplies continuity and genuine compact integrability.
Common numerical inputs still need their common-neighborhood producers; this
file does not claim a locally uniform exponent bound or Cartesian closure.

Prospective source: no compiler was run by the author. Root owns the sole queue.
-/
set_option autoImplicit false
open Set Metric MeasureTheory
open scoped Topology
namespace NlsGge.GK38
noncomputable section

/-- Continuity of the actual circle integrand, with its genuine standard-root
branch. The full own cut is inside the certified circle, including at collapse. -/
private theorem gk16_correction_circle_data38
    (phi : PotPair) (hphi : phi ∈ gkW) (n : ℤ) (s : Lib.L2Seq)
    (C : ℤ → ℂ) (rho : ℤ → ℝ) (hfamily : IsolatingFamily38 phi C rho) :
    let gamma : ℝ → ℂ := circleMap (C n) (rho n)
    let S : ℝ → ℂ := fun t => stdRoot38 ((lamMinus phi n+lamPlus phi n)/2)
      ((lamPlus phi n-lamMinus phi n)^2) (gamma t)
    let f : ℝ → ℂ := fun t => deriv gamma t *
      ((p2OmittedRatio38 n ((phi,s),gamma t)-1)/S t)
    Continuous S ∧ (∀ t : ℝ, S t ≠ 0) ∧ Continuous f := by
  let gamma : ℝ → ℂ := circleMap (C n) (rho n)
  let S : ℝ → ℂ := fun t => stdRoot38 ((lamMinus phi n+lamPlus phi n)/2)
    ((lamPlus phi n-lamMinus phi n)^2) (gamma t)
  have hr : 0 < rho n := isolating_radius_pos38 hfamily n
  have hcut : segment ℝ (lamMinus phi n) (lamPlus phi n) ⊆
      ball (C n) (rho n) := by
    obtain ⟨c,N,hgeom,hspec⟩ := hfamily
    exact (hspec.1 n).1
  have hgc : Continuous gamma := continuous_circleMap (C n) (rho n)
  have hgdc : Continuous (deriv gamma) := by
    change Continuous (deriv (circleMap (C n) (rho n)))
    rw [funext (deriv_circleMap (C n) (rho n))]
    exact (continuous_circleMap 0 (rho n)).mul_const Complex.I
  have hoff : ∀ t : ℝ, gamma t ∉ segment ℝ (lamMinus phi n) (lamPlus phi n) := by
    intro t ht
    have hs := circleMap_mem_sphere (C n) hr.le t
    exact (not_lt.mpr (mem_sphere.mp hs).ge) (mem_ball.mp (hcut ht))
  have hSn : ∀ t : ℝ, S t ≠ 0 :=
    fun t => stdRoot_ne_zero38 (lamMinus phi n) (lamPlus phi n) (gamma t) (hoff t)
  have hSd : Differentiable ℝ S := by
    intro t
    have hs := stdRoot_slit38 (lamMinus phi n) (lamPlus phi n) (gamma t) (hoff t)
    have ha : AnalyticAt ℂ
        (stdRoot38 ((lamMinus phi n+lamPlus phi n)/2)
          ((lamPlus phi n-lamMinus phi n)^2)) (gamma t) :=
      stdRoot_analyticAt38 analyticAt_const analyticAt_const analyticAt_id hs.1 hs.2
    exact (ha.differentiableAt.hasDerivAt.comp t
      (differentiable_circleMap (C n) (rho n) t).hasDerivAt).differentiableAt
  have hSc : Continuous S := hSd.continuous
  have hq := (gk16_own_ratio_analytic38 n phi hphi C rho hfamily s).sub
    (analyticOnNhd_const (v := (1 : ℂ)))
  have hqc : Continuous (fun t => p2OmittedRatio38 n ((phi,s),gamma t)-1) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hq (gamma t) (sphere_subset_closedBall
      (circleMap_mem_sphere (C n) hr.le t))).continuousAt.comp hgc.continuousAt
  exact ⟨hSc,hSn,hgdc.mul (hqc.div hSc hSn)⟩

/-- The actual inner primitive is genuinely integrable and bounded on its
entire parameter interval by the supplied common-circle numerical data. -/
theorem gk16_own_correction_inner_bound38
    (H rmax s0 : ℝ) (hH : 0 ≤ H) (hs0 : 0 < s0)
    (phi : PotPair) (hphi : phi ∈ gkW) (n : ℤ) (s : Lib.L2Seq)
    (C : ℤ → ℂ) (rho : ℤ → ℝ)
    (hfamily : IsolatingFamily38 phi C rho) (hrmax : rho n ≤ rmax)
    (hq : ∀ theta ∈ Icc (0 : ℝ) (2*Real.pi),
      ‖p2OmittedRatio38 n ((phi,s),circleMap (C n) (rho n) theta)‖ ≤ H)
    (hroot : ∀ theta ∈ Icc (0 : ℝ) (2*Real.pi),
      s0 ≤ ‖stdRoot38 ((lamMinus phi n+lamPlus phi n)/2)
        ((lamPlus phi n-lamMinus phi n)^2) (circleMap (C n) (rho n) theta)‖)
    (theta : ℝ) (htheta : theta ∈ Icc (0 : ℝ) (2*Real.pi)) :
    let f : ℝ → ℂ := fun t => deriv (circleMap (C n) (rho n)) t *
      ((p2OmittedRatio38 n ((phi,s),circleMap (C n) (rho n) t)-1) /
        stdRoot38 ((lamMinus phi n+lamPlus phi n)/2)
          ((lamPlus phi n-lamMinus phi n)^2) (circleMap (C n) (rho n) t))
    IntervalIntegrable f volume (0 : ℝ) theta ∧
      ‖∫ t in (0 : ℝ)..theta, f t‖ ≤ 2*Real.pi*rmax*(H+1)/s0 := by
  let gamma : ℝ → ℂ := circleMap (C n) (rho n)
  let S : ℝ → ℂ := fun t => stdRoot38 ((lamMinus phi n+lamPlus phi n)/2)
    ((lamPlus phi n-lamMinus phi n)^2) (gamma t)
  let f : ℝ → ℂ := fun t => deriv gamma t *
    ((p2OmittedRatio38 n ((phi,s),gamma t)-1)/S t)
  let A : ℝ := rmax*(H+1)/s0
  have hr : 0 < rho n := isolating_radius_pos38 hfamily n
  have hrmax0 : 0 ≤ rmax := hr.le.trans hrmax
  have hA : 0 ≤ A := div_nonneg (mul_nonneg hrmax0 (by linarith)) hs0.le
  have hfc : Continuous f := (gk16_correction_circle_data38 phi hphi n s C rho hfamily).2.2
  have hfi : IntervalIntegrable f volume (0 : ℝ) theta := hfc.intervalIntegrable _ _
  have hpoint : ∀ t ∈ Icc (0 : ℝ) (2*Real.pi), ‖f t‖ ≤ A := by
    intro t ht
    have hqm : ‖p2OmittedRatio38 n ((phi,s),gamma t)-1‖ ≤ H+1 := by
      calc
        _ ≤ ‖p2OmittedRatio38 n ((phi,s),gamma t)‖+‖(1 : ℂ)‖ := norm_sub_le _ _
        _ ≤ H+1 := by
          rw [norm_one]
          change ‖p2OmittedRatio38 n ((phi,s),circleMap (C n) (rho n) t)‖+1 ≤ H+1
          linarith only [hq t ht]
    have hgd : ‖deriv gamma t‖ = rho n := by
      simp only [gamma,deriv_circleMap,norm_mul,norm_circleMap_zero,Complex.norm_I,
        mul_one,abs_of_pos hr]
    change ‖deriv gamma t * ((p2OmittedRatio38 n ((phi,s),gamma t)-1)/S t)‖ ≤ A
    rw [norm_mul,norm_div,hgd,← mul_div_assoc]
    exact div_le_div₀ (mul_nonneg hrmax0 (by linarith))
      (mul_le_mul hrmax hqm (norm_nonneg _) hrmax0) hs0 (hroot t ht)
  refine ⟨hfi,?_⟩
  calc
    ‖∫ t in (0 : ℝ)..theta, f t‖ ≤ ∫ t in (0 : ℝ)..theta, ‖f t‖ :=
      intervalIntegral.norm_integral_le_integral_norm htheta.1
    _ ≤ ∫ _t in (0 : ℝ)..theta, A :=
      intervalIntegral.integral_mono_on htheta.1 hfi.norm intervalIntegrable_const
        (fun t ht => hpoint t ⟨ht.1,ht.2.trans htheta.2⟩)
    _ = theta*A := by simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul]
    _ ≤ (2*Real.pi)*A := mul_le_mul_of_nonneg_right htheta.2 hA
    _ = 2*Real.pi*rmax*(H+1)/s0 := by dsimp [A]; ring

/-- Norm bound for the literal nested Cauchy coefficient at the actual
Dirichlet point. Both root denominators and the circle-to-mu distance are
controlled on the same fixed circle; no own-cut-to-offcut inference is used. -/
theorem gk16_own_correction_cauchy_bound38
    (H rmax s0 d0 : ℝ) (hH : 0 ≤ H) (hs0 : 0 < s0) (hd0 : 0 < d0)
    (phi : PotPair) (hphi : phi ∈ gkW) (n : ℤ) (s : Lib.L2Seq)
    (C : ℤ → ℂ) (rho : ℤ → ℝ)
    (hfamily : IsolatingFamily38 phi C rho) (hrmax : rho n ≤ rmax)
    (hq : ∀ theta ∈ Icc (0 : ℝ) (2*Real.pi),
      ‖p2OmittedRatio38 n ((phi,s),circleMap (C n) (rho n) theta)‖ ≤ H)
    (hroot : ∀ theta ∈ Icc (0 : ℝ) (2*Real.pi),
      s0 ≤ ‖stdRoot38 ((lamMinus phi n+lamPlus phi n)/2)
        ((lamPlus phi n-lamMinus phi n)^2) (circleMap (C n) (rho n) theta)‖)
    (hdistance : ∀ theta ∈ Icc (0 : ℝ) (2*Real.pi),
      d0 ≤ ‖circleMap (C n) (rho n) theta-muSeq phi n‖) :
    ‖gk16OwnCorrectionCoefficient38 phi n s (C n) (rho n) (muSeq phi n)‖ ≤
      2*Real.pi*rmax^2*(H+1)/(s0^2*d0) := by
  let gamma : ℝ → ℂ := circleMap (C n) (rho n)
  let S : ℝ → ℂ := fun t => stdRoot38 ((lamMinus phi n+lamPlus phi n)/2)
    ((lamPlus phi n-lamMinus phi n)^2) (gamma t)
  let f : ℝ → ℂ := fun t => deriv gamma t *
    ((p2OmittedRatio38 n ((phi,s),gamma t)-1)/S t)
  let U : ℝ → ℂ := fun theta => ∫ t in (0 : ℝ)..theta, f t
  let J : ℝ → ℂ := fun theta =>
    (U theta/S theta)*deriv gamma theta/(gamma theta-muSeq phi n)
  let M : ℝ := 2*Real.pi*rmax*(H+1)/s0
  let A : ℝ := (M/s0)*rmax/d0
  have hr : 0 < rho n := isolating_radius_pos38 hfamily n
  have hrmax0 : 0 ≤ rmax := hr.le.trans hrmax
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hMs0 : 0 ≤ M/s0 := div_nonneg hM hs0.le
  have hA : 0 ≤ A := div_nonneg (mul_nonneg hMs0 hrmax0) hd0.le
  have hdata := gk16_correction_circle_data38 phi hphi n s C rho hfamily
  have hSc : Continuous S := hdata.1
  have hSn : ∀ t : ℝ, S t ≠ 0 := hdata.2.1
  have hfc : Continuous f := hdata.2.2
  have hUc : Continuous U :=
    (show Differentiable ℝ U from fun theta =>
      (hfc.integral_hasStrictDerivAt 0 theta).hasDerivAt.differentiableAt).continuous
  have hgdc : Continuous (deriv gamma) := by
    change Continuous (deriv (circleMap (C n) (rho n)))
    rw [funext (deriv_circleMap (C n) (rho n))]
    exact (continuous_circleMap 0 (rho n)).mul_const Complex.I
  have hmu : muSeq phi n ∈ ball (C n) (rho n) := by
    obtain ⟨c,N,hgeom,hspec⟩ := hfamily
    exact (hspec.1 n).2.1
  have hden : ∀ theta : ℝ, gamma theta-muSeq phi n ≠ 0 :=
    fun theta => sub_ne_zero.mpr (circleMap_ne_mem_ball hmu theta)
  have hJc : Continuous J :=
    ((hUc.div hSc hSn).mul hgdc).div
      ((continuous_circleMap (C n) (rho n)).sub continuous_const) hden
  have hJi : IntervalIntegrable J volume (0 : ℝ) (2*Real.pi) :=
    hJc.intervalIntegrable _ _
  have hpoint : ∀ theta ∈ Icc (0 : ℝ) (2*Real.pi), ‖J theta‖ ≤ A := by
    intro theta htheta
    have hU : ‖U theta‖ ≤ M :=
      (gk16_own_correction_inner_bound38 H rmax s0 hH hs0 phi hphi n s
        C rho hfamily hrmax hq hroot theta htheta).2
    have hB : ‖U theta/S theta‖ ≤ M/s0 := by
      rw [norm_div]
      exact div_le_div₀ hM hU hs0 (hroot theta htheta)
    have hgd : ‖deriv gamma theta‖ = rho n := by
      simp only [gamma,deriv_circleMap,norm_mul,norm_circleMap_zero,Complex.norm_I,
        mul_one,abs_of_pos hr]
    change ‖(U theta/S theta)*deriv gamma theta/(gamma theta-muSeq phi n)‖ ≤ A
    rw [norm_div,norm_mul,hgd]
    exact div_le_div₀ (mul_nonneg hMs0 hrmax0)
      (mul_le_mul hB hrmax hr.le hMs0) hd0 (hdistance theta htheta)
  have hJbound : ‖∫ theta in (0 : ℝ)..2*Real.pi, J theta‖ ≤ (2*Real.pi)*A := by
    calc
      _ ≤ ∫ theta in (0 : ℝ)..2*Real.pi, ‖J theta‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by positivity)
      _ ≤ ∫ _theta in (0 : ℝ)..2*Real.pi, A :=
        intervalIntegral.integral_mono_on (by positivity) hJi.norm intervalIntegrable_const hpoint
      _ = (2*Real.pi)*A := by
        simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul]
  have hnormalizer : ‖(2*(Real.pi : ℂ)*Complex.I)⁻¹‖ = (2*Real.pi)⁻¹ := by
    simp only [norm_inv,norm_mul,Complex.norm_ofNat,Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le,Complex.norm_I,mul_one]
  change ‖(2*(Real.pi : ℂ)*Complex.I)⁻¹ *
    (∫ theta in (0 : ℝ)..2*Real.pi, J theta)‖ ≤ _
  rw [norm_mul,hnormalizer]
  calc
    _ ≤ (2*Real.pi)⁻¹*((2*Real.pi)*A) :=
      mul_le_mul_of_nonneg_left hJbound (by positivity)
    _ = 2*Real.pi*rmax^2*(H+1)/(s0^2*d0) := by
      dsimp [A,M]
      field_simp [ne_of_gt hs0,ne_of_gt hd0,Real.pi_ne_zero]

end
end NlsGge.GK38
