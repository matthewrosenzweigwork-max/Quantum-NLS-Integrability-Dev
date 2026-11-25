import QuantumNLS.LOCAL017HaarPath
import QuantumNLS.GP05ScalarAverageR14
import QuantumNLS.GP05ConsumerBoundsR14

/-! Scalar holomorphic averaging for the actual LOCAL-017 path measure.
The complexification datum is explicit: the holomorphic covector extends beta,
and its rotations and velocity extend the literal operators.  No analyticity
or derivative bound of the averaged function is a premise. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Set Metric Filter Topology MeasureTheory
namespace QuantumNLS.LOCAL017Haar
open Ext025B7LocalPath GP05CauchyMajorantsR14 GP05ScalarAverageR14
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Original common holomorphic extension data on the complexification of the
real Hilbert space.  The bridge is the accepted GP-05 named bridge. -/
structure ComplexData (β : H → Cov) (R C : ℝ) where
  embed : H →L[ℝ] E
  embed_norm : ∀ z, ‖embed z‖ = ‖z‖
  beta : E → E →L[ℂ] ℂ
  rot : PathParameter → E →L[ℂ] E
  vel : PathParameter → E →L[ℂ] E
  rot_bound : ∀ p z, ‖rot p z‖ ≤ ‖z‖
  vel_bound : ∀ p z, ‖vel p z‖ ≤ Real.pi * ‖z‖
  rot_real : ∀ p z, rot p (embed z) = embed (rotation p z)
  vel_real : ∀ p z, vel p (embed z) = embed (velocity p.1 z)
  beta_real : ∀ z ∈ ball (0 : H) R, ∀ h, beta (embed z) (embed h) = (β z h : ℂ)
  holomorphic : DifferentiableOn ℂ beta (ball 0 R)
  cubic : ∀ z ∈ ball (0 : E) R, ‖beta z‖ ≤ C * ‖z‖^3
  measurable : ∀ z ∈ ball (0 : E) R,
    Measurable (fun p => correctingIntegrand beta rot vel p z)
  bridge : BanachHolomorphicBridge E (E →L[ℂ] ℂ)

def complexPrimitive {β : H → Cov} {R C : ℝ} (D : ComplexData (E := E) β R C)
    (z : E) : ℂ := ∫ p, correctingIntegrand D.beta D.rot D.vel p z ∂pathMeasure

variable {β : H → Cov} {R C : ℝ} (D : ComplexData (E := E) β R C)

theorem complex_bound (hC : 0 ≤ C) {z : E} (hz : z ∈ ball 0 R) :
    ‖complexPrimitive D z‖ ≤ C * Real.pi * ‖z‖^4 := by
  have hb : ∀ p, ‖correctingIntegrand D.beta D.rot D.vel p z‖ ≤ C * Real.pi * ‖z‖^4 := by
    intro p
    have hm : D.rot p z ∈ ball (0 : E) R :=
      mem_ball_zero_iff.mpr ((D.rot_bound p z).trans_lt (mem_ball_zero_iff.mp hz))
    simp only [correctingIntegrand, norm_neg]
    calc
      _ ≤ ‖D.beta (D.rot p z)‖ * ‖D.vel p (D.rot p z)‖ := (D.beta _).le_opNorm _
      _ ≤ (C * ‖z‖^3) * (Real.pi * ‖z‖) := by
        apply mul_le_mul _ ((D.vel_bound _ _).trans (by gcongr; exact D.rot_bound _ _))
          (norm_nonneg _) _
        · exact (D.cubic _ hm).trans (by
            gcongr
            exact D.rot_bound _ _)
        · exact (norm_nonneg _).trans ((D.cubic _ hm).trans (by
            gcongr
            exact D.rot_bound _ _))
      _ = _ := by ring
  simpa only [complexPrimitive, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (μ := pathMeasure) (Eventually.of_forall hb)

/-- GP-05 is applied on a ball about each point, so the average is analytic
on the whole original open ball rather than only at the origin. -/
theorem complex_analytic (hR : 0 < R) (hC : 0 ≤ C) :
    AnalyticOnNhd ℂ (complexPrimitive D) (ball 0 R) := by
  intro z hz
  let r := (R - ‖z‖) / 2
  have hr : 0 < r := by dsimp [r]; linarith [mem_ball_zero_iff.mp hz]
  have hs : ball z r ⊆ ball (0 : E) R := by
    intro y hy
    rw [mem_ball_zero_iff]
    have htri : ‖y‖ ≤ dist y z + ‖z‖ := by
      simpa only [dist_zero_right] using dist_triangle y z 0
    have hyd : dist y z < r := hy
    dsimp [r] at hyd
    linarith [mem_ball_zero_iff.mp hz]
  have ha := correctingIntegrand_analytic D.bridge D.beta D.rot D.vel D.rot_bound D.holomorphic
  obtain ⟨p, _, _, _, hp⟩ := scalar_average_of_analytic pathMeasure
    (correctingIntegrand D.beta D.rot D.vel) z hr (show 0 ≤ C * Real.pi * R^4 by positivity)
    (fun p => (ha p).mono hs) (fun y hy => D.measurable y (hs hy)) (fun p y hy => by
      have hyR := hs hy
      have hh := correctingIntegrand_bound D.beta D.rot D.vel hR hC Real.pi_pos.le
        D.rot_bound D.vel_bound D.cubic p y hyR
      exact hh)
  exact hp z (mem_ball_self (commonRadius_pos hr))

/-- Bind the complex average to the literal real Haar primitive, including
its sign; this is not a supplied identity for the average. -/
theorem complex_real {z : H} (hz : z ∈ ball 0 R) :
    complexPrimitive D (D.embed z) = (primitive β z : ℂ) := by
  unfold complexPrimitive primitive
  have he : (fun p => correctingIntegrand D.beta D.rot D.vel p (D.embed z)) =
      fun p => ((-(pathIntegrand β z p) : ℝ) : ℂ) := by
    funext p
    rw [correctingIntegrand, D.rot_real, D.vel_real, D.beta_real _ (rotation_mem hz p)]
    simp only [pathIntegrand, Complex.ofReal_neg]
  rw [he, integral_complex_ofReal, integral_neg]

include D

/-- Real analyticity is derived on the physical real slice. -/
theorem primitive_analytic (hR : 0 < R) (hC : 0 ≤ C) :
    AnalyticOnNhd ℝ (primitive β) (ball 0 R) := by
  intro z hz
  have hzE : D.embed z ∈ ball (0 : E) R := by
    simpa only [mem_ball_zero_iff, D.embed_norm] using hz
  have hcomp : AnalyticAt ℝ (fun w : H => complexPrimitive D (D.embed w)) z :=
    (((complex_analytic D hR hC) _ hzE).restrictScalars (𝕜 := ℝ)).comp (D.embed.analyticAt z)
  have ha := (Complex.reCLM.analyticAt _).comp hcomp
  apply ha.congr
  filter_upwards [isOpen_ball.mem_nhds hz] with y hy
  change (complexPrimitive D (D.embed y)).re = primitive β y
  rw [complex_real D hy, Complex.ofReal_re]

end QuantumNLS.LOCAL017Haar
