import NlsGge.GK38.Lib.AnalyticL2MajorantCauchy
import NlsGge.GK38.Lib.HilbertValuedAnalytic
import NlsGge.GK38.Lib.InterpolationHilbertOp

/-!
# Summable coordinate-square majorants on smaller analytic discs

E01 L4c part 2c, the generic `hQline` input to P1 (campaign plan §6.1).
Choose an intermediate circle. Cauchy's formula on the squared coordinates gives
an integral majorant. Finite sums of these boundary integrals are bounded by the
integral of the squared `ℓ²` norm; bounded nonnegative finite sums give summability.
This argument uses neither an infinite sum–integral interchange nor uniform
coordinate tails as an additional hypothesis.
-/

set_option autoImplicit false

open Metric Set MeasureTheory
open scoped Real

namespace NlsGge.GK38.Lib

noncomputable section

/-- An analytic `ℓ²(ℤ, ℂ)`-valued map on a disc has a summable coordinate-square
majorant on every smaller positive disc. -/
theorem summable_sup_sq_of_analytic (a : ℂ → L2Z) (ρ : ℝ)
    (ha : AnalyticOnNhd ℂ a (Metric.ball 0 ρ)) {ρ' : ℝ}
    (h : 0 < ρ' ∧ ρ' < ρ) :
    ∃ q : ℤ → ℝ, Summable q ∧ ∀ ζ ∈ Metric.ball 0 ρ', ∀ m, ‖a ζ m‖ ^ 2 ≤ q m := by
  let R : ℝ := (ρ + ρ') / 2
  have hR : 0 < R := by dsimp [R]; linarith [h.1, h.2]
  have hrR : ρ' < R := by dsimp [R]; linarith [h.2]
  have hRρ : R < ρ := by dsimp [R]; linarith [h.2]
  have hsub : closedBall (0 : ℂ) R ⊆ ball 0 ρ := by
    intro z hz
    exact mem_ball.mpr ((mem_closedBall.mp hz).trans_lt hRρ)
  have hac : Continuous (fun t : ℝ => a (circleMap 0 R t)) :=
    ha.continuousOn.comp_continuous (continuous_circleMap 0 R)
      (fun t => hsub (circleMap_mem_closedBall 0 hR.le t))
  have hcoord (m : ℤ) : Continuous (fun t : ℝ => a (circleMap 0 R t) m) :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 m).continuous.comp hac
  have hi (m : ℤ) : IntervalIntegrable
      (fun t : ℝ => ‖a (circleMap 0 R t) m‖ ^ 2) volume 0 (2 * Real.pi) :=
    ((hcoord m).norm.pow 2).intervalIntegrable _ _
  have hia : IntervalIntegrable
      (fun t : ℝ => ‖a (circleMap 0 R t)‖ ^ 2) volume 0 (2 * Real.pi) :=
    (hac.norm.pow 2).intervalIntegrable _ _
  let C : ℝ := sqCauchyCoeff R ρ'
  have hC : 0 ≤ C := sqCauchyCoeff_nonneg hR.le hrR
  let q : ℤ → ℝ := fun m => C * ∫ t : ℝ in 0..2 * Real.pi,
    ‖a (circleMap 0 R t) m‖ ^ 2
  have hq0 (m : ℤ) : 0 ≤ q m := mul_nonneg hC
    (intervalIntegral.integral_nonneg Real.two_pi_pos.le (fun _ _ => sq_nonneg _))
  have hq : Summable q := by
    refine summable_of_sum_le hq0 (c := C * ∫ t : ℝ in 0..2 * Real.pi,
      ‖a (circleMap 0 R t)‖ ^ 2) (fun S => ?_)
    change ∑ m ∈ S, C * (∫ t : ℝ in 0..2 * Real.pi,
      ‖a (circleMap 0 R t) m‖ ^ 2) ≤ _
    rw [← Finset.mul_sum, ← intervalIntegral.integral_finsetSum (fun m _ => hi m)]
    refine mul_le_mul_of_nonneg_left ?_ hC
    exact intervalIntegral.integral_mono_on Real.two_pi_pos.le
      (by simpa only [Finset.sum_fn] using
        IntervalIntegrable.sum S (fun m _ => hi m)) hia
      (fun t _ => sum_sq_le_norm_sq (a (circleMap 0 R t)) S)
  refine ⟨q, hq, fun z hz m => ?_⟩
  have hz' : ‖z‖ < ρ' := by simpa using hz
  exact norm_sq_le_sqCauchyCoeff_integral (fun w => a w m) hR hrR
    ((analyticOnNhd_coord_of_analyticOnNhd ha m).mono hsub) hz'

end

end NlsGge.GK38.Lib
