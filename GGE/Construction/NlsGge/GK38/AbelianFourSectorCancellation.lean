import NlsGge.GK38.AbelianRotatedSectorScalarBoundary
import Mathlib.Tactic.LinearCombination

/-! SOURCE ONLY: actual connector-function equality BEFORE derivatives and
finite additive cancellation AFTER all genuine arc/connector scalar CIs.
No assumed connector integral identity or final contour identity.
Exact targets+English preceded proof; UNCOMPILED, outside next4 native. -/
set_option autoImplicit false
open Set MeasureTheory
open scoped Interval
namespace NlsGge.GK38
noncomputable section

theorem p6Rotated_connector_pullback_next38 (f : ℂ → ℂ) (c : ℂ) (r : ℝ) (k : ℕ) :
    p6RotatedConnectorPullback38 f c r k 1 =
      p6RotatedConnectorPullback38 f c r (k+1) (-1) := by
  have he : (fun v : ℝ => p6RotatedSquareSector38 c r k v 1) =
      (fun v : ℝ => p6RotatedSquareSector38 c r (k+1) v (-1)) :=
    funext (fun v => p6RotatedSquareSector_connector38 c r v k)
  funext u
  exact congrArg (fun h : ℝ → ℂ => f (h u)*deriv h u) he

theorem p6Rotated_connector_pullback_four38 (f : ℂ → ℂ) (c : ℂ) (r : ℝ) (y : ℝ) :
    p6RotatedConnectorPullback38 f c r 4 y = p6RotatedConnectorPullback38 f c r 0 y := by
  have he : (fun v : ℝ => p6RotatedSquareSector38 c r 4 v y) =
      (fun v : ℝ => p6RotatedSquareSector38 c r 0 v y) :=
    funext (fun v => by simpa using p6RotatedSquareSector_period_four38 c r v y 0)
  funext u
  exact congrArg (fun h : ℝ → ℂ => f (h u)*deriv h u) he

theorem p6Four_rotated_sectors_scalar_transport38 (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (p6SquareAnnulus38 c r)) :
    (∀ k : ℕ, k < 4 →
      IntervalIntegrable (p6RotatedSectorPullback38 f c r k 0) volume 0 1 ∧
      IntervalIntegrable (p6RotatedSectorPullback38 f c r k 1) volume 0 1 ∧
      IntervalIntegrable (p6RotatedConnectorPullback38 f c r k (-1)) volume 0 1 ∧
      IntervalIntegrable (p6RotatedConnectorPullback38 f c r k 1) volume 0 1) ∧
    (∑ k ∈ Finset.range 4, ∫ u : ℝ in (0 : ℝ)..1, p6RotatedSectorPullback38 f c r k 0 u) =
      ∑ k ∈ Finset.range 4, ∫ u : ℝ in (0 : ℝ)..1, p6RotatedSectorPullback38 f c r k 1 u := by
  have hb := fun k => p6Rotated_sector_scalar_boundary38 c r k hr f hf
  refine ⟨fun k _ => ⟨(hb k).1,(hb k).2.1,(hb k).2.2.1,(hb k).2.2.2.1⟩,?_⟩
  have h0 := (hb 0).2.2.2.2
  have h1 := (hb 1).2.2.2.2
  have h2 := (hb 2).2.2.2.2
  have h3 := (hb 3).2.2.2.2
  rw [p6Rotated_connector_pullback_next38 f c r 0] at h0
  rw [p6Rotated_connector_pullback_next38 f c r 1] at h1
  rw [p6Rotated_connector_pullback_next38 f c r 2] at h2
  rw [p6Rotated_connector_pullback_next38 f c r 3,
    p6Rotated_connector_pullback_four38 f c r (-1)] at h3
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  linear_combination h0+h1+h2+h3

end
end NlsGge.GK38
