import NlsGge.GK38.AbelianNormalizedSectorArc
import Mathlib.Tactic.Ring

/-! SOURCE ONLY: four genuine adjacent quarter intervals make one fullcircle.
Actual periodCI/quarterCIs precede finite telescope and periodicshift. Actual
complex density realizes generic premises; no contouridentity assumed.
Exact targets+English preceded proof; UNCOMPILED, outside current native. -/
set_option autoImplicit false
open Set MeasureTheory
open scoped Interval
namespace NlsGge.GK38
noncomputable section

theorem p6Four_quarter_interval_sum38 (J : ℝ → ℂ) (hJ : Continuous J)
    (hperiod : Function.Periodic J (2*Real.pi)) :
    IntervalIntegrable J volume 0 (2*Real.pi) ∧
    (∀ k : ℕ, k < 4 → IntervalIntegrable J volume
      (-Real.pi/4+(k : ℝ)*(Real.pi/2)) (Real.pi/4+(k : ℝ)*(Real.pi/2))) ∧
    (∑ k ∈ Finset.range 4, ∫ θ : ℝ in (-Real.pi/4+(k : ℝ)*(Real.pi/2))..
      (Real.pi/4+(k : ℝ)*(Real.pi/2)), J θ) = ∫ θ : ℝ in (0 : ℝ)..(2*Real.pi), J θ := by
  let a : ℕ → ℝ := fun k => -Real.pi/4+(k : ℝ)*(Real.pi/2)
  have hnext (k : ℕ) : Real.pi/4+(k : ℝ)*(Real.pi/2) = a (k+1) := by
    dsimp [a]
    push_cast
    ring
  have hCI : ∀ k < 4, IntervalIntegrable J volume (a k) (a (k+1)) :=
    fun k _ => hJ.intervalIntegrable _ _
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (a := a) (n := 4) hCI
  refine ⟨hJ.intervalIntegrable _ _,fun k _ => hJ.intervalIntegrable _ _,?_⟩
  calc
    _ = ∑ k ∈ Finset.range 4, ∫ θ : ℝ in (a k)..(a (k+1)), J θ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hnext]
    _ = ∫ θ : ℝ in (a 0)..(a 4), J θ := hsum
    _ = ∫ θ : ℝ in (a 0)..(a 0+2*Real.pi), J θ := by
      have hlast : a 4 = a 0+2*Real.pi := by dsimp [a]; ring
      rw [hlast]
    _ = ∫ θ : ℝ in (0 : ℝ)..(2*Real.pi), J θ := by
      simpa using hperiod.intervalIntegral_add_eq (a 0) 0

theorem p6Annulus_four_sector_arcs_circle38 (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (p6SquareAnnulus38 c r)) :
    CircleIntegrable f c r ∧
    (∀ k : ℕ, k < 4 → IntervalIntegrable (p6RotatedSectorPullback38 f c r k 0) volume 0 1) ∧
    circleIntegral f c r =
      ∑ k ∈ Finset.range 4, ∫ u : ℝ in (0 : ℝ)..1, p6RotatedSectorPullback38 f c r k 0 u := by
  have hc := p6Annulus_circle_integral_param38 c r hr f hf
  have hquarters := p6Four_quarter_interval_sum38 (p6CirclePullback38 f c r)
    (p6Annulus_circle_pullback_continuous38 c r hr f hf) (p6CirclePullback_periodic38 f c r)
  have harc := fun k => p6Annulus_normalized_sector_arc38 c r k hr f hf
  have hsum : (∑ k ∈ Finset.range 4,
      ∫ u : ℝ in (0 : ℝ)..1, p6RotatedSectorPullback38 f c r k 0 u) =
      ∑ k ∈ Finset.range 4, ∫ θ : ℝ in (-Real.pi/4+(k : ℝ)*(Real.pi/2))..
        (Real.pi/4+(k : ℝ)*(Real.pi/2)), p6CirclePullback38 f c r θ := by
    apply Finset.sum_congr rfl
    intro k hk
    exact (harc k).2.2
  exact ⟨hc.1,fun k _ => (harc k).1,hc.2.2.trans (hquarters.2.2.symm.trans hsum.symm)⟩

end
end NlsGge.GK38
