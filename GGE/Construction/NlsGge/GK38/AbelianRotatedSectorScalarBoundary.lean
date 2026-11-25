import NlsGge.GK38.AbelianRotatedSectorHomotopy
import NlsGge.GK38.AbelianComplexCurveParameter

/-! SOURCE ONLY: genuine scalar integrabilities precede sector transport.
All four actual curve/parameter identities are earned from global C2 slices
and actual compact trace containment. No connector cancellation oracle.
Exact targets+English preceded proofs; UNCOMPILED, outside next4 scope. -/
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology unitInterval Interval
namespace NlsGge.GK38
noncomputable section

def p6RotatedSectorPullback38 (f : ℂ → ℂ) (c : ℂ) (r : ℝ) (k : ℕ) (t : ℝ) : ℝ → ℂ :=
  fun u => f (p6RotatedSquareSector38 c r k t (2*u-1)) *
    deriv (fun v : ℝ => p6RotatedSquareSector38 c r k t (2*v-1)) u

def p6RotatedConnectorPullback38 (f : ℂ → ℂ) (c : ℂ) (r : ℝ) (k : ℕ) (y : ℝ) : ℝ → ℂ :=
  fun u => f (p6RotatedSquareSector38 c r k u y) *
    deriv (fun v : ℝ => p6RotatedSquareSector38 c r k v y) u

theorem p6Rotated_sector_scalar_boundary38 (c : ℂ) (r : ℝ) (k : ℕ) (hr : 0 ≤ r)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (p6SquareAnnulus38 c r)) :
    IntervalIntegrable (p6RotatedSectorPullback38 f c r k 0) volume 0 1 ∧
    IntervalIntegrable (p6RotatedSectorPullback38 f c r k 1) volume 0 1 ∧
    IntervalIntegrable (p6RotatedConnectorPullback38 f c r k (-1)) volume 0 1 ∧
    IntervalIntegrable (p6RotatedConnectorPullback38 f c r k 1) volume 0 1 ∧
    (∫ u : ℝ in (0 : ℝ)..1, p6RotatedSectorPullback38 f c r k 0 u) +
      (∫ u : ℝ in (0 : ℝ)..1, p6RotatedConnectorPullback38 f c r k 1 u) =
    (∫ u : ℝ in (0 : ℝ)..1, p6RotatedSectorPullback38 f c r k 1 u) +
      (∫ u : ℝ in (0 : ℝ)..1, p6RotatedConnectorPullback38 f c r k (-1) u) := by
  have hpath (t : I) :
      IntervalIntegrable (p6RotatedSectorPullback38 f c r k (t : ℝ)) volume 0 1 ∧
      (∫ᶜ z in p6RotatedSquareSectorPath38 c r k (t : ℝ), p6ComplexForm38 f z) =
        ∫ u : ℝ in (0 : ℝ)..1, p6RotatedSectorPullback38 f c r k (t : ℝ) u := by
    have hC1 : ContDiff ℝ 1
        (fun u : ℝ => p6RotatedSquareSector38 c r k (t : ℝ) (2*u-1)) :=
      ((p6RotatedSquareSector_contDiff38 c r k).comp
        (show ContDiff ℝ 2 (fun u : ℝ => ((t : ℝ),2*u-1)) from by fun_prop)).of_le (by decide)
    have htrace : ContinuousOn f ((fun u : ℝ =>
        p6RotatedSquareSector38 c r k (t : ℝ) (2*u-1)) '' Set.Icc (0 : ℝ) 1) := by
      apply hf.continuousOn.mono
      rintro z ⟨u,hu,rfl⟩
      have hy : |2*u-1| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hu.1,hu.2]
      have hg := p6RotatedSquareSector_geometry38 c r k (t : ℝ) (2*u-1) hr t.property hy
      exact ⟨hg.1,hg.2.1⟩
    have hp := p6Complex_curve_integral_param38 (p6RotatedSquareSectorPath38 c r k (t : ℝ))
      (fun u : ℝ => p6RotatedSquareSector38 c r k (t : ℝ) (2*u-1)) hC1 (by intro u; rfl) f htrace
    exact ⟨hp.2.1,hp.2.2⟩
  have hconnector (y : I) :
      IntervalIntegrable (p6RotatedConnectorPullback38 f c r k (2*(y : ℝ)-1)) volume 0 1 ∧
      (∫ᶜ z in (p6RotatedSquareSectorHomotopy38 c r k).evalAt y, p6ComplexForm38 f z) =
        ∫ u : ℝ in (0 : ℝ)..1, p6RotatedConnectorPullback38 f c r k (2*(y : ℝ)-1) u := by
    have hC1 : ContDiff ℝ 1
        (fun u : ℝ => p6RotatedSquareSector38 c r k u (2*(y : ℝ)-1)) :=
      ((p6RotatedSquareSector_contDiff38 c r k).comp
        (show ContDiff ℝ 2 (fun u : ℝ => (u,2*(y : ℝ)-1)) from by fun_prop)).of_le (by decide)
    have hy : |2*(y : ℝ)-1| ≤ 1 := by rw [abs_le]; constructor <;> linarith [y.property.1,y.property.2]
    have htrace : ContinuousOn f ((fun u : ℝ =>
        p6RotatedSquareSector38 c r k u (2*(y : ℝ)-1)) '' Set.Icc (0 : ℝ) 1) := by
      apply hf.continuousOn.mono
      rintro z ⟨u,hu,rfl⟩
      have hg := p6RotatedSquareSector_geometry38 c r k u (2*(y : ℝ)-1) hr hu hy
      exact ⟨hg.1,hg.2.1⟩
    have hp := p6Complex_curve_integral_param38 ((p6RotatedSquareSectorHomotopy38 c r k).evalAt y)
      (fun u : ℝ => p6RotatedSquareSector38 c r k u (2*(y : ℝ)-1)) hC1
      (by intro u; rfl) f htrace
    exact ⟨hp.2.1,hp.2.2⟩
  have hp0 := hpath (0 : I)
  have hp1 := hpath (1 : I)
  have hc0 := hconnector (0 : I)
  have hc1 := hconnector (1 : I)
  norm_num only [Set.Icc.coe_zero,Set.Icc.coe_one] at hp0 hp1 hc0 hc1
  have hboundary := p6Rotated_square_sector_boundary38 c r k hr f hf
  have hp0real :
      (∫ᶜ z in p6RotatedSquareSectorPath38 c r k (0 : ℝ), p6ComplexForm38 f z) =
        ∫ u : ℝ in (0 : ℝ)..1, p6RotatedSectorPullback38 f c r k 0 u := hp0.2
  have hp1real :
      (∫ᶜ z in p6RotatedSquareSectorPath38 c r k (1 : ℝ), p6ComplexForm38 f z) =
        ∫ u : ℝ in (0 : ℝ)..1, p6RotatedSectorPullback38 f c r k 1 u := hp1.2
  rw [hp0real,hc1.2,hp1real,hc0.2] at hboundary
  exact ⟨hp0.1,hp1.1,hc0.1,hc1.1,hboundary⟩

end
end NlsGge.GK38
