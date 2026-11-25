import NlsGge.GK38.AbelianNormalizedSquareEdges
import NlsGge.GK38.AbelianFourCircleArcs
import NlsGge.GK38.AbelianFourSectorCancellation
import NlsGge.GK38.AbelianSquareEdgeIntegrability

/-! SOURCE ONLY: actual circle-to-square Cauchy transport, with interior cuts.
All circle/arc/connector/edge integrabilities are earned BEFORE each identity.
The exact target and source-equivalent route were recorded before proof.
UNCOMPILED/no native scope/no finite-excision or period-value oracle. -/
set_option autoImplicit false
open Set MeasureTheory
open scoped Interval
namespace NlsGge.GK38
noncomputable section

theorem p6Circle_square_integral38 (f : ℂ → ℂ) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (p6SquareAnnulus38 c r)) :
    CircleIntegrable f c r ∧
    IntervalIntegrable (fun x : ℝ => f ((x : ℂ)+((c.im-r : ℝ) : ℂ)*Complex.I))
      volume (c.re-r) (c.re+r) ∧
    IntervalIntegrable (fun x : ℝ => f ((x : ℂ)+((c.im+r : ℝ) : ℂ)*Complex.I))
      volume (c.re-r) (c.re+r) ∧
    IntervalIntegrable (fun y : ℝ => f (((c.re-r : ℝ) : ℂ)+(y : ℂ)*Complex.I))
      volume (c.im-r) (c.im+r) ∧
    IntervalIntegrable (fun y : ℝ => f (((c.re+r : ℝ) : ℂ)+(y : ℂ)*Complex.I))
      volume (c.im-r) (c.im+r) ∧
    circleIntegral f c r = p6RectBoundary38 f (c.re-r) (c.re+r) (c.im-r) (c.im+r) := by
  have hcircle := p6Annulus_four_sector_arcs_circle38 c r hr.le f hf
  have htransport := p6Four_rotated_sectors_scalar_transport38 c r hr.le f hf
  have hsquare := p6Four_normalized_square_edges38 c r hr.le f hf
  have hedges := p6Annulus_square_edges_integrable38 c r hr.le f hf
  refine ⟨hcircle.1,hedges.1,hedges.2.1,hedges.2.2.1,hedges.2.2.2,?_⟩
  exact hcircle.2.2.trans (htransport.2.trans hsquare.2)

end
end NlsGge.GK38
