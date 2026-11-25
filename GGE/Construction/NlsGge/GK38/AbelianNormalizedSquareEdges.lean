import NlsGge.GK38.AbelianSquareEdgeOrientedIntegrals
import NlsGge.GK38.AbelianComplexAffineSubstitution
import NlsGge.GK38.AbelianRotatedSectorScalarBoundary

/-! SOURCE ONLY: true normalized sector edges to actual CCW square boundary.
Actual global C1 curve/annular trace continuity earn BOTH affine CIs before
transport; no assumed boundary equality. Exact targets/English preceded proof.
UNCOMPILED/no native scope. -/
set_option autoImplicit false
open Set MeasureTheory
open scoped Interval
namespace NlsGge.GK38
noncomputable section

theorem p6Four_normalized_square_edges38 (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (p6SquareAnnulus38 c r)) :
    (∀ k : ℕ, k < 4 →
      IntervalIntegrable (p6RotatedSectorPullback38 f c r k 1) volume 0 1) ∧
    (∑ k ∈ Finset.range 4, ∫ u : ℝ in (0 : ℝ)..1,
      p6RotatedSectorPullback38 f c r k 1 u) =
      p6RectBoundary38 f (c.re-r) (c.re+r) (c.im-r) (c.im+r) := by
  have hraw := p6Four_square_edge_raw_integrals38 c r hr f hf
  have hsub (k : ℕ) := by
    have hcurve : ContDiff ℝ 1 (fun y : ℝ => p6RotatedSquareSector38 c r k 1 y) :=
      (ContDiff.comp
        (g := fun xy : ℝ × ℝ => p6RotatedSquareSector38 c r k xy.1 xy.2)
        (f := fun y : ℝ => ((1 : ℝ),y))
        (p6RotatedSquareSector_contDiff38 c r k) (by fun_prop)).of_le (by decide)
    have htrace : ContinuousOn f
        ((fun y : ℝ => p6RotatedSquareSector38 c r k 1 y) '' Set.Icc (-1 : ℝ) 1) := by
      apply hf.continuousOn.mono
      rintro z ⟨y,hy,rfl⟩
      have hz := p6RotatedSquareSector_geometry38 c r k 1 y hr
        (by constructor <;> norm_num) (abs_le.mpr hy)
      exact ⟨hz.1,hz.2.1⟩
    exact p6Complex_affine_curve_substitution38
      (fun y : ℝ => p6RotatedSquareSector38 c r k 1 y) hcurve f htrace
  refine ⟨fun k _ => (hsub k).1,?_⟩
  calc
    _ = ∑ k ∈ Finset.range 4, ∫ y : ℝ in (-1 : ℝ)..1,
        f (p6RotatedSquareSector38 c r k 1 y)*
          deriv (fun t : ℝ => p6RotatedSquareSector38 c r k 1 t) y := by
      apply Finset.sum_congr rfl
      intro k hk
      exact (hsub k).2.2
    _ = _ := hraw.2

end
end NlsGge.GK38
