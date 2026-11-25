import NlsGge.GK38.AbelianSquareEdgeAffineGeometry
import NlsGge.GK38.AbelianSquareEdgeCoordinateContinuity
import NlsGge.GK38.AbelianComplexAffineLineIntegral
import NlsGge.GK38.AbelianRectangularExcision
import Lean.Elab.Tactic.Omega

/-! SOURCE ONLY: actual four straight-edge integral orientations. Genuine
coordinate/pullback CIs and curveFUNCTION equalities precede every identity.
Analyticity is required only on the annular slab; interior cuts are retained.
Exact target/English preceded proof. UNCOMPILED/no native scope. -/
set_option autoImplicit false
open Set MeasureTheory
open scoped Interval
namespace NlsGge.GK38
noncomputable section

theorem p6Four_square_edge_raw_integrals38 (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (p6SquareAnnulus38 c r)) :
    (∀ k : ℕ, k < 4 → IntervalIntegrable
      (fun y : ℝ => f (p6RotatedSquareSector38 c r k 1 y)*
        deriv (fun t : ℝ => p6RotatedSquareSector38 c r k 1 t) y) volume (-1) 1) ∧
    (∑ k ∈ Finset.range 4, ∫ y : ℝ in (-1 : ℝ)..1,
      f (p6RotatedSquareSector38 c r k 1 y)*
        deriv (fun t : ℝ => p6RotatedSquareSector38 c r k 1 t) y) =
      p6RectBoundary38 f (c.re-r) (c.re+r) (c.im-r) (c.im+r) := by
  let J : (ℝ → ℂ) → ℂ := fun g => ∫ y : ℝ in (-1 : ℝ)..1, f (g y)*deriv g y
  have hcoord := p6Annulus_edge_coordinate_continuity38 c r hr f hf
  have hminus (x : ℝ) : |(x-r)-x|=r := by
    have he : (x-r)-x = -r := by ring
    rw [he,abs_neg,abs_of_nonneg hr]
  have hplus (x : ℝ) : |(x+r)-x|=r := by
    have he : (x+r)-x = r := by ring
    rw [he,abs_of_nonneg hr]
  have hline0 := p6Complex_affine_line_pullback38 f
    ((c.re+r : ℝ) : ℂ) Complex.I r c.im (hcoord.2 (c.re+r) (hplus c.re))
  have hline1 := p6Complex_affine_line_pullback38 f
    (((c.im+r : ℝ) : ℂ)*Complex.I) (1 : ℂ) (-r) c.re (by
      simpa only [sub_neg_eq_add,← sub_eq_add_neg,Set.uIcc_comm] using
        hcoord.1 (c.im+r) (hplus c.im))
  have hline2 := p6Complex_affine_line_pullback38 f
    ((c.re-r : ℝ) : ℂ) Complex.I (-r) c.im (by
      simpa only [sub_neg_eq_add,← sub_eq_add_neg,Set.uIcc_comm] using
        hcoord.2 (c.re-r) (hminus c.re))
  have hline3 := p6Complex_affine_line_pullback38 f
    (((c.im-r : ℝ) : ℂ)*Complex.I) (1 : ℂ) r c.re
    (hcoord.1 (c.im-r) (hminus c.im))
  have he := p6Square_edge_affine_curves38 c r
  have htransfer (g h : ℝ → ℂ) (hgh : g=h) (z : ℂ)
      (hp : IntervalIntegrable (fun y : ℝ => f (h y)*deriv h y) volume (-1) 1 ∧ J h=z) :
      IntervalIntegrable (fun y : ℝ => f (g y)*deriv g y) volume (-1) 1 ∧ J g=z := by
    simpa only [hgh] using hp
  have h0 := htransfer _ _ he.1 _ ⟨hline0.1,hline0.2.2⟩
  have h1 := htransfer _ _ he.2.1 _ ⟨hline1.1,hline1.2.2⟩
  have h2 := htransfer _ _ he.2.2.1 _ ⟨hline2.1,hline2.2.2⟩
  have h3 := htransfer _ _ he.2.2.2 _ ⟨hline3.1,hline3.2.2⟩
  have hrevx :
      (∫ x : ℝ in (c.re+r)..(c.re-r),
        f ((x : ℂ)+((c.im+r : ℝ) : ℂ)*Complex.I)) =
      -(∫ x : ℝ in (c.re-r)..(c.re+r),
        f ((x : ℂ)+((c.im+r : ℝ) : ℂ)*Complex.I)) :=
    intervalIntegral.integral_symm _ _
  have hrevy :
      (∫ y : ℝ in (c.im+r)..(c.im-r), f (((c.re-r : ℝ) : ℂ)+(y : ℂ)*Complex.I)) =
      -(∫ y : ℝ in (c.im-r)..(c.im+r), f (((c.re-r : ℝ) : ℂ)+(y : ℂ)*Complex.I)) :=
    intervalIntegral.integral_symm _ _
  have h1value : J (fun y : ℝ => p6RotatedSquareSector38 c r 1 1 y) =
      -(∫ x : ℝ in (c.re-r)..(c.re+r),
        f ((x : ℂ)+((c.im+r : ℝ) : ℂ)*Complex.I)) := by
    simpa only [sub_neg_eq_add,← sub_eq_add_neg,one_mul,hrevx,mul_one,
      add_comm (((c.im+r : ℝ) : ℂ)*Complex.I)] using h1.2
  have h2value : J (fun y : ℝ => p6RotatedSquareSector38 c r 2 1 y) =
      Complex.I*(-(∫ y : ℝ in (c.im-r)..(c.im+r),
        f (((c.re-r : ℝ) : ℂ)+(y : ℂ)*Complex.I))) := by
    simpa only [sub_neg_eq_add,← sub_eq_add_neg,hrevy] using h2.2
  have h3value : J (fun y : ℝ => p6RotatedSquareSector38 c r 3 1 y) =
      ∫ x : ℝ in (c.re-r)..(c.re+r),
        f ((x : ℂ)+((c.im-r : ℝ) : ℂ)*Complex.I) := by
    simpa only [one_mul,mul_one,add_comm (((c.im-r : ℝ) : ℂ)*Complex.I)] using h3.2
  refine ⟨?_,?_⟩
  · intro k hk
    have hcases : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    rcases hcases with rfl | rfl | rfl | rfl
    · exact h0.1
    · exact h1.1
    · exact h2.1
    · exact h3.1
  · change (∑ k ∈ Finset.range 4, J (fun y : ℝ => p6RotatedSquareSector38 c r k 1 y)) = _
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
    rw [h0.2,h1value,h2value,h3value]
    unfold p6RectBoundary38
    ring

end
end NlsGge.GK38
