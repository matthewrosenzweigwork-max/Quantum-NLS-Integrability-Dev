import NlsGge.GK38.ActionUpperArc
import NlsGge.GK38.ActionBranchQuotientReflection
import NlsGge.GK38.ActionEllipseReflection
import NlsGge.GK38.ActionGapLocalization
import NlsGge.Spectral.ActualGapHeightSemicircleE02_38

set_option autoImplicit false
open Set Metric Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations
open NlsGge.Analysis.EllipseDeformation NlsGge.GK38.ActionEllipseContinuity
open scoped ComplexConjugate
namespace NlsGge.GK38.ActionCircleReduction
noncomputable section

theorem upperPrimitive_product_re_off_cuts (u : PhysicalL2) (x : ℝ)
    (hx : (x : ℂ) ∉ gapSegments38 (realSlice u)) :
    ((x : ℂ) * upperPrimitive u (x : ℂ)).re = 0 := by
  have hre : (upperPrimitive u (x : ℂ)).re = 0 := by
    calc
      _ = (actualQuasimomentumBoundaryE02_38 u x).im := by
        simp [upperPrimitive, actualQuasimomentumBoundaryE02_38, Complex.mul_re]
      _ = actualGapHeightE02_38 u x :=
        boundaryLimit_im_E02_38 u x _ (tendsto_actualQuasimomentumBoundaryE02_38 u x)
      _ = 0 := NlsGge.GK38.ActionGapLocalization.height_zero_off_cuts u x hx
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hre,
    mul_zero, zero_mul, sub_zero]

theorem curve_zero (c r δ : ℝ) : curve (c : ℂ) r δ 0 = ((c + r : ℝ) : ℂ) := by
  simp [curve, Complex.ofReal_add]

theorem curve_pi (c r δ : ℝ) : curve (c : ℂ) r δ Real.pi = ((c - r : ℝ) : ℂ) := by
  simp [curve, sub_eq_add_neg]

theorem endpoint_products_re_zero (u : PhysicalL2) (c r δ : ℝ) (hr : 0 < r)
    (hs : sphere (c : ℂ) r ⊆ actionCutDomain38 (realSlice u)) :
    (curve (c : ℂ) r δ 0 * upperPrimitive u (curve (c : ℂ) r δ 0)).re = 0 ∧
    (curve (c : ℂ) r δ Real.pi *
      upperPrimitive u (curve (c : ℂ) r δ Real.pi)).re = 0 := by
  have hzero : curve (c : ℂ) r δ 0 ∈ sphere (c : ℂ) r := by
    have he : curve (c : ℂ) r δ 0 = curve (c : ℂ) r 1 0 := by simp [curve]
    rw [he, curve_one]
    exact circleMap_mem_sphere (c : ℂ) hr.le 0
  have hpi : curve (c : ℂ) r δ Real.pi ∈ sphere (c : ℂ) r := by
    have he : curve (c : ℂ) r δ Real.pi = curve (c : ℂ) r 1 Real.pi := by simp [curve]
    rw [he, curve_one]
    exact circleMap_mem_sphere (c : ℂ) hr.le Real.pi
  rw [curve_zero] at hzero ⊢
  rw [curve_pi] at hpi ⊢
  exact ⟨upperPrimitive_product_re_off_cuts u (c + r) (hs hzero),
    upperPrimitive_product_re_off_cuts u (c - r) (hs hpi)⟩

theorem circle_integral_eq_neg_two_upper_primitive_re (u : PhysicalL2) (c r δ : ℝ)
    (hr : 0 < r) (hδ : 0 < δ)
    (hs : sphere (c : ℂ) r ⊆ actionCutDomain38 (realSlice u)) :
    circleIntegral (actionIntegrand38 (realSlice u)) (c : ℂ) r =
      -2 * ((∫ θ in (0 : ℝ)..Real.pi, velocity r δ θ *
        upperPrimitive u (curve (c : ℂ) r δ θ)).re : ℂ) := by
  have he := NlsGge.GK38.ActionEllipseDomain.actual_action_ellipse_eq_circle u (c : ℂ) r δ
    (by simp) hr hδ hs
  have hi : IntervalIntegrable
      (NlsGge.GK38.ActionEllipseReflection.pullback (actionIntegrand38 (realSlice u)) c r δ)
      volume 0 (2 * Real.pi) := he.1
  have hsym := NlsGge.GK38.ActionEllipseReflection.full_integral_eq_upper_add_conj c r δ hr hδ
    (NlsGge.GK38.ActionBranch.actionIntegrand_conj u) hi
  change (∫ θ in (0 : ℝ)..2 * Real.pi,
    velocity r δ θ * actionIntegrand38 (realSlice u) (curve (c : ℂ) r δ θ)) =
    (∫ θ in (0 : ℝ)..Real.pi,
      velocity r δ θ * actionIntegrand38 (realSlice u) (curve (c : ℂ) r δ θ)) +
    conj (∫ θ in (0 : ℝ)..Real.pi,
      velocity r δ θ * actionIntegrand38 (realSlice u) (curve (c : ℂ) r δ θ)) at hsym
  have hibp := NlsGge.GK38.ActionUpperArc.actual_upper_arc_integration_by_parts u c r δ hr hδ hs
  have hend := endpoint_products_re_zero u c r δ hr hs
  have hre := congrArg Complex.re hibp.2.2
  simp only [Complex.sub_re, hend.1, hend.2] at hre
  rw [← he.2.2, hsym, Complex.add_conj, hre]
  push_cast
  ring

end
end NlsGge.GK38.ActionCircleReduction
