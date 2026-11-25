import NlsGge.GK38.AbelianComplexAffineSubstitution
import NlsGge.GK38.AbelianComplexArctanSubstitution
import NlsGge.GK38.AbelianRotatedSectorScalarBoundary
import NlsGge.GK38.AbelianCircleScalarPullback

/-! SOURCE ONLY: actual normalized sector arc is the shifted quarter circle.
Both CIs precede the identity. Actual curveFUNCTION equality precedes deriv;
real affine/arctan substitutions are genuinely complex-vector-valued. No
contour transport oracle. Exact target+English preceded proof. UNCOMPILED,
OUTSIDE the current four scientific scope. -/
set_option autoImplicit false
open Set Metric MeasureTheory
open scoped Interval
namespace NlsGge.GK38
noncomputable section

theorem p6Annulus_normalized_sector_arc38 (c : ℂ) (r : ℝ) (k : ℕ) (hr : 0 ≤ r)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (p6SquareAnnulus38 c r)) :
    IntervalIntegrable (p6RotatedSectorPullback38 f c r k 0) volume 0 1 ∧
    IntervalIntegrable (p6CirclePullback38 f c r) volume
      (-Real.pi/4+(k : ℝ)*(Real.pi/2)) (Real.pi/4+(k : ℝ)*(Real.pi/2)) ∧
    (∫ u : ℝ in (0 : ℝ)..1, p6RotatedSectorPullback38 f c r k 0 u) =
      ∫ θ : ℝ in (-Real.pi/4+(k : ℝ)*(Real.pi/2))..
        (Real.pi/4+(k : ℝ)*(Real.pi/2)), p6CirclePullback38 f c r θ := by
  let s : ℝ := (k : ℝ)*(Real.pi/2)
  let g : ℝ → ℂ := fun θ => circleMap c r (θ+s)
  have hcircle (θ : ℝ) : circleMap c r θ ∈ p6SquareAnnulus38 c r := by
    have hn : ‖circleMap c r θ-c‖ = r := by simp [abs_of_nonneg hr]
    refine ⟨hn.ge,?_⟩
    have hre := Complex.abs_re_le_norm (circleMap c r θ-c)
    simpa only [Complex.sub_re,hn] using hre
  have hg : ContDiff ℝ 1 g := ContDiff.comp
    (g := circleMap c r) (f := fun θ : ℝ => θ+s)
    (contDiff_circleMap c r) (by fun_prop)
  have hsector : ContDiff ℝ 1 (fun y : ℝ => p6RotatedSquareSector38 c r k 0 y) :=
    (ContDiff.comp
      (g := fun xy : ℝ × ℝ => p6RotatedSquareSector38 c r k xy.1 xy.2)
      (f := fun y : ℝ => ((0 : ℝ),y))
      (p6RotatedSquareSector_contDiff38 c r k) (by fun_prop)).of_le (by decide)
  have hfsector : ContinuousOn f
      ((fun y : ℝ => p6RotatedSquareSector38 c r k 0 y) '' Set.Icc (-1 : ℝ) 1) := by
    apply hf.continuousOn.mono
    rintro z ⟨y,hy,rfl⟩
    have hz := p6RotatedSquareSector_geometry38 c r k 0 y hr (by constructor <;> norm_num)
      (abs_le.mpr hy)
    exact ⟨hz.1,hz.2.1⟩
  have haffine := p6Complex_affine_curve_substitution38
    (fun y : ℝ => p6RotatedSquareSector38 c r k 0 y) hsector f hfsector
  have hfg : ContinuousOn f (g '' Set.Icc (-Real.pi/4) (Real.pi/4)) := by
    apply hf.continuousOn.mono
    rintro z ⟨θ,hθ,rfl⟩
    exact hcircle (θ+s)
  have harctan := p6Complex_arctan_curve_substitution38 g hg f hfg
  have heq : (fun y : ℝ => p6RotatedSquareSector38 c r k 0 y) = g ∘ Real.arctan :=
    p6Rotated_sector_circle_curve38 c r k
  have hderiv (θ : ℝ) : deriv g θ = circleMap 0 r (θ+s)*Complex.I := by
    simpa only [g,Function.comp_def,id_eq,one_smul] using
      ((hasDerivAt_circleMap c r (θ+s)).scomp θ ((hasDerivAt_id θ).add_const s)).deriv
  have hCIquarter : IntervalIntegrable (p6CirclePullback38 f c r) volume
      (-Real.pi/4+s) (Real.pi/4+s) :=
    (p6Annulus_circle_pullback_continuous38 c r hr f hf).intervalIntegrable
      (-Real.pi/4+s) (Real.pi/4+s)
  refine ⟨haffine.1,hCIquarter,?_⟩
  calc
    _ = ∫ y : ℝ in (-1 : ℝ)..1, f (p6RotatedSquareSector38 c r k 0 y) *
        deriv (fun v : ℝ => p6RotatedSquareSector38 c r k 0 v) y := haffine.2.2
    _ = ∫ y : ℝ in (-1 : ℝ)..1, f ((g ∘ Real.arctan) y)*deriv (g ∘ Real.arctan) y :=
      congrArg (fun h : ℝ → ℂ => ∫ y : ℝ in (-1 : ℝ)..1, f (h y)*deriv h y) heq
    _ = ∫ θ : ℝ in (-Real.pi/4)..(Real.pi/4), f (g θ)*deriv g θ := harctan.2.2
    _ = ∫ θ : ℝ in (-Real.pi/4)..(Real.pi/4), p6CirclePullback38 f c r (θ+s) := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      change f (g θ)*deriv g θ = f (g θ)*(circleMap 0 r (θ+s)*Complex.I)
      exact congrArg (fun w : ℂ => f (g θ)*w) (hderiv θ)
    _ = _ := intervalIntegral.integral_comp_add_right (p6CirclePullback38 f c r) s

end
end NlsGge.GK38
