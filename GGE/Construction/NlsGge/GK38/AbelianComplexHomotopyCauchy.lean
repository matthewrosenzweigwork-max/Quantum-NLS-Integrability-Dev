import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Tactic.Ring

/-! SOURCE ONLY: actual complex analytic functions realize closed 1-forms.
Only the COMPACT traced homotopy image is used for the closure-continuity gate.
Actual C² homotopy membership still must be earned for each geometric chart.
Exact targets+English preceded proof authoring. UNCOMPILED. -/
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology unitInterval
namespace NlsGge.GK38
noncomputable section

def p6ComplexForm38 (f : ℂ → ℂ) (z : ℂ) : ℂ →L[ℂ] ℂ :=
  ContinuousLinearMap.mul ℂ ℂ (f z)

def p6ComplexFormDeriv38 (f : ℂ → ℂ) (z : ℂ) : ℂ →L[ℝ] (ℂ →L[ℂ] ℂ) :=
  ((ContinuousLinearMap.mul ℂ ℂ).comp (fderiv ℂ f z)).restrictScalars ℝ

theorem p6ComplexForm_hasFDerivAt38 (f : ℂ → ℂ) (z : ℂ)
    (hf : AnalyticAt ℂ f z) :
    HasFDerivAt (p6ComplexForm38 f) (p6ComplexFormDeriv38 f z) z := by
  exact ((ContinuousLinearMap.mul ℂ ℂ).hasFDerivAt.comp z
    hf.differentiableAt.hasFDerivAt).restrictScalars ℝ

theorem p6ComplexForm_derivative_symmetric38 (f : ℂ → ℂ) (z u v : ℂ) :
    p6ComplexFormDeriv38 f z u v = p6ComplexFormDeriv38 f z v u := by
  have hu : fderiv ℂ f z u = u*(fderiv ℂ f z 1) := by
    simp [smul_eq_mul]
  have hv : fderiv ℂ f z v = v*(fderiv ℂ f z 1) := by
    simp [smul_eq_mul]
  change (fderiv ℂ f z u)*v = (fderiv ℂ f z v)*u
  rw [hu,hv]
  ring

theorem p6Complex_homotopy_boundary38 {a b c d : ℂ}
    {γ₀ : Path a b} {γ₁ : Path c d}
    (H : (γ₀ : C(I, ℂ)).Homotopy γ₁) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (Set.range H))
    (hC2 : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ => Set.IccExtend zero_le_one (H.extend xy.1) xy.2)
      (Set.Icc 0 1)) :
    (∫ᶜ z in γ₀, p6ComplexForm38 f z) + (∫ᶜ z in H.evalAt 1, p6ComplexForm38 f z) =
      (∫ᶜ z in γ₁, p6ComplexForm38 f z) + (∫ᶜ z in H.evalAt 0, p6ComplexForm38 f z) := by
  refine H.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt
    (t := Set.range H) (ω := p6ComplexForm38 f) (dω := p6ComplexFormDeriv38 f)
    ?_ ?_ ?_ ?_ hC2
  · intros
    apply mem_range_self
  · intro z hz
    exact (p6ComplexForm_hasFDerivAt38 f z (hf z hz)).hasFDerivWithinAt
  · rw [(isCompact_range (map_continuous H)).isClosed.closure_eq]
    exact (ContinuousLinearMap.mul ℂ ℂ).continuous.comp_continuousOn hf.continuousOn
  · intro z hz u hu v hv
    exact p6ComplexForm_derivative_symmetric38 f z u v

end
end NlsGge.GK38
