import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Finite-dimensional Jacobi formula, inverse-pushforward orientation

For a homeomorphism `T` of a finite-dimensional real normed space that is
differentiable everywhere, and any measure `μ.withDensity ρ` with `μ` an
additive Haar measure, the inverse pushforward satisfies

  `(μ.withDensity ρ).map T.symm = μ.withDensity (|det DT| · ρ ∘ T)`.

Equivalently `(μ.withDensity ρ) (T '' A) = ∫_A |det DT x| ρ (T x) dμ(x)`.
This is the orientation of v2 `eq:Ramercommon` and of Zakai–Zeitouni (1992),
equation (1): `(T⁻¹)^* P₀ (A) = P₀ {ω : T⁻¹ ω ∈ A}`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace NlsGge.Ramer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The image of a set under a homeomorphism is the preimage under
its inverse. -/
theorem homeomorph_symm_preimage_eq_image (T : E ≃ₜ E) (A : Set E) :
    T.symm ⁻¹' A = T '' A := by
  ext y
  constructor
  · intro hy
    exact ⟨T.symm y, hy, T.apply_symm_apply y⟩
  · rintro ⟨x, hx, rfl⟩
    simpa using hx

/-- Finite-dimensional Jacobi formula in the inverse-pushforward orientation,
for an arbitrary (not necessarily finite) density `ρ` against an additive Haar
measure `μ`. Only everywhere differentiability of `T` is used; no invertibility
of the derivative is assumed or needed for the identity. -/
theorem map_symm_withDensity_eq_withDensity_absDet_mul
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (T : E ≃ₜ E) (hT : Differentiable ℝ T) (ρ : E → ℝ≥0∞) :
    (μ.withDensity ρ).map T.symm =
      μ.withDensity (fun x => ENNReal.ofReal |(fderiv ℝ T x).det| * ρ (T x)) := by
  ext A hA
  have himage : MeasurableSet (T '' A) :=
    T.toMeasurableEquiv.measurableSet_image.2 hA
  rw [Measure.map_apply T.symm.continuous.measurable hA,
    homeomorph_symm_preimage_eq_image, withDensity_apply _ himage,
    withDensity_apply _ hA]
  exact lintegral_image_eq_lintegral_abs_det_fderiv_mul μ hA
    (fun x _ => (hT x).hasFDerivAt.hasFDerivWithinAt) T.injective.injOn ρ

/-- Set form of the same identity: `∫_A |det DT| ρ ∘ T dμ = ν (T '' A)` with
`ν = μ.withDensity ρ`. -/
theorem setLIntegral_absDet_mul_eq_measure_image
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (T : E ≃ₜ E) (hT : Differentiable ℝ T) (ρ : E → ℝ≥0∞)
    {A : Set E} (hA : MeasurableSet A) :
    ∫⁻ x in A, ENNReal.ofReal |(fderiv ℝ T x).det| * ρ (T x) ∂μ =
      (μ.withDensity ρ) (T '' A) := by
  have h := congrArg (fun ν : Measure E => ν A)
    (map_symm_withDensity_eq_withDensity_absDet_mul μ T hT ρ)
  rw [Measure.map_apply T.symm.continuous.measurable hA,
    homeomorph_symm_preimage_eq_image, withDensity_apply _ hA] at h
  exact h.symm

/-- If the inverse is also differentiable, the derivative of `T` is invertible
at every point, so its determinant is nonzero. Proved from the chain rule for
`T.symm ∘ T = id`, not from global bijectivity alone. -/
theorem det_fderiv_ne_zero_of_symm_differentiable
    (T : E ≃ₜ E) (hT : Differentiable ℝ T) (hTs : Differentiable ℝ T.symm) (x : E) :
    (fderiv ℝ T x).det ≠ 0 := by
  have hcomp : fderiv ℝ (T.symm ∘ T) x =
      (fderiv ℝ T.symm (T x)).comp (fderiv ℝ T x) :=
    fderiv_comp x (hTs (T x)) (hT x)
  have hidfun : (T.symm ∘ T) = id := by
    funext y; simp
  have heq : (fderiv ℝ T.symm (T x)).comp (fderiv ℝ T x) =
      ContinuousLinearMap.id ℝ E := by
    rw [← hcomp, hidfun, fderiv_id]
  have hdet := congrArg
    (fun L : E →L[ℝ] E => LinearMap.det (L : E →ₗ[ℝ] E)) heq
  simp only [ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp,
    ContinuousLinearMap.coe_id, LinearMap.det_id] at hdet
  intro h0
  rw [ContinuousLinearMap.det] at h0
  rw [h0, mul_zero] at hdet
  exact zero_ne_one hdet

end NlsGge.Ramer
