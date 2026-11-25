import NlsGge.Ramer.FiniteJacobi
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Trace

/-!
# The exact Ramer formula for a standard Gaussian in finite dimensions

`V` is a finite-dimensional real inner product space with its canonical volume.
In the application, `V` is a finite Fourier head with the Cameron–Martin inner
product, whose norm squared is `2 Σ q_n |h_n|²`. The standard Gaussian of that
inner product has density `(2π)^{-n/2} exp(-‖x‖²/2)`, and `‖x‖²/2` is
`A_q(x)` in the notation of v2 `prop:gaussiancommon`. The identification of
this measure with the project's concrete finite Fourier head law
(`NlsGge.Measure.fourierPlaneGaussian`) is a separate bridge obligation and is
NOT proved here.

Contents:
* `finiteStdGaussian V`, proved to be a probability measure;
* `finiteRamerDensity T x = |det DT(x)| exp(-(‖T x‖² - ‖x‖²)/2)`;
* `finiteStdGaussian_map_symm`: `(T⁻¹)_# γ = J_T γ`, the inverse-pushforward identity;
* `lintegral_finiteRamerDensity`: `∫ J_T dγ = 1`;
* `finiteRamerDensity_pos`: `J_T > 0` everywhere when `T⁻¹` is differentiable;
* `finiteDet2`, `finiteGaussianDivergence` and the algebraic identity
  `|det₂(I+DK)| exp(-δK - ‖K‖²/2) = |det DT| exp(-(‖Tx‖²-‖x‖²)/2)`.

`finiteDet2 B := det(I+B) · exp(-tr B)` is the finite-rank value that the
sibling det₂ package must reproduce (interface item 3). It is a local
finite-dimensional definition, not the Hilbert–Schmidt det₂.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Real
open scoped ENNReal RealInnerProductSpace

namespace NlsGge.Ramer

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

variable (V) in
/-- Density of the standard Gaussian of the inner product of `V`. -/
def finiteGaussianDensity (x : V) : ℝ :=
  (2 * π) ^ (-(Module.finrank ℝ V : ℝ) / 2) * Real.exp (-(‖x‖ ^ 2) / 2)

variable (V) in
/-- The standard Gaussian of the inner product of `V`. -/
def finiteStdGaussian : Measure V :=
  volume.withDensity (fun x => ENNReal.ofReal (finiteGaussianDensity V x))

theorem finiteGaussianDensity_pos (x : V) : 0 < finiteGaussianDensity V x := by
  unfold finiteGaussianDensity
  have : 0 < 2 * π := by positivity
  positivity

theorem continuous_finiteGaussianDensity : Continuous (finiteGaussianDensity V) := by
  unfold finiteGaussianDensity
  fun_prop

theorem integral_finiteGaussianDensity : ∫ x : V, finiteGaussianDensity V x = 1 := by
  unfold finiteGaussianDensity
  rw [integral_const_mul]
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := V) (b := (1 / 2 : ℝ)) (by norm_num)
  have hfun : (fun x : V => Real.exp (-(‖x‖ ^ 2) / 2)) =
      (fun x : V => Real.exp (-(1 / 2 : ℝ) * ‖x‖ ^ 2)) := by
    funext x; congr 1; ring
  rw [hfun, h]
  have h2 : π / (1 / 2 : ℝ) = 2 * π := by ring
  rw [h2, ← Real.rpow_add (by positivity)]
  have h3 : -(Module.finrank ℝ V : ℝ) / 2 + (Module.finrank ℝ V : ℝ) / 2 = 0 := by ring
  rw [h3, Real.rpow_zero]

instance finiteStdGaussian_isProbability : IsProbabilityMeasure (finiteStdGaussian V) := by
  constructor
  rw [finiteStdGaussian, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_finiteGaussianDensity, ENNReal.ofReal_one]
  · apply Integrable.of_integral_ne_zero
    rw [integral_finiteGaussianDensity]; exact one_ne_zero
  · exact Filter.Eventually.of_forall (fun x => (finiteGaussianDensity_pos x).le)

/-- The finite-dimensional Jacobian density for the inverse pushforward:
`J_T(x) = |det DT(x)| exp(-A(T x) + A(x))` with `A(x) = ‖x‖²/2`. -/
def finiteRamerDensity (T : V → V) (x : V) : ℝ :=
  |(fderiv ℝ T x).det| * Real.exp (-(‖T x‖ ^ 2 - ‖x‖ ^ 2) / 2)

theorem finiteRamerDensity_nonneg (T : V → V) (x : V) : 0 ≤ finiteRamerDensity T x := by
  unfold finiteRamerDensity; positivity

theorem measurable_finiteRamerDensity (T : V ≃ₜ V) :
    Measurable (finiteRamerDensity (T : V → V)) := by
  unfold finiteRamerDensity
  have hdet : Measurable (fun x : V => (fderiv ℝ T x).det) :=
    ContinuousLinearMap.continuous_det.measurable.comp (measurable_fderiv ℝ T)
  have hexp : Measurable (fun x : V => Real.exp (-(‖T x‖ ^ 2 - ‖x‖ ^ 2) / 2)) := by
    have : Continuous (fun x : V => Real.exp (-(‖T x‖ ^ 2 - ‖x‖ ^ 2) / 2)) := by
      have := T.continuous; fun_prop
    exact this.measurable
  exact (continuous_abs.measurable.comp hdet).mul hexp

/-- **Finite-dimensional Ramer formula (inverse-pushforward orientation).**
For a homeomorphism `T` of `V` that is differentiable everywhere,
`(T⁻¹)_# γ = J_T γ` with `J_T = |det DT| exp(-(‖T x‖² - ‖x‖²)/2)`. -/
theorem finiteStdGaussian_map_symm (T : V ≃ₜ V) (hT : Differentiable ℝ T) :
    (finiteStdGaussian V).map T.symm =
      (finiteStdGaussian V).withDensity
        (fun x => ENNReal.ofReal (finiteRamerDensity (T : V → V) x)) := by
  have hρ : Measurable (fun x : V => ENNReal.ofReal (finiteGaussianDensity V x)) :=
    (continuous_finiteGaussianDensity.measurable).ennreal_ofReal
  rw [finiteStdGaussian, map_symm_withDensity_eq_withDensity_absDet_mul volume T hT,
    ← withDensity_mul volume hρ (measurable_finiteRamerDensity T).ennreal_ofReal]
  congr 1
  funext x
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (abs_nonneg _),
    ← ENNReal.ofReal_mul (finiteGaussianDensity_pos x).le]
  congr 1
  unfold finiteRamerDensity finiteGaussianDensity
  have hexp : Real.exp (-(‖T x‖ ^ 2) / 2) =
      Real.exp (-(‖x‖ ^ 2) / 2) * Real.exp (-(‖T x‖ ^ 2 - ‖x‖ ^ 2) / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hexp]; ring

/-- Unit mass: `∫ J_T dγ = 1`, derived from the inverse-pushforward identity
and the fact that `γ` is a probability measure. -/
theorem lintegral_finiteRamerDensity (T : V ≃ₜ V) (hT : Differentiable ℝ T) :
    ∫⁻ x, ENNReal.ofReal (finiteRamerDensity (T : V → V) x) ∂(finiteStdGaussian V) = 1 := by
  have h := congrArg (fun ν : Measure V => ν Set.univ) (finiteStdGaussian_map_symm T hT)
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    Measure.map_apply T.symm.continuous.measurable MeasurableSet.univ,
    Set.preimage_univ, measure_univ] at h
  exact h.symm

/-- Real integrability and real integral one. -/
theorem integral_finiteRamerDensity (T : V ≃ₜ V) (hT : Differentiable ℝ T) :
    Integrable (finiteRamerDensity (T : V → V)) (finiteStdGaussian V) ∧
      ∫ x, finiteRamerDensity (T : V → V) x ∂(finiteStdGaussian V) = 1 := by
  have hlin := lintegral_finiteRamerDensity T hT
  have hmeas := (measurable_finiteRamerDensity T).aestronglyMeasurable
    (μ := finiteStdGaussian V)
  have hint : Integrable (finiteRamerDensity (T : V → V)) (finiteStdGaussian V) := by
    refine ⟨hmeas, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall
      (fun x => finiteRamerDensity_nonneg _ x)), hlin]
    exact ENNReal.one_lt_top
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall
    (fun x => finiteRamerDensity_nonneg _ x)) hmeas, hlin, ENNReal.toReal_one]

/-- Strict positivity everywhere, from invertibility of the derivative, which
itself follows from differentiability of `T⁻¹` (chain rule). -/
theorem finiteRamerDensity_pos (T : V ≃ₜ V) (hT : Differentiable ℝ T)
    (hTs : Differentiable ℝ T.symm) (x : V) : 0 < finiteRamerDensity (T : V → V) x := by
  unfold finiteRamerDensity
  have := det_fderiv_ne_zero_of_symm_differentiable T hT hTs x
  positivity

/-! ### det₂ and Gaussian divergence in finite dimensions -/

/-- Finite-rank value `det₂(I + B) = det(I + B) exp(-tr B)`. -/
def finiteDet2 (B : V →L[ℝ] V) : ℝ :=
  (ContinuousLinearMap.id ℝ V + B).det * Real.exp (-(LinearMap.trace ℝ V (B : V →ₗ[ℝ] V)))

/-- Finite-dimensional Gaussian divergence of a differentiable vector field:
score pairing minus real trace, `δF(x) = ⟪x, F x⟫ - tr DF(x)`. -/
def finiteGaussianDivergence (F : V → V) (x : V) : ℝ :=
  ⟪x, F x⟫ - LinearMap.trace ℝ V ((fderiv ℝ F x : V →L[ℝ] V) : V →ₗ[ℝ] V)

/-- **Trace cancellation** (interface item 7): for real finite-dimensional `V`,
`x k : V` and a linear `B`, with `d = ⟪x,k⟫ - tr B`,
`|det₂(I+B)| exp(-d - ‖k‖²/2) = |det(I+B)| exp(-(‖x+k‖² - ‖x‖²)/2)`.
No invertibility or integrability is used. -/
theorem abs_finiteDet2_mul_exp_eq (B : V →L[ℝ] V) (x k : V) :
    |finiteDet2 B| *
        Real.exp (-(⟪x, k⟫ - LinearMap.trace ℝ V (B : V →ₗ[ℝ] V)) - ‖k‖ ^ 2 / 2) =
      |(ContinuousLinearMap.id ℝ V + B).det| *
        Real.exp (-(‖x + k‖ ^ 2 - ‖x‖ ^ 2) / 2) := by
  unfold finiteDet2
  rw [abs_mul, abs_of_pos (Real.exp_pos _), mul_assoc, ← Real.exp_add]
  congr 2
  rw [norm_add_sq_real]
  ring

/-- The finite Ramer density in det₂/divergence form, for `T = id + K`. -/
theorem finiteRamerDensity_eq_det2_form (T : V → V) (hT : Differentiable ℝ T) (x : V) :
    finiteRamerDensity T x =
      |finiteDet2 (fderiv ℝ (fun y => T y - y) x)| *
        Real.exp (-finiteGaussianDivergence (fun y => T y - y) x -
          ‖T x - x‖ ^ 2 / 2) := by
  have hK : fderiv ℝ (fun y => T y - y) x = fderiv ℝ T x - ContinuousLinearMap.id ℝ V := by
    rw [fderiv_fun_sub (hT x) differentiableAt_fun_id, fderiv_fun_id]
  have hsum : ContinuousLinearMap.id ℝ V + fderiv ℝ (fun y => T y - y) x = fderiv ℝ T x := by
    rw [hK]; abel
  unfold finiteGaussianDivergence
  rw [neg_sub, show (LinearMap.trace ℝ V) ((fderiv ℝ (fun y => T y - y) x : V →L[ℝ] V) :
      V →ₗ[ℝ] V) - ⟪x, T x - x⟫ = -(⟪x, T x - x⟫ - (LinearMap.trace ℝ V)
      ((fderiv ℝ (fun y => T y - y) x : V →L[ℝ] V) : V →ₗ[ℝ] V)) by ring,
    abs_finiteDet2_mul_exp_eq, hsum]
  unfold finiteRamerDensity
  congr 3
  abel_nf

/-- **Finite-dimensional E05 statement in the v2 notation.** For a
homeomorphism `T = id + K` of `V` with `T` and `T⁻¹` differentiable,
`(T⁻¹)_# γ = J_T γ`, `J_T = |det₂(I + DK)| exp(-δK - ‖K‖²/2) > 0`, and
`∫ J_T dγ = 1` (both as an ENNReal integral and as a real integral of an
integrable function). -/
theorem finite_ramer_formula (T : V ≃ₜ V) (hT : Differentiable ℝ T)
    (hTs : Differentiable ℝ T.symm) :
    (finiteStdGaussian V).map T.symm =
        (finiteStdGaussian V).withDensity (fun x => ENNReal.ofReal
          (|finiteDet2 (fderiv ℝ (fun y => T y - y) x)| *
            Real.exp (-finiteGaussianDivergence (fun y => T y - y) x -
              ‖T x - x‖ ^ 2 / 2))) ∧
      (∀ x, 0 < |finiteDet2 (fderiv ℝ (fun y => T y - y) x)| *
            Real.exp (-finiteGaussianDivergence (fun y => T y - y) x -
              ‖T x - x‖ ^ 2 / 2)) ∧
      Integrable (finiteRamerDensity (T : V → V)) (finiteStdGaussian V) ∧
      ∫ x, finiteRamerDensity (T : V → V) x ∂(finiteStdGaussian V) = 1 := by
  have hform : ∀ x, finiteRamerDensity (T : V → V) x =
      |finiteDet2 (fderiv ℝ (fun y => T y - y) x)| *
        Real.exp (-finiteGaussianDivergence (fun y => T y - y) x - ‖T x - x‖ ^ 2 / 2) :=
    fun x => finiteRamerDensity_eq_det2_form T hT x
  refine ⟨?_, ?_, integral_finiteRamerDensity T hT⟩
  · rw [finiteStdGaussian_map_symm T hT]
    congr 1; funext x; rw [hform x]
  · intro x; rw [← hform x]; exact finiteRamerDensity_pos T hT hTs x

end NlsGge.Ramer
