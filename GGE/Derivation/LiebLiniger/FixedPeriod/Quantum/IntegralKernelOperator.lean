import LiebLiniger.FixedPeriod.Quantum.TransferCoefficientKernel
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
Actual L²-kernel operator, with the source conjugate-linear-first convention.
Author candidate; the root's lane B alone runs the compiler. The kernel and
both measures are genuine objects. No operator, bound, Hilbert--Schmidt identity,
or compactness conclusion is supplied as a premise.

The generic construction allows different sigma-finite input/output measures.
The transfer specialization uses unnormalized centered-interval length measure.
-/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace ComplexConjugate

namespace LiebLiniger.FixedPeriod.Quantum

section Conjugation
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

/-- Scalar conjugation with its correct complex *semilinearity*. -/
def complexConjugationCLM : ℂ →L⋆[ℂ] ℂ :=
  (starₗᵢ ℂ : ℂ ≃ₗᵢ⋆[ℂ] ℂ).toContinuousLinearEquiv.toContinuousLinearMap

/-- Pointwise conjugation on actual L² equivalence classes. -/
def conjugateL2 : Lp ℂ 2 μ →L⋆[ℂ] Lp ℂ 2 μ :=
  complexConjugationCLM.compLpL 2 μ

theorem conjugateL2_coeFn (u : Lp ℂ 2 μ) :
    conjugateL2 μ u =ᵐ[μ] fun x => conj (u x) :=
  complexConjugationCLM.coeFn_compLpL u

@[simp] theorem norm_conjugateL2 (u : Lp ℂ 2 μ) :
    ‖conjugateL2 μ u‖ = ‖u‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  apply congrArg ENNReal.toReal
  apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
  filter_upwards [conjugateL2_coeFn μ u] with x hx
  rw [hx, Complex.norm_conj]

end Conjugation

section KernelOperator
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]

/-- The Riesz-oriented form is conjugate-linear in its input and linear in
its output test vector. Its conjugate is the source pairing `<v,T_K u>`. -/
def kernelRieszFormLinear (K : Lp ℂ 2 (μ.prod ν)) :
    Lp ℂ 2 ν →ₗ⋆[ℂ] Lp ℂ 2 μ →ₗ[ℂ] ℂ where
  toFun u :=
    { toFun := fun v => inner ℂ K (separatedL2 μ ν v (conjugateL2 ν u))
      map_add' := fun v w => by rw [separatedL2_add_left, inner_add_right]
      map_smul' := fun c v => by
        rw [separatedL2_smul_left, inner_smul_right]
        rfl }
  map_add' u w := by
    apply LinearMap.ext
    intro v
    change inner ℂ K (separatedL2 μ ν v (conjugateL2 ν (u + w))) = _
    rw [map_add, separatedL2_add_right, inner_add_right]
    rfl
  map_smul' c u := by
    apply LinearMap.ext
    intro v
    change inner ℂ K (separatedL2 μ ν v (conjugateL2 ν (c • u))) = _
    rw [(conjugateL2 ν).map_smulₛₗ c u, separatedL2_smul_right, inner_smul_right]
    rfl

/-- Cauchy--Schwarz, applied in the actual product L² space. -/
theorem kernelRieszForm_bound (K : Lp ℂ 2 (μ.prod ν))
    (u : Lp ℂ 2 ν) (v : Lp ℂ 2 μ) :
    ‖kernelRieszFormLinear μ ν K u v‖ ≤ ‖K‖ * ‖u‖ * ‖v‖ := by
  change ‖inner ℂ K (separatedL2 μ ν v (conjugateL2 ν u))‖ ≤ _
  calc
    _ ≤ ‖K‖ * ‖separatedL2 μ ν v (conjugateL2 ν u)‖ := norm_inner_le_norm _ _
    _ = ‖K‖ * ‖u‖ * ‖v‖ := by rw [norm_separatedL2, norm_conjugateL2]; ring

/-- The literal kernel form is bounded, without an assumed kernel bound. -/
def kernelRieszForm (K : Lp ℂ 2 (μ.prod ν)) :
    Lp ℂ 2 ν →L⋆[ℂ] Lp ℂ 2 μ →L[ℂ] ℂ :=
  (kernelRieszFormLinear μ ν K).mkContinuous₂ ‖K‖ (kernelRieszForm_bound μ ν K)

@[simp] theorem kernelRieszForm_apply (K : Lp ℂ 2 (μ.prod ν))
    (u : Lp ℂ 2 ν) (v : Lp ℂ 2 μ) :
    kernelRieszForm μ ν K u v = inner ℂ K (separatedL2 μ ν v (conjugateL2 ν u)) := rfl

/-- Riesz turns the conjugate-linear form into the actual complex-linear
integral operator. The two conjugate-linear maps compose to a linear map. -/
def integralKernelOperator (K : Lp ℂ 2 (μ.prod ν)) : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ :=
  (InnerProductSpace.toDual ℂ (Lp ℂ 2 μ)).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (kernelRieszForm μ ν K)

/-- The first defining Riesz equality, in the orientation of `toDual`. -/
theorem integralKernelOperator_inner_left (K : Lp ℂ 2 (μ.prod ν))
    (u : Lp ℂ 2 ν) (v : Lp ℂ 2 μ) :
    inner ℂ (integralKernelOperator μ ν K u) v =
      inner ℂ K (separatedL2 μ ν v (conjugateL2 ν u)) :=
  InnerProductSpace.toDual_symm_apply

/-- The source convention places the test vector in the first entry. -/
theorem inner_integralKernelOperator (K : Lp ℂ 2 (μ.prod ν))
    (u : Lp ℂ 2 ν) (v : Lp ℂ 2 μ) :
    inner ℂ v (integralKernelOperator μ ν K u) =
      inner ℂ (separatedL2 μ ν v (conjugateL2 ν u)) K := by
  rw [← inner_conj_symm v, integralKernelOperator_inner_left, inner_conj_symm]

/-- The actual Cauchy--Schwarz bound for every input vector. -/
theorem norm_integralKernelOperator_apply_le (K : Lp ℂ 2 (μ.prod ν)) (u : Lp ℂ 2 ν) :
    ‖integralKernelOperator μ ν K u‖ ≤ ‖K‖ * ‖u‖ := by
  change ‖(InnerProductSpace.toDual ℂ (Lp ℂ 2 μ)).symm (kernelRieszForm μ ν K u)‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro v
  exact kernelRieszForm_bound μ ν K u v

/-- Operator norm is bounded by the genuine L²-kernel norm. -/
theorem norm_integralKernelOperator_le (K : Lp ℂ 2 (μ.prod ν)) :
    ‖integralKernelOperator μ ν K‖ ≤ ‖K‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  exact norm_integralKernelOperator_apply_le μ ν K

/-- The source integrand, with no conjugation on the input vector. -/
def kernelPairingIntegrand (K : Lp ℂ 2 (μ.prod ν))
    (u : Lp ℂ 2 ν) (v : Lp ℂ 2 μ) (z : X × Y) : ℂ :=
  conj (v z.1) * K z * u z.2

/-- Quotient representatives enter the pairing only through an AE equality. -/
theorem kernelPairingIntegrand_ae (K : Lp ℂ 2 (μ.prod ν))
    (u : Lp ℂ 2 ν) (v : Lp ℂ 2 μ) :
    (fun z => inner ℂ (separatedL2 μ ν v (conjugateL2 ν u) z) (K z)) =ᵐ[μ.prod ν]
      kernelPairingIntegrand μ ν K u v := by
  have hu := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae_eq_comp
    (conjugateL2_coeFn ν u)
  filter_upwards [separatedL2_coeFn μ ν v (conjugateL2 ν u), hu] with z hs hu
  simp only [Function.comp_apply] at hu
  rw [hs, hu]
  simp only [RCLike.inner_apply, map_mul, starRingEnd_self_apply, kernelPairingIntegrand]
  ring

/-- Integrability is established before any product-integral action identity. -/
theorem integrable_kernelPairingIntegrand (K : Lp ℂ 2 (μ.prod ν))
    (u : Lp ℂ 2 ν) (v : Lp ℂ 2 μ) :
    Integrable (kernelPairingIntegrand μ ν K u v) (μ.prod ν) :=
  (L2.integrable_inner (separatedL2 μ ν v (conjugateL2 ν u)) K).congr
    (kernelPairingIntegrand_ae μ ν K u v)

/-- Exact literal integral-kernel pairing; the test variable is conjugated,
whereas the input variable is not, as required by the source convention. -/
theorem inner_integralKernelOperator_eq_integral (K : Lp ℂ 2 (μ.prod ν))
    (u : Lp ℂ 2 ν) (v : Lp ℂ 2 μ) :
    inner ℂ v (integralKernelOperator μ ν K u) =
      ∫ z, conj (v z.1) * K z * u z.2 ∂μ.prod ν := by
  have hi := integrable_kernelPairingIntegrand μ ν K u v
  rw [inner_integralKernelOperator, L2.inner_def]
  exact integral_congr_ae (kernelPairingIntegrand_ae μ ν K u v)

end KernelOperator

section TransferOperator
variable {L : ℝ} (hL : 0 ≤ L)

/-- The literal separately symmetrized transfer kernel, including its separately
specified scalar degree zero, on the physical centered interval. -/
def transferCoefficientKernelL2 (ζ : ℂ) (r : ℕ) : Lp ℂ 2 (transferKernelMeasure L r) :=
  symmetrizeKernelL2 (ι := Fin r) (κ := Fin r) (transferIntervalMeasure L)
    (transferCoefficientRawKernelL2 hL ζ r)

/-- Actual source coefficient on the full symmetric interval sector. Its
projection is the genuine orthogonal permutation average. -/
def transferCoefficientIntervalOperator (ζ : ℂ) (r : ℕ) :
    SymmetricSector (transferIntervalMeasure L) r →L[ℂ]
      SymmetricSector (transferIntervalMeasure L) r :=
  symmetricSectorProjection (transferIntervalMeasure L) r ∘L
    integralKernelOperator (transferCoordinateMeasure L r) (transferCoordinateMeasure L r)
      (transferCoefficientKernelL2 hL ζ r) ∘L
    (symmetricSectorInclusion (transferIntervalMeasure L) r).toContinuousLinearMap

/-- An honest first coefficient bound; the sharp simplex factorial estimate and
Hilbert--Schmidt identity are not assumed or claimed here. -/
theorem norm_transferCoefficientIntervalOperator_le_kernel (ζ : ℂ) (r : ℕ) :
    ‖transferCoefficientIntervalOperator hL ζ r‖ ≤ ‖transferCoefficientKernelL2 hL ζ r‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro u
  calc
    _ ≤ ‖integralKernelOperator (transferCoordinateMeasure L r) (transferCoordinateMeasure L r)
        (transferCoefficientKernelL2 hL ζ r) (u : ProductL2 (transferIntervalMeasure L) (Fin r))‖ :=
      norm_symmetricSectorProjection_apply_le _ _ _
    _ ≤ ‖transferCoefficientKernelL2 hL ζ r‖ * ‖u‖ :=
      norm_integralKernelOperator_apply_le _ _ _ _

/-- Separate input/output averaging cannot enlarge the actual raw-kernel bound. -/
theorem norm_transferCoefficientIntervalOperator_le_rawKernel (ζ : ℂ) (r : ℕ) :
    ‖transferCoefficientIntervalOperator hL ζ r‖ ≤ ‖transferCoefficientRawKernelL2 hL ζ r‖ :=
  (norm_transferCoefficientIntervalOperator_le_kernel hL ζ r).trans
    (norm_symmetrizeKernelL2_apply_le _ _)

end TransferOperator
end LiebLiniger.FixedPeriod.Quantum
