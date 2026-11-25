import LiebLiniger.FixedPeriod.Quantum.IntegralKernelAction
import LiebLiniger.FixedPeriod.Quantum.CircleIntervalSectors

/-! Same-witness physical coefficient, transported along the actual mass-L
circle/centered-interval symmetric-sector unitary. No Hilbert--Schmidt or sharp
factorial estimate is assumed. Author candidate; root lane B validates. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace ComplexConjugate
namespace LiebLiniger.FixedPeriod.Quantum

section IsometricConjugation
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Conjugation of a genuine bounded operator by an actual Hilbert isometry. -/
def isometricConjugateOperator (e : E ≃ₗᵢ[ℂ] F) (A : F →L[ℂ] F) : E →L[ℂ] E :=
  e.symm.toLinearIsometry.toContinuousLinearMap ∘L A ∘L
    e.toLinearIsometry.toContinuousLinearMap

@[simp] theorem isometricConjugateOperator_apply (e : E ≃ₗᵢ[ℂ] F) (A : F →L[ℂ] F) (u : E) :
    isometricConjugateOperator e A u = e.symm (A (e u)) := rfl

/-- Actual unitary transport preserves the full operator norm. -/
theorem norm_isometricConjugateOperator (e : E ≃ₗᵢ[ℂ] F) (A : F →L[ℂ] F) :
    ‖isometricConjugateOperator e A‖ = ‖A‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro u
    change ‖e.symm (A (e u))‖ ≤ ‖A‖ * ‖u‖
    rw [LinearIsometryEquiv.norm_map]
    calc
      _ ≤ ‖A‖ * ‖e u‖ := A.le_opNorm (e u)
      _ = _ := by rw [LinearIsometryEquiv.norm_map]
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro v
    have h := (isometricConjugateOperator e A).le_opNorm (e.symm v)
    change ‖e.symm (A (e (e.symm v)))‖ ≤ ‖isometricConjugateOperator e A‖ * ‖e.symm v‖ at h
    simpa only [LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.norm_map] using h

end IsometricConjugation

section HilbertPairing
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem inner_isometricConjugateOperator (e : E ≃ₗᵢ[ℂ] F) (A : F →L[ℂ] F) (u v : E) :
    inner ℂ v (isometricConjugateOperator e A u) = inner ℂ (e v) (A (e u)) := by
  rw [← e.inner_map_map v (isometricConjugateOperator e A u)]
  change inner ℂ (e v) (e (e.symm (A (e u)))) = _
  rw [LinearIsometryEquiv.apply_symm_apply]

end HilbertPairing

section PhysicalCoefficient
variable (L : ℝ) [Fact (0 < L)]

/-- The actual physical source coefficient on `Sym^r L²(T_L)`, with the same
literal separately symmetrized KA/KD kernel on the centered interval. -/
def transferCoefficientOperator (ζ : ℂ) (r : ℕ) :
    SymmetricSector (volume : Measure (AddCircle L)) r →L[ℂ]
      SymmetricSector (volume : Measure (AddCircle L)) r :=
  isometricConjugateOperator (circleIntervalSymmetricSectorEquiv L r)
    (transferCoefficientIntervalOperator (Fact.out : 0 < L).le ζ r)

/-- The physical torus/interval identification introduces no norm or measure
scale factor. In particular, its interval measure retains total mass L. -/
theorem norm_transferCoefficientOperator_eq_interval (ζ : ℂ) (r : ℕ) :
    ‖transferCoefficientOperator L ζ r‖ =
      ‖transferCoefficientIntervalOperator (Fact.out : 0 < L).le ζ r‖ :=
  norm_isometricConjugateOperator _ _

/-- First concrete physical estimate from Cauchy--Schwarz and the actual
orthogonal input/output averages. Sharp factorial/HS estimates remain later. -/
theorem norm_transferCoefficientOperator_le_kernel (ζ : ℂ) (r : ℕ) :
    ‖transferCoefficientOperator L ζ r‖ ≤
      ‖transferCoefficientKernelL2 (Fact.out : 0 < L).le ζ r‖ := by
  rw [norm_transferCoefficientOperator_eq_interval]
  exact norm_transferCoefficientIntervalOperator_le_kernel _ ζ r

theorem norm_transferCoefficientOperator_le_rawKernel (ζ : ℂ) (r : ℕ) :
    ‖transferCoefficientOperator L ζ r‖ ≤
      ‖transferCoefficientRawKernelL2 (Fact.out : 0 < L).le ζ r‖ := by
  rw [norm_transferCoefficientOperator_eq_interval]
  exact norm_transferCoefficientIntervalOperator_le_rawKernel _ ζ r

/-- Exact physical symmetric-sector kernel action in weak form. The SAME
constructed operator is transported by the actual symmetric-sector unitary;
no abstract coefficient or independently chosen realization is introduced. -/
theorem transferCoefficientOperator_pairing (ζ : ℂ) (r : ℕ)
    (u v : SymmetricSector (volume : Measure (AddCircle L)) r) :
    inner ℂ v (transferCoefficientOperator L ζ r u) =
      ∫ z,
        conj (((circleIntervalSymmetricSectorEquiv L r v :
          SymmetricSector (transferIntervalMeasure L) r) :
            ProductL2 (transferIntervalMeasure L) (Fin r)) z.1) *
        transferCoefficientKernelL2 (Fact.out : 0 < L).le ζ r z *
        (((circleIntervalSymmetricSectorEquiv L r u :
          SymmetricSector (transferIntervalMeasure L) r) :
            ProductL2 (transferIntervalMeasure L) (Fin r)) z.2)
        ∂transferKernelMeasure L r := by
  change inner ℂ v (isometricConjugateOperator (circleIntervalSymmetricSectorEquiv L r)
    (transferCoefficientIntervalOperator (Fact.out : 0 < L).le ζ r) u) = _
  rw [inner_isometricConjugateOperator]
  exact transferCoefficientIntervalOperator_pairing _ ζ r _ _

end PhysicalCoefficient
end LiebLiniger.FixedPeriod.Quantum
