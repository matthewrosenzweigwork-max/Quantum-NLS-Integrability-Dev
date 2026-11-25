import NlsGge.Spectral.ActualPhysicalL2ZsDysonDeterminantOneV3
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Matrix
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

private theorem det_sub_identity_fin_two_of_det_one
    (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.det = 1) :
    (M - 1).det = 2 - M.trace := by
  simp only [Matrix.det_fin_two] at hM
  simp [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.sub_apply, Matrix.one_apply]
  linear_combination hM

private theorem det_add_identity_fin_two_of_det_one
    (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.det = 1) :
    (M + 1).det = 2 + M.trace := by
  simp only [Matrix.det_fin_two] at hM
  simp [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.add_apply, Matrix.one_apply]
  linear_combination hM

/-- A nonzero fixed endpoint vector for the actual rough-L² fundamental
matrix is equivalent to full endpoint trace two. This is a matrix boundary
criterion; identification with the full operator's Sobolev eigenfunctions
and labeled spectrum remains a separate obligation. -/
theorem actualPhysicalL2ZsDysonTsum_fixed_vector_iff_trace_two
    (u : PhysicalL2) (z : ℂ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 2) :
    (∃ v : Fin 2 → ℂ, v ≠ 0 ∧
      actualComplexZsDysonTsum
        (fun x => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (x : SpectralCircle))
        z t *ᵥ v = v) ↔
      Matrix.trace (actualComplexZsDysonTsum
        (fun x => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (x : SpectralCircle))
        z t) = 2 := by
  let M := actualComplexZsDysonTsum
    (fun x => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (x : SpectralCircle)) z t
  have hdet : M.det = 1 := actualPhysicalL2ZsDysonTsum_det_one u z t ht
  have hker : (∃ v : Fin 2 → ℂ, v ≠ 0 ∧ M *ᵥ v = v) ↔
      ∃ v : Fin 2 → ℂ, v ≠ 0 ∧ (M - 1) *ᵥ v = 0 := by
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]
  change (∃ v : Fin 2 → ℂ, v ≠ 0 ∧ M *ᵥ v = v) ↔ M.trace = 2
  rw [hker, Matrix.exists_mulVec_eq_zero_iff,
    det_sub_identity_fin_two_of_det_one M hdet]
  exact sub_eq_zero.trans eq_comm

/-- The corresponding negative endpoint vector criterion uses full trace
minus two. In particular it applies at the unit-period endpoint without
silently identifying the unit and doubled monodromy traces. -/
theorem actualPhysicalL2ZsDysonTsum_negative_vector_iff_trace_neg_two
    (u : PhysicalL2) (z : ℂ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 2) :
    (∃ v : Fin 2 → ℂ, v ≠ 0 ∧
      actualComplexZsDysonTsum
        (fun x => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (x : SpectralCircle))
        z t *ᵥ v = -v) ↔
      Matrix.trace (actualComplexZsDysonTsum
        (fun x => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (x : SpectralCircle))
        z t) = -2 := by
  let M := actualComplexZsDysonTsum
    (fun x => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (x : SpectralCircle)) z t
  have hdet : M.det = 1 := actualPhysicalL2ZsDysonTsum_det_one u z t ht
  have hker : (∃ v : Fin 2 → ℂ, v ≠ 0 ∧ M *ᵥ v = -v) ↔
      ∃ v : Fin 2 → ℂ, v ≠ 0 ∧ (M + 1) *ᵥ v = 0 := by
    simp only [Matrix.add_mulVec, Matrix.one_mulVec, add_eq_zero_iff_eq_neg]
  change (∃ v : Fin 2 → ℂ, v ≠ 0 ∧ M *ᵥ v = -v) ↔ M.trace = -2
  rw [hker, Matrix.exists_mulVec_eq_zero_iff,
    det_add_identity_fin_two_of_det_one M hdet]
  constructor <;> intro h <;> linear_combination h

end NlsGge.SpectralFoundations
end
