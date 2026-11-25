import NlsGge.Spectral.ActualPhysicalL2ZsEndpointTraceCriterionV2
import NlsGge.Spectral.ActualPhysicalUnitDiscriminantNonrealZeroFree32V1
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Matrix
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-- Exact finite-dimensional characteristic equation, ordinary determinant. -/
theorem det_sub_scalar_identity_fin_two_det_one33
    (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.det = 1) (χ : ℂ) :
    (M - χ • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det = χ^2 - M.trace*χ + 1 := by
  simp only [Matrix.det_fin_two] at hM
  simp [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  linear_combination hM

/-- The actual rough source monodromy has precisely the eigenmultipliers
of its normalized half-trace quadratic. All complex multipliers are retained. -/
theorem actualPhysicalUnit_eigenmultiplier_iff_quadratic33
    (u : PhysicalL2) (z χ : ℂ) :
    (∃ v : Fin 2 → ℂ, v ≠ 0 ∧
      (actualComplexZsDysonTsum
        (fun x => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (x : SpectralCircle))
        z 1).mulVec v = χ • v) ↔
      χ^2 - 2*actualPhysicalUnitHalfTrace32 u z*χ + 1 = 0 := by
  let M := actualComplexZsDysonTsum
    (fun x => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (x : SpectralCircle)) z 1
  have hdet : M.det = 1 := actualPhysicalL2ZsDysonTsum_det_one u z 1 (by norm_num)
  have hker : (∃ v : Fin 2 → ℂ, v ≠ 0 ∧ M.mulVec v = χ • v) ↔
      ∃ v : Fin 2 → ℂ, v ≠ 0 ∧ (M-χ • (1 : Matrix (Fin 2) (Fin 2) ℂ)).mulVec v = 0 := by
    simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero]
  have htrace : M.trace = 2*actualPhysicalUnitHalfTrace32 u z := by
    dsimp [M, actualPhysicalUnitHalfTrace32]
    ring
  change (∃ v : Fin 2 → ℂ, v ≠ 0 ∧ M.mulVec v = χ • v) ↔ _
  rw [hker, Matrix.exists_mulVec_eq_zero_iff,
    det_sub_scalar_identity_fin_two_det_one33 M hdet χ, htrace]

/-- Each actual half-trace square-root branch gives a genuine monodromy
multiplier, not merely a formal scalar quadratic root. -/
theorem actualPhysicalUnit_squareRoot_gives_eigenmultiplier33
    (u : PhysicalL2) (z s : ℂ)
    (hs : s^2 = actualPhysicalUnitHalfTrace32 u z ^2 - 1) :
    ∃ v : Fin 2 → ℂ, v ≠ 0 ∧
      (actualComplexZsDysonTsum
        (fun x => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (x : SpectralCircle))
        z 1).mulVec v = (actualPhysicalUnitHalfTrace32 u z+s) • v := by
  apply (actualPhysicalUnit_eigenmultiplier_iff_quadratic33 u z
    (actualPhysicalUnitHalfTrace32 u z+s)).mpr
  linear_combination hs

end NlsGge.SpectralFoundations
end
