import NlsGge.Spectral.FreeZakharovShabatFundamentalComplexV4
import Mathlib.Tactic
set_option autoImplicit false
set_option maxRecDepth 2048
noncomputable section
open scoped Matrix
namespace NlsGge.SpectralFoundations
/-- Exact scalar coefficient conjugacy; no representative assumption. -/
theorem actualPhysicalSignFlipScalarCoefficientMinimum31
    (a z : ℂ) (v : Fin 2 → ℂ) :
    zsCoefficientComplex (fun _ => -a) z 0 *ᵥ ![v 0, -v 1] =
      ![(zsCoefficientComplex (fun _ => a) z 0 *ᵥ v) 0,
        -(zsCoefficientComplex (fun _ => a) z 0 *ᵥ v) 1] := by
  funext i
  fin_cases i <;>
    simp only [zsCoefficientComplex, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_zero', Matrix.cons_val_succ', star_neg] <;> ring
end NlsGge.SpectralFoundations
end
