import NlsGge.GK38.EigenvalueCompactnessRealKernel

/-! # S7: nonscalar eigenspaces and phase-ratio invariance -/
set_option autoImplicit false
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem real_eigenvectors_wedge_or_scalar38 (M : Matrix (Fin 2) (Fin 2) ℂ) (σ : ℂ)
    (a b : ℂ) (ha : M.mulVec (realInitial38 a) = σ • realInitial38 a)
    (hb : M.mulVec (realInitial38 b) = σ • realInitial38 b) :
    a * star b - b * star a = 0 ∨ M = σ • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  by_cases hw : a * star b - b * star a = 0
  · exact Or.inl hw
  right
  have ha0 := congrFun ha 0
  have ha1 := congrFun ha 1
  have hb0 := congrFun hb 0
  have hb1 := congrFun hb 1
  simp only [realInitial38, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Pi.smul_apply, smul_eq_mul] at ha0 ha1 hb0 hb1
  have h00 : (M 0 0 - σ) * (a * star b - b * star a) = 0 := by
    linear_combination star b * ha0 - star a * hb0
  have h01 : M 0 1 * (a * star b - b * star a) = 0 := by
    linear_combination a * hb0 - b * ha0
  have h10 : M 1 0 * (a * star b - b * star a) = 0 := by
    linear_combination star b * ha1 - star a * hb1
  have h11 : (M 1 1 - σ) * (a * star b - b * star a) = 0 := by
    linear_combination a * hb1 - b * ha1
  have h00' := sub_eq_zero.mp ((mul_eq_zero.mp h00).resolve_right hw)
  have h01' := (mul_eq_zero.mp h01).resolve_right hw
  have h10' := (mul_eq_zero.mp h10).resolve_right hw
  have h11' := sub_eq_zero.mp ((mul_eq_zero.mp h11).resolve_right hw)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply, Matrix.one_apply, h00', h01', h10', h11']

theorem real_matrix_state_ratio38 (M : Matrix (Fin 2) (Fin 2) ℂ) (a b : ℂ)
    (hw : a * star b - b * star a = 0)
    (ha : (M.mulVec (realInitial38 a)) 0 ≠ 0)
    (hb : (M.mulVec (realInitial38 b)) 0 ≠ 0) :
    (M.mulVec (realInitial38 a)) 1 / (M.mulVec (realInitial38 a)) 0 =
      (M.mulVec (realInitial38 b)) 1 / (M.mulVec (realInitial38 b)) 0 := by
  apply (div_eq_div_iff ha hb).mpr
  simp only [realInitial38, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination (M 0 1 * M 1 0 - M 0 0 * M 1 1) * hw

end
end NlsGge.GK38
