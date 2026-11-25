import Mathlib

                                                                                                                                               
                                                                                                                                         
                                                                                                                                                
                                                                                                                                                     
                                                                                                                        
                                                                                                                                    
set_option autoImplicit false
open Matrix

namespace NlsGge.ThirdConsultation.S
noncomputable section

theorem weighted_real_matrix_similarity {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : Matrix ι ι ℝ} {D : ι → ℝ} (hD : ∀ c, 0 < D c) :
    Matrix.trace (Matrix.diagonal D * B * Matrix.diagonal (D⁻¹)) = Matrix.trace B ∧
    Matrix.det (1 + Matrix.diagonal D * B * Matrix.diagonal (D⁻¹)) = Matrix.det (1 + B) := by
  have h1 : Matrix.diagonal D * Matrix.diagonal (D⁻¹) = (1 : Matrix ι ι ℝ) := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext c
    simp [mul_inv_cancel₀ (hD c).ne']
  have h2 : Matrix.diagonal (D⁻¹) * Matrix.diagonal D = (1 : Matrix ι ι ℝ) := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext c
    simp [inv_mul_cancel₀ (hD c).ne']
  constructor
  · rw [Matrix.trace_mul_comm (Matrix.diagonal D * B), ← Matrix.mul_assoc, h2, Matrix.one_mul]
  · have e : (1 : Matrix ι ι ℝ) + Matrix.diagonal D * B * Matrix.diagonal (D⁻¹) =
        Matrix.diagonal D * (1 + B) * Matrix.diagonal (D⁻¹) := by
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, h1]
    rw [e, Matrix.det_mul, Matrix.det_mul]
    have h3 : Matrix.det (Matrix.diagonal D) * Matrix.det (Matrix.diagonal (D⁻¹)) = 1 := by
      rw [← Matrix.det_mul, h1, Matrix.det_one]
    calc Matrix.det (Matrix.diagonal D) * Matrix.det (1 + B) * Matrix.det (Matrix.diagonal (D⁻¹))
        = (Matrix.det (Matrix.diagonal D) * Matrix.det (Matrix.diagonal (D⁻¹))) * Matrix.det (1 + B) := by ring
      _ = Matrix.det (1 + B) := by rw [h3, one_mul]

end
end NlsGge.ThirdConsultation.S
