                                                                                                                                         
                                                                                                                                      
import Mathlib
import NlsGge.Schur.FiniteLogDetEstimate38V1
import NlsGge.Atomic.S.S037

                                                                                                              
                                                                                                                   
                                                                                                  
                                                                                                                          
                                                                                               

set_option autoImplicit false
open scoped BigOperators Matrix.Norms.L2Operator

namespace NlsGge.ThirdConsultation.S
noncomputable section

theorem real_logdet_near_identity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (hB : operatorNorm B ≤ 1 / 2) :
    0 < Matrix.det (1 + B) ∧
      |Real.log (Matrix.det (1 + B)) - Matrix.trace B| ≤ 1 * matrixHSNorm B ^ 2 := by
  have hOp : NlsGge.Schur.OpBound B (1 / 2) := by
    intro v
    have h := NlsGge.Schur.opBound_of_norm B v
    have he := NlsGge.Schur.eN_nonneg v
    have hB' : ‖B‖ ≤ 1 / 2 := hB
    exact h.trans (mul_le_mul_of_nonneg_right hB' he)
  have hpos := NlsGge.Schur.det_pos_of_opBound B hOp (t := 1) zero_le_one le_rfl
  have hlog := NlsGge.Schur.logdet_abs_sub_trace_le_HS B hOp
  have hsq : matrixHSNorm B ^ 2 = ∑ i, ∑ j, (B i j) ^ 2 := by
    unfold matrixHSNorm
    exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)
  refine ⟨by simpa using hpos, ?_⟩
  rw [one_mul, hsq]
  simpa using hlog

end
end NlsGge.ThirdConsultation.S
