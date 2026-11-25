import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS006Host
import NlsGge.ThirdConsultation.KSPS.KSPS005Support
import NlsGge.ThirdConsultation.KSPS.IBP002Support

                                                                                                                    
                                                                                                                             
                                                                                                                         
                                                                                                        
set_option autoImplicit false
noncomputable section
open NlsGge.ThirdConsultation.KSPS
open scoped Matrix.Norms.L2Operator

namespace NlsGge.ThirdConsultation.KSPS006Support

theorem adj_add (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    KSPSVolterra.adjugate2 (A + B) = KSPSVolterra.adjugate2 A + KSPSVolterra.adjugate2 B := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [KSPSVolterra.adjugate2] <;> ring

theorem adj_sub (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    KSPSVolterra.adjugate2 (A - B) = KSPSVolterra.adjugate2 A - KSPSVolterra.adjugate2 B := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [KSPSVolterra.adjugate2] <;> ring

theorem adj_smul (c : ℂ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    KSPSVolterra.adjugate2 (c • A) = c • KSPSVolterra.adjugate2 A := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [KSPSVolterra.adjugate2]

theorem adj_free (x : ℝ) (lam : ℂ) :
    KSPSVolterra.adjugate2 (freePropagator x lam) = freePropagator (-x) lam := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [KSPSVolterra.adjugate2, freePropagator]

theorem adj_term1 (φ : SobolevC 1) (x : ℝ) (lam : ℂ) :
    KSPSVolterra.adjugate2 (volterraTerm 1 x lam φ) = -volterraTerm 1 x lam φ := by
  have h00 := NlsGge.ThirdConsultation.KSPS002Support.term1_00 φ x lam
  have h11 := NlsGge.ThirdConsultation.KSPS002Support.term1_11 φ x lam
  ext i j
  fin_cases i <;> fin_cases j <;> simp [KSPSVolterra.adjugate2, h00, h11]

theorem adj_mt (φ : SobolevC 1) (x : ℝ) (lam : ℂ) :
    KSPSVolterra.adjugate2 (freePropagator x lam * KSPSVolterra.R * KSPSVolterra.integratedQuadratic φ x) =
      -(freePropagator (-x) lam * KSPSVolterra.R * KSPSVolterra.integratedQuadratic φ x) := by
  unfold KSPSVolterra.integratedQuadratic
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [KSPSVolterra.adjugate2, freePropagator, KSPSVolterra.R, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem inverseFundamentalRemainder_eq (φ : SobolevC 1) (x : ℝ) (lam : ℂ) :
    inverseFundamentalRemainder φ x lam =
      KSPSVolterra.adjugate2 (fundamentalRemainder φ x lam) := by
  unfold fundamentalRemainder inverseFundamentalRemainder
  rw [adj_sub, adj_sub, adj_sub, adj_smul, adj_free, adj_term1, adj_mt]
  unfold KSPSVolterra.inverseFundamental
  simp only [smul_neg, sub_neg_eq_add]

theorem norm_entry_le_l2 (A : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) : ‖A i j‖ ≤ ‖A‖ := by
  classical
  have h := Matrix.l2_opNorm_mulVec A (EuclideanSpace.single j (1 : ℂ))
  have e1 : ‖EuclideanSpace.single j (1 : ℂ)‖ = 1 := by simp
  have e2 := PiLp.norm_apply_le ((EuclideanSpace.equiv (Fin 2) ℂ).symm
    (Matrix.mulVec A ⇑(EuclideanSpace.single j (1 : ℂ)))) i
  have e3 : ((EuclideanSpace.equiv (Fin 2) ℂ).symm (Matrix.mulVec A ⇑(EuclideanSpace.single j (1 : ℂ)))) i =
      A i j := by
    simp
  rw [e3] at e2
  rw [e1, mul_one] at h
  exact e2.trans h

theorem norm_adjugate2_le_two (A : Matrix (Fin 2) (Fin 2) ℂ) :
    ‖KSPSVolterra.adjugate2 A‖ ≤ 2 * ‖A‖ := by
  refine NlsGge.ThirdConsultation.KSPS005Support.opNorm_le_two _ (fun i j => ?_)
  fin_cases i <;> fin_cases j <;>
    simpa [KSPSVolterra.adjugate2] using norm_entry_le_l2 A _ _

end NlsGge.ThirdConsultation.KSPS006Support
end
