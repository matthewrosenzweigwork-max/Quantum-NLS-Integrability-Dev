import Mathlib
import NlsGge.Schur.FreeResolventSquareNeumannAfterScalarPrerequisites

                                                                                           
                                                                                               
                                                                                               
                                                                                 
                                                                                               
                                                                                                  
                                                                         
set_option autoImplicit false
noncomputable section

namespace NlsGge.ThirdConsultation.S

theorem inverse_one_sub_of_square_small
    {B : Type*} [NormedRing B] [CompleteSpace B]
    (A : B) (hA : ‖A ^ 2‖ < 1) :
    IsUnit (1 - A) ∧
      Ring.inverse (1 - A) =
        (1 + A) * Ring.inverse (1 - A ^ 2) := by
  have hw : IsUnit (1 - A ^ 2) := IsUnit.one_sub_of_norm_lt_one hA
  have hfac : (1 - A) * (1 + A) = 1 - A ^ 2 := by noncomm_ring
  have hfac' : (1 + A) * (1 - A) = 1 - A ^ 2 := by noncomm_ring
  have hcomm : Commute (1 - A) (1 + A) := by
    show (1 - A) * (1 + A) = (1 + A) * (1 - A)
    exact hfac.trans hfac'.symm
  have hprod : IsUnit ((1 - A) * (1 + A)) := by
    rw [hfac]; exact hw
  obtain ⟨h1, _⟩ := hcomm.isUnit_mul_iff.1 hprod
  refine ⟨h1, ?_⟩
  have hright : (1 - A) * ((1 + A) * Ring.inverse (1 - A ^ 2)) = 1 := by
    rw [← mul_assoc, hfac, Ring.mul_inverse_cancel _ hw]
  calc Ring.inverse (1 - A)
      = Ring.inverse (1 - A) * ((1 - A) * ((1 + A) * Ring.inverse (1 - A ^ 2))) := by
        rw [hright, mul_one]
    _ = (Ring.inverse (1 - A) * (1 - A)) * ((1 + A) * Ring.inverse (1 - A ^ 2)) := by
        rw [mul_assoc]
    _ = (1 + A) * Ring.inverse (1 - A ^ 2) := by
        rw [Ring.inverse_mul_cancel _ h1, one_mul]

theorem inverse_one_sub_of_square_small_twoSided
    {B : Type*} [NormedRing B] [CompleteSpace B]
    (A : B) (hA : ‖A ^ 2‖ < 1) :
    IsUnit (1 - A ^ 2) ∧ IsUnit (1 - A) ∧
      Ring.inverse (1 - A) * (1 - A) = 1 ∧
      (1 - A) * Ring.inverse (1 - A) = 1 ∧
      Ring.inverse (1 - A) =
        (1 + A) * Ring.inverse (1 - A ^ 2) ∧
      Ring.inverse (1 - A) =
        Ring.inverse (1 - A ^ 2) * (1 + A) := by
  obtain ⟨h1, hinv⟩ := inverse_one_sub_of_square_small A hA
  have hw : IsUnit (1 - A ^ 2) := IsUnit.one_sub_of_norm_lt_one hA
  have hfac' : (1 + A) * (1 - A) = 1 - A ^ 2 := by noncomm_ring
  have hleft : Ring.inverse (1 - A ^ 2) * (1 + A) * (1 - A) = 1 := by
    rw [mul_assoc, hfac', Ring.inverse_mul_cancel _ hw]
  have hleft' : Ring.inverse (1 - A) = Ring.inverse (1 - A ^ 2) * (1 + A) := by
    calc Ring.inverse (1 - A)
        = (Ring.inverse (1 - A ^ 2) * (1 + A) * (1 - A)) * Ring.inverse (1 - A) := by
          rw [hleft, one_mul]
      _ = Ring.inverse (1 - A ^ 2) * (1 + A) * ((1 - A) * Ring.inverse (1 - A)) := by
          rw [mul_assoc]
      _ = Ring.inverse (1 - A ^ 2) * (1 + A) := by
          rw [Ring.mul_inverse_cancel _ h1, mul_one]
  exact ⟨hw, h1, Ring.inverse_mul_cancel _ h1, Ring.mul_inverse_cancel _ h1, hinv, hleft'⟩

theorem inverse_one_sub_of_square_le_half_norm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] [Nontrivial E]
    (A : E →L[ℂ] E) (B : ℝ) (hB : 0 ≤ B)
    (hA : ‖A‖ ≤ B) (hA2 : ‖A * A‖ ≤ (1 / 2 : ℝ)) :
    ‖Ring.inverse (1 - A)‖ ≤ 2 * (1 + B) := by
  have hsq : ‖A ^ 2‖ < 1 := by
    rw [pow_two]; linarith
  have h1 : IsUnit (1 - A) := (inverse_one_sub_of_square_small A hsq).1
  obtain ⟨S, hSl, hSr, hS⟩ :=
    NlsGge.Schur.continuousLinearMap_square_neumann_inverse A B hB hA hA2
  have hS_eq : S = Ring.inverse (1 - A) := by
    calc S = S * ((1 - A) * Ring.inverse (1 - A)) := by
          rw [Ring.mul_inverse_cancel _ h1, mul_one]
      _ = (S * (1 - A)) * Ring.inverse (1 - A) := by rw [mul_assoc]
      _ = Ring.inverse (1 - A) := by rw [hSl, one_mul]
  rw [← hS_eq]
  exact hS

end NlsGge.ThirdConsultation.S
