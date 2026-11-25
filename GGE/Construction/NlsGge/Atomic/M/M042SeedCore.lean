import Mathlib
import NlsGge.GK38.MolnarInverseBase
import NlsGge.Spectral.ActualActionSumE02_38

                                                                                                     
                                                                                                                 
                                                                                      
                                                                                                          
                                                                                                             
                                                                                                                 
                                                                                                      
                                                                 
                                                                                                                  

set_option autoImplicit false
open MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.ThirdConsultation.M042Seed

theorem reflected_weighted_tsum (v : PhysicalL2) :
    (∑' p : ℤ, (1 + |2 * Real.pi * (p : ℝ)|) ^ 2 * ‖reflectedFourierL2 v p‖ ^ 2) =
      ∑' n : ℤ, (1 + |2 * Real.pi * (n : ℝ)|) ^ 2 * ‖physicalFourier v n‖ ^ 2 := by
  set h : ℤ → ℝ := fun n => (1 + |2 * Real.pi * (n : ℝ)|) ^ 2 * ‖physicalFourier v n‖ ^ 2 with hh
  have e : (fun p : ℤ => (1 + |2 * Real.pi * (p : ℝ)|) ^ 2 * ‖reflectedFourierL2 v p‖ ^ 2) =
      fun p => h ((Equiv.neg ℤ) p) := by
    funext p
    simp only [hh, Equiv.neg_apply, reflectedFourierL2_apply, reflectedFourier, norm_neg,
      Int.cast_neg, mul_neg, abs_neg]
  rw [e, (Equiv.neg ℤ).tsum_eq h]

theorem seed_core (v : PhysicalL2) (hu : SobolevSquareSummable 1 (physicalFourier v)) :
    (1 / 3 : ℝ) * (2 * ∑' p : ℤ, (1 + |2 * Real.pi * (p : ℝ)|) ^ 2 * ‖reflectedFourierL2 v p‖ ^ 2) ≤
      (∑' n : ℤ, ((1 + |2 * Real.pi * (n : ℝ)|) ^ 1) ^ 2 * actualGapActionAllE02_38 v n) +
        (∑' n : ℤ, ((1 + |2 * Real.pi * (n : ℝ)|) ^ 0) ^ 2 * actualGapActionAllE02_38 v n) ^ 2 := by
  obtain ⟨-, -, hineq⟩ := MolnarBounds38.molnar_inverse_base_pair38 v hu
  have hmass := actualGapAction_hasSum_E02_38 v hu
  have hA0 : (∑' n : ℤ, ((1 + |2 * Real.pi * (n : ℝ)|) ^ 0) ^ 2 * actualGapActionAllE02_38 v n) =
      ‖v‖ ^ 2 := by
    simp only [pow_zero, one_pow, one_mul]
    exact hmass.tsum_eq
  have hA1 : (∑' n : ℤ, ((1 + |2 * Real.pi * (n : ℝ)|) ^ 1) ^ 2 * actualGapActionAllE02_38 v n) =
      ∑' n : ℤ, (1 + |2 * Real.pi * (n : ℝ)|) ^ 2 * actualGapActionAllE02_38 v n := by
    simp only [pow_one]
  rw [reflected_weighted_tsum, hA0, hA1]
  linarith

theorem house_le_source_sum (r : ℤ → ℝ) (hr : ∀ p, 0 ≤ r p)
    (hs : Summable (fun p : ℤ => (1 + |2 * Real.pi * (p : ℝ)|) ^ 2 * r p)) :
    (∑' p : ℤ, (1 + (p : ℝ) ^ 2) * r p) ≤
      2 * ∑' p : ℤ, (1 + |2 * Real.pi * (p : ℝ)|) ^ 2 * r p := by
  have hw : ∀ p : ℤ, (1 + (p : ℝ) ^ 2) ≤ (1 + |2 * Real.pi * (p : ℝ)|) ^ 2 := by
    intro p
    have ha : (p : ℝ) ^ 2 ≤ |2 * Real.pi * (p : ℝ)| ^ 2 := by
      rw [sq_abs, mul_pow]
      have h2 : (1 : ℝ) ≤ (2 * Real.pi) ^ 2 := by nlinarith [Real.pi_gt_three]
      nlinarith [sq_nonneg (p : ℝ)]
    nlinarith [abs_nonneg (2 * Real.pi * (p : ℝ))]
  have hle : ∀ p : ℤ, (1 + (p : ℝ) ^ 2) * r p ≤ (1 + |2 * Real.pi * (p : ℝ)|) ^ 2 * r p :=
    fun p => mul_le_mul_of_nonneg_right (hw p) (hr p)
  have hs' : Summable (fun p : ℤ => (1 + (p : ℝ) ^ 2) * r p) :=
    Summable.of_nonneg_of_le (fun p => mul_nonneg (by positivity) (hr p)) hle hs
  have h1 := hs'.tsum_le_tsum hle hs
  have h0 : 0 ≤ ∑' p : ℤ, (1 + |2 * Real.pi * (p : ℝ)|) ^ 2 * r p :=
    tsum_nonneg fun p => mul_nonneg (by positivity) (hr p)
  linarith

end NlsGge.ThirdConsultation.M042Seed
