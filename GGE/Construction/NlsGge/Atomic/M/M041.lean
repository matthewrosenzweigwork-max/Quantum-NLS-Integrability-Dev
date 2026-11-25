import Mathlib
import NlsGge.ThirdConsultation.M.M053Host
import NlsGge.ThirdConsultation.M.M041Bridge
import NlsGge.GK38.MolnarInverseBase
import NlsGge.GK38.ActionRealScalar

                                                                                                                   
                                                                                                                  
                                                                                                                 
                                                                                                            
                                                                                                                    
                                                                                                       
                                                                                                       
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ENNReal
open NlsGge.Pilot NlsGge.SpectralFoundations

namespace NlsGge.ThirdConsultation.M

theorem energy_action_lower_bound (u : SobolevR 1) :
    actionWeightedSumENNReal 1 (physicalOfSobolev u) ≠ ⊤ ∧
    Summable (fun n : ℤ => (2 * (n : ℝ) * Real.pi) ^ 2 *
      action (physicalOfSobolev u) n) ∧
    signedCharge 1 u - 2 * massCharge (physicalOfSobolev u) ^ 2 ≤
      ∑' n : ℤ, (2 * (n : ℝ) * Real.pi) ^ 2 *
        action (physicalOfSobolev u) n := by
  have hcar := NlsGge.ThirdConsultation.M041B.carrier_eq u
  obtain ⟨hsum, hint, hid⟩ := NlsGge.GK38.MolnarBounds38.molnar_cubic_trace38
    (ordinarySobolevCoordinates 1 u)
  rw [hcar] at hsum hint hid
  have hsob : SobolevSquareSummable 1 (physicalFourier (physicalOfSobolev u)) := by
    rw [← hcar]
    simpa only [Nat.cast_one] using sobolevToL2_38_sobolev 1 (ordinarySobolevCoordinates 1 u)
  have hpair := NlsGge.GK38.MolnarBounds38.molnar_inverse_base_pair38 (physicalOfSobolev u) hsob
  have hw : (fun n : ℤ => (2 * (n : ℝ) * Real.pi) ^ 2 * action (physicalOfSobolev u) n) =
      fun n : ℤ => (2 * Real.pi * (n : ℝ)) ^ 2 * actualGapActionAllE02_38 (physicalOfSobolev u) n := by
    funext n
    simp only [action]
    ring
  refine ⟨?_, ?_, ?_⟩
  · -- the weighted ENNReal action sum is finite
    unfold actionWeightedSumENNReal
    refine NlsGge.ThirdConsultation.M041B.ennreal_tsum_ne_top
      (fun n => mul_nonneg (sq_nonneg _) (NlsGge.GK38.actionNonnegative38 _ n)) ?_
    refine hpair.2.1.congr ?_
    intro n
    simp only [molnarWeight, action, pow_one]
  · rw [hw]
    exact hsum
  · rw [hw, NlsGge.ThirdConsultation.M041B.signedCharge_eq_chargeSobolev u, massCharge, hid]
    have hv : 0 ≤ ∫ x : ℝ, actualGapHeightE02_38 (physicalOfSobolev u) x ^ 3 :=
      integral_nonneg (fun x => pow_nonneg (actualGapHeightE02_38_nonneg _ x) 3)
    exact NlsGge.ThirdConsultation.M041B.sub_nonneg_mul_le _ _ _ (by positivity) hv

end NlsGge.ThirdConsultation.M
