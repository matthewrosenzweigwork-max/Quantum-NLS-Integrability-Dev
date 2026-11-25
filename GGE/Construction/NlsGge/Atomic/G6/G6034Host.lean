import Mathlib
import NlsGge.Atomic.PhysicalSobolev
import NlsGge.Birkhoff.BirkhoffAPI38
import NlsGge.Sobolev.WeightedHilbert

                                                                                                               
                                                                                                         
                                                                                                            
                                                                                                                    
                                                                                                                   
                                                                                                                        
                                                                                                       
                                                                                                                         
                                                           
                                                                                                               
                                                                                                                                
                                                                                                                      
                                                                      
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common
open scoped ENNReal InnerProductSpace

namespace NlsGge.GKDefinitionDesign
noncomputable section

abbrev WeightedActionSpace := lp (fun _ : ℤ => ℝ) 1

def actionWeight (n : ℤ) : ℝ := sobolevModeWeight (1 : ℝ) n

def actionCoefficient (I : WeightedActionSpace) (n : ℤ) : ℝ := I n / actionWeight n

def weightedActionNorm (I : WeightedActionSpace) : ℝ := ‖I‖

theorem weightedCoordinateActions_mem (z : SobolevCarrier38 ((1 : ℕ) : ℝ)) :
  Memℓp (fun n : ℤ => actionWeight n * ‖carrierCoe38 ((1 : ℕ) : ℝ) z n‖^2) 1 := by
  have hs : HasSum (fun n : ℤ => sobolevModeWeight ((1 : ℕ) : ℝ) n *
      ‖carrierCoe38 ((1 : ℕ) : ℝ) z n‖ ^ 2)
      (‖(show WeightedHilbert (sobolevModeWeight ((1 : ℕ) : ℝ)) from z)‖ ^ 2) :=
    weightedHilbert_hasSum (sobolevModeWeight ((1 : ℕ) : ℝ))
      (show WeightedHilbert (sobolevModeWeight ((1 : ℕ) : ℝ)) from z)
  have hw : ∀ n : ℤ, sobolevModeWeight ((1 : ℕ) : ℝ) n = actionWeight n := by
    intro n
    rw [Nat.cast_one]
    rfl
  refine memℓp_gen ?_
  have hnn : ∀ n : ℤ, 0 ≤ actionWeight n * ‖carrierCoe38 ((1 : ℕ) : ℝ) z n‖ ^ 2 := fun n =>
    mul_nonneg (sobolevModeWeight_pos 1 n).le (sq_nonneg _)
  have he : (fun n : ℤ =>
      ‖actionWeight n * ‖carrierCoe38 ((1 : ℕ) : ℝ) z n‖ ^ 2‖ ^ (1 : ℝ≥0∞).toReal) =
      fun n : ℤ => sobolevModeWeight ((1 : ℕ) : ℝ) n * ‖carrierCoe38 ((1 : ℕ) : ℝ) z n‖ ^ 2 := by
    funext n
    rw [ENNReal.toReal_one, Real.rpow_one, Real.norm_of_nonneg (hnn n), hw n]
  rw [he]
  exact hs.summable

def coordinateActions (z : SobolevCarrier38 ((1 : ℕ) : ℝ)) : WeightedActionSpace :=
  ⟨fun n => actionWeight n * ‖carrierCoe38 ((1 : ℕ) : ℝ) z n‖^2,
    weightedCoordinateActions_mem z⟩

end
end NlsGge.GKDefinitionDesign
