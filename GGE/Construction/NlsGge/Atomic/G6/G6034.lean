import Mathlib
import NlsGge.Atomic.G6.G6034Host
import NlsGge.Analysis.PhysicalH1Bounds
import NlsGge.GK38.Defs

                                                                                                                  
                                                                                                             
                                                                                                                   
                                                                       
                                                                                                               
                                                                                                                                   
                                                                        
                                                                                                                      
                                                                                                                     
                                                                                                                        
                                                                                                            
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Common
open scoped ENNReal InnerProductSpace

namespace NlsGge.GKDefinitionDesign
namespace G6034Aux
noncomputable section

theorem actionWeight_pos (n : ℤ) : 0 < actionWeight n := sobolevModeWeight_pos 1 n

theorem actionWeight_eq (n : ℤ) : actionWeight n = 1 + (n : ℝ) ^ 2 := by
  have h := NlsGge.Analysis.japaneseBracket_h1_weight n
  simpa [actionWeight, sobolevModeWeight] using h

theorem coordinateActions_apply (z : SobolevCarrier38 ((1 : ℕ) : ℝ)) (n : ℤ) :
    coordinateActions z n = actionWeight n * ‖carrierCoe38 ((1 : ℕ) : ℝ) z n‖ ^ 2 := rfl

theorem hasSum_norm_one (I : WeightedActionSpace) :
    HasSum (fun n : ℤ => ‖I n‖) ‖I‖ := by
  have h := lp.hasSum_norm (p := (1 : ℝ≥0∞)) (by norm_num) I
  simpa only [ENNReal.toReal_one, Real.rpow_one] using h

theorem hasSum_coordinateActions (z : SobolevCarrier38 ((1 : ℕ) : ℝ)) :
    HasSum (fun n : ℤ => coordinateActions z n) (‖z‖ ^ 2) := by
  have hs : HasSum (fun n : ℤ => sobolevModeWeight ((1 : ℕ) : ℝ) n *
      ‖carrierCoe38 ((1 : ℕ) : ℝ) z n‖ ^ 2)
      (‖(show WeightedHilbert (sobolevModeWeight ((1 : ℕ) : ℝ)) from z)‖ ^ 2) :=
    weightedHilbert_hasSum (sobolevModeWeight ((1 : ℕ) : ℝ))
      (show WeightedHilbert (sobolevModeWeight ((1 : ℕ) : ℝ)) from z)
  have he : (fun n : ℤ => coordinateActions z n) = fun n : ℤ => sobolevModeWeight ((1 : ℕ) : ℝ) n *
      ‖carrierCoe38 ((1 : ℕ) : ℝ) z n‖ ^ 2 := by
    funext n
    have hw : sobolevModeWeight ((1 : ℕ) : ℝ) n = actionWeight n := by
      rw [Nat.cast_one]
      rfl
    rw [coordinateActions_apply, hw]
  rw [he]
  exact hs

end
end G6034Aux

noncomputable section

theorem G6034 (z : SobolevCarrier38 ((1 : ℕ) : ℝ)) :
  (∀ n : ℤ, actionCoefficient (coordinateActions z) n = ‖carrierCoe38 ((1 : ℕ) : ℝ) z n‖^2) ∧
  HasSum (fun n : ℤ => actionWeight n *
    |actionCoefficient (coordinateActions z) n|) (weightedActionNorm (coordinateActions z)) ∧
  weightedActionNorm (coordinateActions z) = ‖z‖^2 ∧
  (∀ n : ℤ, actionWeight n = 1 + (n : ℝ)^2) ∧ actionWeight 0 = 1 := by
  have hcoef : ∀ n : ℤ, actionCoefficient (coordinateActions z) n = ‖carrierCoe38 ((1 : ℕ) : ℝ) z n‖^2 := by
    intro n
    unfold actionCoefficient
    rw [G6034Aux.coordinateActions_apply]
    exact mul_div_cancel_left₀ _ (G6034Aux.actionWeight_pos n).ne'
  have hterm : (fun n : ℤ => actionWeight n * |actionCoefficient (coordinateActions z) n|) =
      fun n : ℤ => ‖coordinateActions z n‖ := by
    funext n
    rw [hcoef, abs_of_nonneg (sq_nonneg _), G6034Aux.coordinateActions_apply,
      Real.norm_of_nonneg (mul_nonneg (G6034Aux.actionWeight_pos n).le (sq_nonneg _))]
  have hS : HasSum (fun n : ℤ => actionWeight n *
      |actionCoefficient (coordinateActions z) n|) (weightedActionNorm (coordinateActions z)) := by
    rw [hterm]
    exact G6034Aux.hasSum_norm_one (coordinateActions z)
  have hN : weightedActionNorm (coordinateActions z) = ‖z‖^2 := by
    have h1 := G6034Aux.hasSum_norm_one (coordinateActions z)
    have h2 : HasSum (fun n : ℤ => ‖coordinateActions z n‖) (‖z‖ ^ 2) := by
      have h3 := G6034Aux.hasSum_coordinateActions z
      have he : (fun n : ℤ => ‖coordinateActions z n‖) = fun n : ℤ => coordinateActions z n := by
        funext n
        rw [Real.norm_of_nonneg]
        rw [G6034Aux.coordinateActions_apply]
        exact mul_nonneg (G6034Aux.actionWeight_pos n).le (sq_nonneg _)
      rw [he]
      exact h3
    exact h1.unique h2
  refine ⟨hcoef, hS, hN, G6034Aux.actionWeight_eq, ?_⟩
  rw [G6034Aux.actionWeight_eq]
  norm_num

end
end NlsGge.GKDefinitionDesign
