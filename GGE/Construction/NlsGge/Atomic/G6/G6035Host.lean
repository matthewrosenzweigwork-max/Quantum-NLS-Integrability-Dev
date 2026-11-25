import Mathlib
import NlsGge.Atomic.G6.G6034Host
import NlsGge.Atomic.G6.G6033Host
import NlsGge.Atomic.LIB.LIB003

                                                                                                                          
                                                                                                                        
                                                                                                                        
                                                                                                                  
                                                                                                           
                                                                                                                     
                                                        
                                                                                                                        
                                                                                                            
                                                                                                                         
                                                                                                             
                                                            
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Common
open scoped ENNReal InnerProductSpace

namespace NlsGge.GKDefinitionDesign
noncomputable section

abbrev PositiveActionSpace := {I : WeightedActionSpace // ∀ n : ℤ, 0 ≤ I n}

def coordinateActionsPositive (z : SobolevCarrier38 ((1 : ℕ) : ℝ)) : PositiveActionSpace :=
  ⟨coordinateActions z, fun n =>
    mul_nonneg (sobolevModeWeight_pos 1 n).le (sq_nonneg _)⟩

theorem positiveActionRoot_mem (I : PositiveActionSpace) :
  (fun n : ℤ => (Real.sqrt (actionCoefficient I.val n) : ℂ)) ∈ seqSobolev38 1 := by
  apply NlsGge.Atomic.LIB003.weightedSequence_mem_seqSobolev38
  have hw : ∀ n : ℤ, 0 < actionWeight n := fun n => sobolevModeWeight_pos 1 n
  have he : (fun n : ℤ => sobolevModeWeight 1 n * ‖(Real.sqrt (actionCoefficient I.val n) : ℂ)‖ ^ 2) =
      fun n : ℤ => ‖I.val n‖ := by
    funext n
    have hc : 0 ≤ actionCoefficient I.val n := div_nonneg (I.2 n) (hw n).le
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hc,
      Real.norm_of_nonneg (I.2 n)]
    unfold actionCoefficient
    have : sobolevModeWeight 1 n = actionWeight n := rfl
    rw [this]
    field_simp [(hw n).ne']
  rw [he]
  have h1 := lp.memℓp I.val
  have hs := h1.summable (by norm_num : 0 < (1 : ℝ≥0∞).toReal)
  simpa only [ENNReal.toReal_one, Real.rpow_one] using hs

def positiveActionRoot (I : PositiveActionSpace) : SobolevCarrier38 ((1 : ℕ) : ℝ) :=
  carrierMk38 ((1 : ℕ) : ℝ) (fun n => (Real.sqrt (actionCoefficient I.val n) : ℂ))
    (by rw [Nat.cast_one]; exact positiveActionRoot_mem I)

def actionHamiltonian (I : PositiveActionSpace) : ℝ :=
  transformedNLSHamiltonian (positiveActionRoot I)

end
end NlsGge.GKDefinitionDesign
