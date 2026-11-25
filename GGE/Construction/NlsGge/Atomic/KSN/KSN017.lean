import Mathlib
import NlsGge.Atomic.KSN.KSN017Asm
import NlsGge.Atomic.M.M032
import NlsGge.ThirdConsultation.KSPS.KSPS017Uniform7
                                                                                                                      
                                                                                                                     
                                                                                                                                         
                                                                                                               
                                                                                                
                                                                                                                     
                                                                                                              
                                                                                                            
                                                                                                          
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open scoped BigOperators
open NlsGge.Pilot NlsGge.GK38 NlsGge.Birkhoff NlsGge.Sobolev38
open NlsGge.Atomic.Common NlsGge.GKDefinitionDesign

namespace NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.KSN

theorem KSN017_main :
  (∀ x₀ ∈ complexDomain 1 (by norm_num),
    ∃ (U : Set (PairScale 1)) (C : ℝ), IsOpen U ∧ x₀ ∈ U ∧
      U ⊆ complexDomain 1 (by norm_num) ∧ 0 ≤ C ∧
      ∀ x ∈ U, ∀ n : ℤ,
        deltaFactor n (pairPotential 1 (by norm_num) x) (muSeq (pairPotential 1 (by norm_num) x) n) ≠ 0 ∧
        ‖(deltaFactor n (pairPotential 1 (by norm_num) x) (muSeq (pairPotential 1 (by norm_num) x) n))⁻¹ - (-1 : ℂ)^n‖ ≤ C / bracket n) ∧
  (∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, 0 ≤ C ∧
    ∀ x : PairScale 1, IsRealPair 1 x → ‖x‖ ≤ B → ∀ n : ℤ,
      deltaFactor n (pairPotential 1 (by norm_num) x) (muSeq (pairPotential 1 (by norm_num) x) n) ≠ 0 ∧
        ‖(deltaFactor n (pairPotential 1 (by norm_num) x) (muSeq (pairPotential 1 (by norm_num) x) n))⁻¹ - (-1 : ℂ)^n‖ ≤ C / bracket n) :=
  NlsGge.ThirdConsultation.KSN.KSN017_of
    (fun w hw N φ hW hφ hN => (NlsGge.ThirdConsultation.M.gap_weighted_tail w hw N φ hW hφ hN).2.2)
    NlsGge.ThirdConsultation.KSPS.midpoint_first_order_uniform

end NlsGge.GKDefinitionDesign
