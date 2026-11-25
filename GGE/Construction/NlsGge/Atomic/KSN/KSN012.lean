import Mathlib
import NlsGge.Atomic.KSN.KSN012Asm
import NlsGge.Atomic.KSN.KSN012BetaLocal
import NlsGge.Atomic.KSN.KSN012MissingA
import NlsGge.Atomic.KSN.KSN010
import NlsGge.Atomic.M.M032

                                                                                                                    
                                                                                                                     
                                                                                                         
                                            
                                                                                              
                                                                                               
                                                                                                          
                                                              
                                   
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open scoped BigOperators
open NlsGge.Pilot NlsGge.GK38 NlsGge.Birkhoff NlsGge.Sobolev38
open NlsGge.Atomic.Common NlsGge.GKDefinitionDesign

namespace NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.KSN

theorem KSN012_main :
  (∀ x₀ ∈ complexDomain 1 (by norm_num),
    ∃ (U : Set (PairScale 1)) (C : ℝ), IsOpen U ∧ x₀ ∈ U ∧
      U ⊆ complexDomain 1 (by norm_num) ∧ 0 ≤ C ∧
      ∀ x ∈ U, ∀ n : ℤ,
        ‖betaSum n (pairPotential 1 (by norm_num) x)‖ ≤ C / bracket n ∧
        ∀ a : ℤ, (a = 1 ∨ a = -1) → ‖eta n a (pairPotential 1 (by norm_num) x) - 1‖ ≤ C / bracket n) ∧
  (∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, 0 ≤ C ∧
    ∀ x : PairScale 1, IsRealPair 1 x → ‖x‖ ≤ B → ∀ n : ℤ,
      ‖betaSum n (pairPotential 1 (by norm_num) x)‖ ≤ C / bracket n ∧
        ∀ a : ℤ, (a = 1 ∨ a = -1) → ‖eta n a (pairPotential 1 (by norm_num) x) - 1‖ ≤ C / bracket n) :=
  NlsGge.ThirdConsultation.KSN012L.KSN012_of
    (fun φ₀ hφ₀ => NlsGge.ThirdConsultation.KSN012L.beta_local
      (fun w hw N φ hW hφ hN => (NlsGge.ThirdConsultation.M.gap_weighted_tail w hw N φ hW hφ hN).2.2)
      NlsGge.ThirdConsultation.KSN.KSN012_missingB_holds φ₀ hφ₀)
    NlsGge.GKDefinitionDesign.KSN010_main.2

end NlsGge.GKDefinitionDesign
