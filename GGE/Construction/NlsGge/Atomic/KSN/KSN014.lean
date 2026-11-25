import Mathlib
import NlsGge.Atomic.KSN.KSN014Asm
import NlsGge.Atomic.M.M032

                                                                                                                    
                                                                                                                
                                                                                                           
                                                                                                             
                                                                                                        
                                   
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open scoped BigOperators
open NlsGge.Pilot NlsGge.GK38 NlsGge.Birkhoff NlsGge.Sobolev38
open NlsGge.Atomic.Common NlsGge.GKDefinitionDesign

namespace NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.KSN

theorem KSN014_main :
  (∀ x₀ ∈ complexDomain 1 (by norm_num),
    ∃ (U : Set (PairScale 1)) (C : ℝ), IsOpen U ∧ x₀ ∈ U ∧
      U ⊆ complexDomain 1 (by norm_num) ∧ 0 ≤ C ∧
      ∀ x ∈ U, ∀ n : ℤ,
        ‖xiN38 n (pairPotential 1 (by norm_num) x) - 1‖ ≤ C / bracket n) ∧
  (∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, 0 ≤ C ∧
    ∀ x : PairScale 1, IsRealPair 1 x → ‖x‖ ≤ B → ∀ n : ℤ,
      ‖xiN38 n (pairPotential 1 (by norm_num) x) - 1‖ ≤ C / bracket n) :=
  NlsGge.ThirdConsultation.KSN.KSN014_of_M032
    (fun w hw N φ hW hφ hN => (NlsGge.ThirdConsultation.M.gap_weighted_tail w hw N φ hW hφ hN).2.2)

end NlsGge.GKDefinitionDesign
