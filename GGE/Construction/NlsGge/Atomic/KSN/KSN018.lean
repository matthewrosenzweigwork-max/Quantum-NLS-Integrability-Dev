import Mathlib
import NlsGge.Atomic.KSN.KSN018Host
import NlsGge.Atomic.KSN.KSN018Asm
import NlsGge.Atomic.KSN.KSN012
import NlsGge.Atomic.KSN.KSN014
import NlsGge.Atomic.KSN.KSN017
import NlsGge.Atomic.KSN.KSN010
import NlsGge.Atomic.G4.G4014
import NlsGge.ThirdConsultation.KSPS.KSPS017Uniform7
import NlsGge.ThirdConsultation.KSPS.KSPSAntitraceUniform

                                                                                                                    
                                                                                                                  
                                                                                                                   
                                                                                                                       
                                                                                              
                                                                                                     
                                                                                 
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open scoped BigOperators
open NlsGge.Pilot NlsGge.GK38 NlsGge.Birkhoff NlsGge.Sobolev38
open NlsGge.Atomic.Common NlsGge.GKDefinitionDesign

namespace NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.KSN

theorem KSN018_main (N : ℕ) (hN : 1 ≤ N) :
  (∀ x₀ ∈ complexDomain (N : ℝ) (Nat.cast_nonneg N),
    ∃ (U : Set (PairScale (N : ℝ))) (C : ℝ),
      IsOpen U ∧ x₀ ∈ U ∧ U ⊆ complexDomain (N : ℝ) (Nat.cast_nonneg N) ∧ 0 ≤ C ∧
      ∀ x ∈ U, Memℓp (storedSequence ((N : ℝ) + 1) (smoothingCoefficient N x)) 2 ∧
        ‖complexSmoothing N x‖ ≤ C) ∧
  (∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, 0 ≤ C ∧
    ∀ x : PairScale (N : ℝ), IsRealPair (N : ℝ) x → ‖x‖ ≤ B →
      Memℓp (storedSequence ((N : ℝ) + 1) (smoothingCoefficient N x)) 2 ∧
      ‖complexSmoothing N x‖ ≤ C) :=
  NlsGge.ThirdConsultation.KSN.KSN018_of N hN
    NlsGge.GKDefinitionDesign.KSN012_main
    NlsGge.GKDefinitionDesign.KSN014_main
    NlsGge.GKDefinitionDesign.KSN017_main
    NlsGge.GKDefinitionDesign.KSN010_main.1
    (fun n φ h => NlsGge.GKDefinitionDesign.G4014Aux.cartZ_plus n φ h)
    (fun n φ h => NlsGge.GKDefinitionDesign.G4014Aux.cartZ_minus n φ h)
    NlsGge.ThirdConsultation.KSPS.midpoint_dirichlet_difference_uniform
    NlsGge.ThirdConsultation.KSPS.antitrace_at_dirichlet_uniform

end NlsGge.GKDefinitionDesign
