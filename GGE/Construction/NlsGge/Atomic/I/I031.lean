import Mathlib
import NlsGge.ThirdConsultation.I.I031Core
import NlsGge.ThirdConsultation.I.ActualEnsembleBridge
import NlsGge.ThirdConsultation.PDE.PDE073Sup
import NlsGge.Atomic.PDE.PDE061
import NlsGge.Atomic.PDE.PDE072
import NlsGge.Atomic.PDE.PDE074
import NlsGge.Atomic.G6.G6028
import NlsGge.Birkhoff.S04FiniteGapInvariance38

                                                                                                                    
                                                                                                                          
                                                                                                            
                                                                                                    
                                                    
                                                                                                                        
                                                                                                                   
                                                                                                                          
                                                                                                                         
                                                                                                   
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights
open NlsGge.SpectralFoundations
open NlsGge.Birkhoff NlsGge.Sobolev38 NlsGge.GKDefinitionDesign
open NlsGge.Atomic.I010 (spectralEnergy)
open NlsGge.ThirdConsultation

namespace NlsGge.ThirdConsultation.I

theorem i031 (lower upper : ℝ) (c : BoundedCoefficients lower upper) (Λ : Finset ℤ) :
    ∃ ω : (Λ → ℝ) → Λ → ℝ, ∀ t : ℝ,
      (∀ (w : Λ → ℂ) (n : Λ),
        finiteGapFlow Λ t w n =
          Complex.exp (-Complex.I * ((t * ω (fun k => ‖w k‖ ^ 2) n : ℝ) : ℂ)) * w n) ∧
      (∀ w : Λ → ℂ,
        NlsGge.NLS38.nlsFlowL2 t (finiteGapField Λ w) =
          finiteGapField Λ (finiteGapFlow Λ t w) ∧
        (∀ n : ℤ, actualGapActionAllE02_38
          (NlsGge.NLS38.nlsFlowL2 t (finiteGapField Λ w)) n =
            actualGapActionAllE02_38 (finiteGapField Λ w) n) ∧
        spectralEnergy (weight c.val) (NlsGge.NLS38.nlsFlowL2 t (finiteGapField Λ w)) =
          spectralEnergy (weight c.val) (finiteGapField Λ w)) ∧
      MeasurePreserving (finiteGapFlow Λ t) (finiteComplexVolume Λ) (finiteComplexVolume Λ) ∧
      (finiteGapCoordinateLaw (weight c.val) Λ).map (finiteGapFlow Λ t) =
        finiteGapCoordinateLaw (weight c.val) Λ ∧
      (finiteGapLaw (weight c.val) Λ).map (NlsGge.NLS38.nlsFlowL2 t) =
        finiteGapLaw (weight c.val) Λ := by
  obtain ⟨hlower, -, hc⟩ := c.property
  have hbound : ∀ j : ℕ, lower ≤ c.val j := fun j => (hc j).1
  have hupper : ∀ j : ℕ, c.val j ≤ upper := fun j => (hc j).2
  have hens := (actual_ensemble_eq_I lower upper c).2.2.2 Λ
  exact I031Aux.i031_of PDE.actualBirkhoffTop38 PDE.actualOmega PDE.measurable_actualOmega
    lower upper c Λ
    (fun u n => PDE.actualBirkhoffTop38_Phi u n)
    (fun w => actual_finiteGapField_eq Λ w)
    (fun w t => PDE.actual_finiteGapField_twist Λ w t)
    (fun t w => PDE.PDE073Aux.actual_densΛ38_twist c.val Λ t w)
    (fun t => PDE.actual_finitegap_law_invariant lower upper c.val hlower hbound hupper Λ t)
    hens.2.1 hens.2.2
    (PDE.actualBirkhoffTop38.measurable_nuHatDens38 lower upper c.val hlower hbound hupper Λ)
    (fun u n => ((G6028).1 u n).2.2)

end NlsGge.ThirdConsultation.I
