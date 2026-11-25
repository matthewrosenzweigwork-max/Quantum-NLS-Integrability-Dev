import Mathlib
import NlsGge.ThirdConsultation.I.I030Core
import NlsGge.ThirdConsultation.I.ActualEnsembleBridge
import NlsGge.ThirdConsultation.PDE.BirkhoffRealization

                                                                                                                    
                                                                                                                      
                                                                                                              
                                                                                             
                                                                                                                      
                                                                                                                     
                                                                                                              
                                                                                                                           
                                                                                                      
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology ContDiff
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights
open NlsGge.HierarchyRiccati.Core NlsGge.SpectralFoundations
open NlsGge.Birkhoff NlsGge.Sobolev38 NlsGge.GKDefinitionDesign
open scoped BoundedContinuousFunction

namespace NlsGge.ThirdConsultation.I

theorem i030 (lower upper : ℝ) (c : BoundedCoefficients lower upper) :
    (∀ j : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ d : ℕ,
      ∀ u : PhysicalL2, SobolevSquareSummable ((j + 1 : ℕ) : ℝ) (physicalFourier u) →
        |chargeFn38 (j + 2) j u| ≤ C * (1 + ‖physFS38 (j + 1) u‖) ^ d) ∧
    (∀ (j : ℕ) (q : ℝ), 0 ≤ q →
      Integrable (fun u : PhysicalL2 => |chargeFn38 (j + 2) j u| ^ q)
        (physicalLaw (weight c.val))) ∧
    (∀ᵐ u ∂physicalLaw (weight c.val),
      ∃ (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1),
        smoothL2_38 U hU hper = u ∧
        ∀ j : ℕ, chargeFn38 (j + 2) j u = localCharge38 U j) :=
  NlsGge.ThirdConsultation.I030Aux.i030_of lower upper c PDE.actualBirkhoffTop38 PDE.actualBirkhoffMolnar38
    (physicalLaw (weight c.val)) (actual_ensemble_eq_I lower upper c).2.2.1

end NlsGge.ThirdConsultation.I
