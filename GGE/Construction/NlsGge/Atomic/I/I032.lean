import Mathlib
import NlsGge.ThirdConsultation.I.I032Core
import NlsGge.ThirdConsultation.I.ActualEnsembleBridge
import NlsGge.Atomic.PDE.PDE067

                                                                                                            
                                                                                                                         
                                                                                                       
                                                                                                                     
                                                                           
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology ContDiff BoundedContinuousFunction
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights
open NlsGge.SpectralFoundations
open NlsGge.Birkhoff NlsGge.Sobolev38 NlsGge.GKDefinitionDesign
open NlsGge.Atomic.I010 (spectralEnergy)
open NlsGge.ThirdConsultation

namespace NlsGge.ThirdConsultation.I

theorem i032 (lower upper : ℝ) (c : BoundedCoefficients lower upper) (t : ℝ) :
    (physicalLaw (weight c.val)).map (NlsGge.NLS38.nlsFlowL2 t) =
      physicalLaw (weight c.val) ∧
    ∀ m : ℕ, 1 ≤ m →
      Continuous (fun u : SobolevHilbert (m : ℝ) =>
        physFS38 m (NlsGge.NLS38.nlsFlowL2 t (sobolevToL2_38 m u))) ∧
      ∀ F : SobolevHilbert (m : ℝ) →ᵇ ℝ,
        (∫ u : PhysicalL2, F (physFS38 m (NlsGge.NLS38.nlsFlowL2 t u))
          ∂physicalLaw (weight c.val)) =
        ∫ u : PhysicalL2, F (physFS38 m u) ∂physicalLaw (weight c.val) :=
  I032Aux.i032_of PDE.actualBirkhoffTop38 lower upper c PDE.actualBirkhoffNLSFlowInput38
    (actual_ensemble_eq_I lower upper c).2.2.1 t

end NlsGge.ThirdConsultation.I
