import Mathlib
import NlsGge.ThirdConsultation.PDE.PDE074Core
import NlsGge.ThirdConsultation.PDE.ActualEnsemble
import NlsGge.ThirdConsultation.PDE.ActualGibbs
import NlsGge.ThirdConsultation.PDE.Round14ActionFreq
import NlsGge.Birkhoff.S04FiniteGapInvariance38
import NlsGge.Atomic.PDE.PDE039
import NlsGge.Atomic.PDE.PDE061
import NlsGge.Atomic.PDE.PDE072
import NlsGge.Atomic.PDE.PDE073

                                                                                                            
                                                                                                                          
                                                                                                 
                                                                                                                           
                                                                                                                      
                                                                                                                      
                                          
                                                                                                                   
                                                                                                                             
                                                                                                                 
                                                                                                       
                                                                                                                             
                                                                                                
set_option autoImplicit false
open Set Filter Topology Metric MeasureTheory
open scoped BigOperators ENNReal InnerProductSpace
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.SpectralFoundations NlsGge.GK38 NlsGge.Atomic.Common
open NlsGge.GKDefinitionDesign NlsGge.NLS38
namespace NlsGge.ThirdConsultation.PDE

theorem actual_finitegap_law_invariant
    (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper)
    (Lambda : Finset ℤ) (t : ℝ) :
  Measure.map (nlsFlowL2 t) (actualNu c Lambda) = actualNu c Lambda := by
  have hbr : finiteGibbsDensity c Lambda = fun w : Lambda → ℂ =>
      ENNReal.ofReal (actualBirkhoffTop38.densΛ38 c Lambda w / actualBirkhoffTop38.ZcalΛ38 c Lambda) := rfl
  exact PDE074Aux.nu_invariant_of actualBirkhoffTop38 c Lambda (nlsFlowL2 t) (measurable_actual_flow t)
    (kappaΛ38 actualOmega Lambda t) (measurable_kappaΛ38 actualOmega measurable_actualOmega Lambda t)
    (PDE074Aux.rotationInvariant_kappa actualOmega Lambda t)
    (finiteGibbsDensity c Lambda)
    (by rw [hbr]; exact actualBirkhoffTop38.measurable_nuHatDens38 lower upper c hlower hbound hupper Lambda)
    (fun z => actual_finite_density_twist lower upper c hlower hbound hupper Lambda t z)
    (by rw [hbr]; rfl)
    (fun w => actual_finiteGapField_twist Lambda w t)

end NlsGge.ThirdConsultation.PDE
