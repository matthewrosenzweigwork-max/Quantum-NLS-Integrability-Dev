import Mathlib
import NlsGge.ThirdConsultation.PDE.Round14Rotation
import NlsGge.ThirdConsultation.PDE.PDE063Core
import NlsGge.ThirdConsultation.Common.Actions
import NlsGge.ThirdConsultation.Common.FiniteSupport

                                                                                                                    
                                                                                                                     
                                                                                                                  
                                                                                                                        
                                                                                                        
                                                                                                                     
                                                                                                 
                                                                                                      
set_option autoImplicit false
open Set Filter Topology Metric MeasureTheory
open scoped BigOperators ENNReal InnerProductSpace
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.SpectralFoundations NlsGge.GK38 NlsGge.Atomic.Common
open NlsGge.GKDefinitionDesign NlsGge.NLS38
open NlsGge.ThirdConsultation.Common
namespace NlsGge.ThirdConsultation.PDE

theorem finite_support_rotation_regular
    (z0 : Lib.L2Z) (hz : FiniteSupportSequence z0) :
  ∀ r : ℝ,
    ContDiff ℝ 1 (fun t : ℝ => rotationCurve r z0 hz t) ∧
    (∀ t : ℝ, HasDerivAt (fun s : ℝ => rotationCurve r z0 hz s)
      (rotationDeriv r z0 hz t) t) ∧
    (∀ (t : ℝ) (n : ℤ),
      ‖carrierCoe38 r (rotationCurve r z0 hz t) n‖^2 = actions z0 n) ∧
    ∀ t : ℝ,
      {n : ℤ | carrierCoe38 r (rotationCurve r z0 hz t) n ≠ 0} =
        {n : ℤ | z0 n ≠ 0} := fun r =>
  PDE063Aux.rotation_core r (fun n => actualOmega n (actions z0)) z0 hz
    (fun t => finiteSupport_mem_seqSobolev38 r _ (rotationSequence_finiteSupport z0 hz t))
    (fun t => finiteSupport_mem_seqSobolev38 r _ (rotationDerivativeSequence_finiteSupport z0 hz t))

end NlsGge.ThirdConsultation.PDE
