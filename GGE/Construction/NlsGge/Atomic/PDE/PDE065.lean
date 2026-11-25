import Mathlib
import NlsGge.ThirdConsultation.PDE.PDE065Core
import NlsGge.ThirdConsultation.PDE.Round14InverseRotation
import NlsGge.ThirdConsultation.PDE.Round14Rotation
import NlsGge.ThirdConsultation.PDE.Round14Deriv
import NlsGge.ThirdConsultation.Common.Actions
import NlsGge.ThirdConsultation.Common.FiniteSupport
import NlsGge.Atomic.PDE.PDE062
import NlsGge.Atomic.PDE.PDE063
import NlsGge.Atomic.PDE.PDE064
import NlsGge.Atomic.G6.G6027

                                                                                                            
                                                                                                                          
                                                                                  
                                                                                                                           
                                                                   
                                                                                                     
                                                                                                  
                                                                                      
                                                                                                    
                                                                            
                                                                                                
                                                                                                    
                                                                                           
                                                                                                                  
                                                                                                             
set_option autoImplicit false
open Set Filter Topology Metric MeasureTheory
open scoped BigOperators ENNReal InnerProductSpace
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.SpectralFoundations NlsGge.GK38 NlsGge.Atomic.Common
open NlsGge.GKDefinitionDesign NlsGge.NLS38
open NlsGge.ThirdConsultation.Common
namespace NlsGge.ThirdConsultation.PDE

theorem inverse_rotation_is_actual_nls
    (z0 : Lib.L2Z) (hz : FiniteSupportSequence z0) :
  (∀ t0 : ℝ,
    HasDerivAt (fun t : ℝ => physicalCoreBase (inverseRotationCurve z0 hz t))
      (nlsVectorField (inverseRotationCurve z0 hz t0)) t0) ∧
  IsPhysicalNLSSolution (inverseRotationPhysical z0 hz) := by
  obtain ⟨hΦa1, hΨa1, hL1, hR1, -, hc1⟩ := G6027 1 le_rfl
  obtain ⟨-, hΨa3, -, -, -, hc3⟩ := G6027 3 (by norm_num)
  exact PDE065Aux.rotation_nls_core actualOmega (actions z0)
    (fun t => rotationCurve ((3 : ℕ) : ℝ) z0 hz t) (fun t => rotationDeriv ((3 : ℕ) : ℝ) z0 hz t)
    hΦa1 hΨa1 hL1 hR1 (fun z => (hc1 z).2) hΨa3 (fun z => (hc3 z).2)
    (fun u n => actual_nls_coordinate_field u n)
    (finite_support_rotation_regular z0 hz ((3 : ℕ) : ℝ)).2.2.1
    (fun t n => by
      unfold rotationDeriv rotationCurve
      rw [carrierCoe38_mk, carrierCoe38_mk]
      rfl)
    (fun t0 => inverse_finite_curve_hasDerivAt z0 hz t0)

end NlsGge.ThirdConsultation.PDE
