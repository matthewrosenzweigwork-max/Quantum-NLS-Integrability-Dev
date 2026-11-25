import Mathlib
import NlsGge.ThirdConsultation.PDE.Round14InverseRotation
import NlsGge.ThirdConsultation.PDE.Round14Deriv
import NlsGge.ThirdConsultation.PDE.PDE064Core
import NlsGge.Atomic.PDE.PDE063
import NlsGge.Atomic.G6.G6027

                                                                                                  
                                                                                    
                                                                                                                         
                                                           
                                                                                                                       
                                                                                                                 
                                                                                                                       
                                                                                                          
                                                                                      
set_option autoImplicit false
open Set Filter Topology Metric MeasureTheory
open scoped BigOperators ENNReal InnerProductSpace
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.SpectralFoundations NlsGge.GK38 NlsGge.Atomic.Common
open NlsGge.GKDefinitionDesign NlsGge.NLS38
open NlsGge.ThirdConsultation.Common
namespace NlsGge.ThirdConsultation.PDE

theorem inverse_finite_curve_hasDerivAt
    (z0 : Lib.L2Z) (hz : FiniteSupportSequence z0) (t0 : ℝ) :
  HasDerivAt (inverseRotationCurve z0 hz)
    (DPhiinv 3 (rotationCurve ((3 : ℕ) : ℝ) z0 hz t0)
      (rotationDeriv ((3 : ℕ) : ℝ) z0 hz t0)) t0 :=
  PDE064Aux.hasDerivAt_comp_of_analyticOnNhd (inverseBirkhoffSobolev 3)
    (G6027 3 (by norm_num)).2.1
    (fun t : ℝ => rotationCurve ((3 : ℕ) : ℝ) z0 hz t)
    (rotationDeriv ((3 : ℕ) : ℝ) z0 hz t0) t0
    ((finite_support_rotation_regular z0 hz ((3 : ℕ) : ℝ)).2.1 t0)

end NlsGge.ThirdConsultation.PDE
