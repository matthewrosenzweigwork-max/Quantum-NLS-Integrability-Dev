import Mathlib
import NlsGge.ThirdConsultation.PDE.BirkhoffTop
import NlsGge.ThirdConsultation.PDE.BirkhoffRaw
import NlsGge.ThirdConsultation.Common.Actions
import NlsGge.ThirdConsultation.Common.FiniteSupport
import NlsGge.NLS38.PhysicalFlow38
import NlsGge.Atomic.PDE.PDE066

                                                                                                                           
                                                                                                                       
                                                                                                                            
                                                                                                                      
                                                                                               
set_option autoImplicit false
open Set Filter Topology Metric MeasureTheory
open scoped BigOperators ENNReal InnerProductSpace
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.SpectralFoundations NlsGge.GK38 NlsGge.Atomic.Common
open NlsGge.GKDefinitionDesign NlsGge.NLS38
open NlsGge.ThirdConsultation.Common
namespace NlsGge.ThirdConsultation.PDE

namespace PDE072Aux

theorem actual_rotation_Phi :
    ∀ u : PhysicalL2, {n : ℤ | actualBirkhoffTop38.Φ u n ≠ 0}.Finite → ∀ (t : ℝ) (n : ℤ),
      actualBirkhoffTop38.Φ (nlsFlowL2 t u) n =
        Complex.exp (-(((t * actualOmega n (fun k => ‖actualBirkhoffTop38.Φ u k‖ ^ 2) : ℝ) : ℂ) * Complex.I)) * actualBirkhoffTop38.Φ u n := by
  intro u hfin t n
  have hf : FiniteSupportSequence (actualPhi u) := by
    simpa only [FiniteSupportSequence, NlsGge.ThirdConsultation.PDE.actualBirkhoffTop38_Phi] using hfin
  have hact : actions (actualPhi u) = fun k => ‖actualPhi u k‖ ^ 2 := rfl
  simp only [NlsGge.ThirdConsultation.PDE.actualBirkhoffTop38_Phi]
  rw [actual_finitegap_rotation u hf t n, hact]
  congr 2
  ring

end PDE072Aux

end NlsGge.ThirdConsultation.PDE
