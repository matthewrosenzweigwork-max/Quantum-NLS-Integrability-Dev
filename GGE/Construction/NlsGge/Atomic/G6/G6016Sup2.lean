import Mathlib
import NlsGge.Atomic.G6.G6016Host
import NlsGge.Atomic.G6.G6016Sup1Core
import NlsGge.Atomic.G5.G5012
import NlsGge.Atomic.G5.G5012Sup3
import NlsGge.Atomic.G5.G5032Sup1
import NlsGge.Atomic.G4.G4040
import NlsGge.Atomic.G5.G5040

                                                                           
                                                                                                                      
                                                                                                                          
                                                                                                                     
                                                                                          
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Common
open scoped ENNReal InnerProductSpace

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem fderiv_physicalBirkhoff_actionField (v : PhysicalL2) (n : ℤ) :
    fderiv ℝ physicalBirkhoff v
        (physicalHamiltonianField (fun w : PhysicalL2 => actualGapActionAllE02_38 w n) v) =
      lp.single 2 n (-Complex.I * physicalBirkhoff v n) := by
  have hre : ∀ (w : PhysicalL2) (k : ℤ),
      (cartesianX k (realSlice w)).im = 0 ∧ (cartesianY k (realSlice w)).im = 0 :=
    fun w k => ⟨(G4040 w k).1, (G4040 w k).2.1⟩
  exact G6016Aux.fderiv_actionField v (G5012.2.2 v) (gradient_physicalCoordinate v)
    (fun k => G5032Sup1.star_pairGradientCLM_snd _
      (G5032Sup1.fderiv_realSlice_im _ (fun w => (hre w k).1) v))
    (fun k => G5032Sup1.star_pairGradientCLM_snd _
      (G5032Sup1.fderiv_realSlice_im _ (fun w => (hre w k).2) v))
    (fun a b => G5040 v a b) n

end
end NlsGge.GKDefinitionDesign
