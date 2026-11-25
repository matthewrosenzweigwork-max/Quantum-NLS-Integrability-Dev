import Mathlib
import NlsGge.ThirdConsultation.G6.BirkhoffBasic
import NlsGge.ThirdConsultation.G6.RealCartesianBirkhoff
import NlsGge.Atomic.G6.G6011Sup1Core
import NlsGge.Atomic.G6.G6013Host
import NlsGge.Atomic.G6.G6013Sup1
import NlsGge.Atomic.G6.G6010
import NlsGge.Atomic.G6.G6011
import NlsGge.Atomic.G6.G6012

                                                                                                            
                                                                                                                                 
                                                                                                                                
                                                                                                                             
                                                                                                                           
                                                                                                                     
                                                                                                     
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Common
open scoped ENNReal InnerProductSpace

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G6013 :
  Function.Bijective realBirkhoffCartesian ∧ Function.Bijective physicalBirkhoff ∧
  Function.LeftInverse inverseBirkhoffCartesian realBirkhoffCartesian ∧
  Function.RightInverse inverseBirkhoffCartesian realBirkhoffCartesian ∧
  Function.LeftInverse physicalInverseBirkhoff physicalBirkhoff ∧
  Function.RightInverse physicalInverseBirkhoff physicalBirkhoff := by
  have h0 : ∃! u : PhysicalL2, realBirkhoffCartesian u = 0 := by
    have hpre := G6010.1
    have hmem : (0 : PhysicalL2) ∈ realBirkhoffCartesian ⁻¹' ({0} : Set CartesianReal) := by
      rw [hpre]
      exact Set.mem_singleton 0
    refine ⟨0, hmem, fun y hy => ?_⟩
    have hy' : y ∈ realBirkhoffCartesian ⁻¹' ({0} : Set CartesianReal) := hy
    rw [hpre] at hy'
    exact hy'
  have hR : Function.Bijective realBirkhoffCartesian :=
    G6011Aux.bijective_of_singletonFiber realBirkhoffCartesian ⟨G6011, G6012⟩ h0
  obtain ⟨e, -, he⟩ := exists_physicalCartesianEquiv
  have hP : Function.Bijective physicalBirkhoff := by
    refine ⟨fun a b hab => hR.1 (by rw [he a, he b, hab]), fun z => ?_⟩
    obtain ⟨u, hu⟩ := hR.2 (e z)
    refine ⟨u, e.injective ?_⟩
    rw [← he u, hu]
  exact ⟨hR, hP, Function.leftInverse_invFun hR.1, Function.rightInverse_invFun hR.2,
    Function.leftInverse_invFun hP.1, Function.rightInverse_invFun hP.2⟩

end
end NlsGge.GKDefinitionDesign
