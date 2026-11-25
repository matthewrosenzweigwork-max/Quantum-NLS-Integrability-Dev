import Mathlib
import NlsGge.ThirdConsultation.G6.BirkhoffBasic
import NlsGge.ThirdConsultation.G6.RealCartesianBirkhoff
import NlsGge.Atomic.G6.G6011Sup1Core
import NlsGge.Atomic.G6.G6013Host
import NlsGge.Atomic.G6.G6013Sup1
import NlsGge.Atomic.G6.G6010
import NlsGge.Atomic.G6.G6011
import NlsGge.Atomic.G6.G6012

/- G6-013 PACKET (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G6/G6013.lean.
   Head `G6013` VERBATIM from PRO_DEFINITION_RESPONSE_FP80_14.md cluster 6 (= followup12 STATEMENTS/G6.md "## G6-013"); G6 shared
   opens. No lexical repair.  inverseBirkhoffCartesian is hosted once in G6013Host (design body); physicalInverseBirkhoff is the
   landed BirkhoffBasic body.  Proof (GK Theorem 19.3): singleton-fiber set clopen (G6011, G6012), contains 0 (G6010), target
   connected (LIB-085 via G6011Aux.bijective_of_singletonFiber), so realBirkhoffCartesian is bijective; physicalBirkhoff is
   transported through the round-14 cluster-6 bridge CLE (G6013Sup1.exists_physicalCartesianEquiv; no physical clopen
   statement re-proved, no G6028); the four Function.invFun equations are earned from bijectivity. -/
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
