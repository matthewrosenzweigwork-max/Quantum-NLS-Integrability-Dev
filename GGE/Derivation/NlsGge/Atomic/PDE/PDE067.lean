import Mathlib
import NlsGge.ThirdConsultation.PDE.BirkhoffTop
import NlsGge.ThirdConsultation.PDE.BirkhoffRaw
import NlsGge.ThirdConsultation.Common.Actions
import NlsGge.ThirdConsultation.Common.FiniteSupport
import NlsGge.NLS38.PhysicalFlow38
import NlsGge.Atomic.PDE.PDE061
import NlsGge.Atomic.PDE.PDE066

/- PDE-067 PRODUCTION02 (proof development, AUTHOR; not reviewed). Target NlsGge/Atomic/PDE/PDE067.lean,
   namespace NlsGge.ThirdConsultation.PDE. Statement (def name and type) VERBATIM from Pro r14 '### PDE-067'. PROOF-SCRIPT REPAIR of the final
   `simpa only [..._Phi, actions, neg_mul, mul_comm] using actual_finitegap_rotation u hf t n`, which fails (lane
   bc1be5e4, replica of the verbatim body): `actions (actualPhi u)` is partial so simp does not unfold it, and mul_comm
   permutes the two sides differently. Replaced by: hact (actions as a lambda, rfl); simp only [_Phi]; rw [PDE-066, hact];
   congr 2; ring (exactly Pro's remark: scalar order in exp is immaterial by commutativity). Type of the def unchanged.
   Opens: Pro's prelude plus `open NlsGge.ThirdConsultation.Common` (repair 22 addendum: FiniteSupportSequence, actions,
   actualPhi are COMMON names used in the body). No separate host is needed: the record BirkhoffNLSFlowInput38 is landed
   (Birkhoff/BirkhoffInput38.lean:265, single field `rotation`), and the def itself is the packet.
   Uses: landed actualBirkhoffTop38 / actualBirkhoffTop38_Phi (PDE/BirkhoffTop.lean), PDE-061 measurable_actualOmega
   (h782, landing q195), PDE-066 actual_finitegap_rotation (h782, drafted; awaits h783 PDE-065).
   MAIN-ONLY (BirkhoffTop closure). -/
set_option autoImplicit false
open Set Filter Topology Metric MeasureTheory
open scoped BigOperators ENNReal InnerProductSpace
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.SpectralFoundations NlsGge.GK38 NlsGge.Atomic.Common
open NlsGge.GKDefinitionDesign NlsGge.NLS38
open NlsGge.ThirdConsultation.Common
namespace NlsGge.ThirdConsultation.PDE

def actualBirkhoffNLSFlowInput38 :
    BirkhoffNLSFlowInput38 NlsGge.ThirdConsultation.PDE.actualBirkhoffTop38
      NlsGge.NLS38.nlsFlowL2 where
  rotation := by
    refine ⟨actualOmega, measurable_actualOmega, ?_⟩
    intro u hfin t n
    have hf : FiniteSupportSequence (actualPhi u) := by
      simpa only [FiniteSupportSequence,
        NlsGge.ThirdConsultation.PDE.actualBirkhoffTop38_Phi] using hfin
    have hact : actions (actualPhi u) = fun k => ‖actualPhi u k‖ ^ 2 := rfl
    simp only [NlsGge.ThirdConsultation.PDE.actualBirkhoffTop38_Phi]
    rw [actual_finitegap_rotation u hf t n, hact]
    congr 2
    ring

end NlsGge.ThirdConsultation.PDE
