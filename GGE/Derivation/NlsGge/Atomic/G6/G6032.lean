import Mathlib
import NlsGge.Atomic.G6.G6032Core
import NlsGge.Atomic.G6.G6013
import NlsGge.Atomic.G6.G6021
import NlsGge.Atomic.G6.G6029
import NlsGge.Atomic.G6.G6030
import NlsGge.Atomic.G6.G6031
import NlsGge.Atomic.G2.G2045

/- G6032 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G6/G6032.lean.
   Packet G6-032, head VERBATIM from Pro (followup13 STATEMENTS/G6.md §G6-032; round 15 Q5 "Retain exact head";
   pin cc702018); shared G6 context block.  Proof: G6032S.G6032_of (G6032Core) applied to G6013 conjuncts 5/6,
   G6021, G6029 clause 3, G6030 at m = 1, G6031 (analyticity and energy integral) and the realSlice-inclusion and
   k = 3 trace clauses of G2_045 3.  The spectral input higherAction_eq_of_isospectral is G6032Sup1Core (landed
   contour-to-cut identity G2042MomentA.circle_eq_cut; resolves G6032_STOP.md).  TASK_INDEX prerequisites
   G2-042..045, G6-030, M-001, M-002, KSPS-001, KSN-001 (the M/KSPS/KSN entries are not used by this route).
   No new hypothesis; no repair. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Common
open scoped ENNReal InnerProductSpace

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G6032 (u v : PhysicalSobolev38 ((1 : ℕ) : ℝ))
    (hiso : physicalSobolevEmbed 1 v ∈ isospectralSet (physicalSobolevEmbed 1 u)) :
  nlsHamiltonian u = nlsHamiltonian v := by
  obtain ⟨U, -, -, hU, -, hall⟩ := G2_045 3 (by norm_num)
  exact NlsGge.ThirdConsultation.G6032S.G6032_of G6013.2.2.2.2.1 G6013.2.2.2.2.2 (fun x => (G6021 x).2)
    (fun x => (G6029 x).2.2) (fun x hx => (G6030 x 1 hx).2.2) G6031.1 (fun w => (G6031.2 w).2.2.2.2)
    U hU (fun φ hφ => ((hall φ hφ).2.2.2 rfl).2) u v hiso

end
end NlsGge.GKDefinitionDesign
