import Mathlib
import NlsGge.Atomic.KST.KST065
import NlsGge.Atomic.PhysicalSobolev
import NlsGge.Definitions.PilotInterfaces
import NlsGge.GK38.Defs
import NlsGge.ThirdConsultation.KO.Basic
import NlsGge.ThirdConsultation.KST.KST061Host
import NlsGge.ThirdConsultation.KST.KST066Host
import NlsGge.ThirdConsultation.KST.KST066Support

/- KST-066 PRODUCTION01 (proof development, AUTHOR; not self-reviewed).  Target NlsGge/Atomic/KST/KST066.lean,
   namespace NlsGge.ThirdConsultation.KST.  Head VERBATIM from design STATEMENTS/KST.md "## KST-066"
   (proof development's KST066Head; byte-identical in gpt6pro_followup8/9/10; no Pro round entry).  No repair of the head.
   Route (as proof development's KST066_ROUTE.md / KST066_STOP.md): the landed conditional reduction
   `kst066_of_smooth` (KST066Support: all of KST-066 except smoothness) with its single hypothesis
   `hsm : forall w, finiteGap w -> SmoothPhysical w` discharged by the second conjunct of `kst065`
   (finite gaps imply smoothness of the actual potential).  No new hypothesis. -/
set_option autoImplicit false
noncomputable section
open Filter Topology
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.ThirdConsultation.KST

theorem kst066 (s : ℝ) (hs : 0 ≤ s)
    (u : NlsGge.Atomic.Common.PhysicalSobolev38 s) :
  ∃ v : ℕ → NlsGge.Atomic.Common.PhysicalSobolev38 s,
    Tendsto v atTop (𝓝 u) ∧
    ∀ j : ℕ, let uj := NlsGge.GKDefinitionDesign.physicalSobolevEmbedRealExponent s hs (v j)
      NlsGge.ThirdConsultation.finiteGap uj ∧ pairFiniteGap (realSlice uj) ∧
      NlsGge.ThirdConsultation.KO.SmoothPhysical uj :=
  kst066_of_smooth (fun w hw => (kst065 w hw).2.1) s hs u

end NlsGge.ThirdConsultation.KST
end
