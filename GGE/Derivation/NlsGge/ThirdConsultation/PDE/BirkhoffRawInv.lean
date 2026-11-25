import Mathlib
import NlsGge.ThirdConsultation.PDE.BirkhoffRawInvCore
import NlsGge.Atomic.G6.G6013
import NlsGge.Atomic.G6.G6023

/- BKRAWC support (proof development, AUTHOR; not reviewed).  Target NlsGge/ThirdConsultation/PDE/BirkhoffRawInv.lean.
   Heads VERBATIM from round-14 DEFINITIONS/BIRKHOFF_REALIZATION.lean.md ("Literal raw sequence maps"):
   actualTinv38_mapsTo, actualT38_left_inv, actualT38_right_inv.  Producers as Pro's table: G6-013 (landed G6013, the
   inverse equations of physicalBirkhoff/physicalInverseBirkhoff) with Fourier inversion, and G6-023 (landed G6023,
   reverse direction) for the inverse levels m >= 1.  No hypothesis is added: the conditional cores are applied to the
   landed theorems. -/
set_option autoImplicit false
open Set
open scoped ENNReal Topology
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.SpectralFoundations
open NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.Common
namespace NlsGge.ThirdConsultation.PDE
noncomputable section

theorem actualTinv38_mapsTo (m : ℕ) :
    ∀ z ∈ seqSobolev38 (m : ℝ), actualTinv38 z ∈ seqSobolev38 (m : ℝ) :=
  BirkhoffRawInvCore.tinv_mapsTo_of (fun w => G6013.2.2.2.2.2 w) (fun u k => (G6023 u k).2) m

theorem actualT38_left_inv :
    ∀ x ∈ seqSobolev38 0, actualTinv38 (actualT38 x) = x :=
  BirkhoffRawInvCore.left_inv_of (fun u => G6013.2.2.2.2.1 u)

theorem actualT38_right_inv :
    ∀ z ∈ seqSobolev38 0, actualT38 (actualTinv38 z) = z :=
  BirkhoffRawInvCore.right_inv_of (fun w => G6013.2.2.2.2.2 w)

end
end NlsGge.ThirdConsultation.PDE
