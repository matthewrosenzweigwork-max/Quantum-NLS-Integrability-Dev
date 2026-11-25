import Mathlib
import NlsGge.Atomic.PhysicalSobolev
import NlsGge.Atomic.G6.G6001Sup1Core
import NlsGge.Atomic.G5.G5012
import NlsGge.Atomic.G5.G5012Sup3
import NlsGge.Atomic.G5.G5032Sup1
import NlsGge.Atomic.G4.G4040
import NlsGge.Atomic.G5.G5040

/- G6-001 PACKET (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/Atomic/G6/G6001.lean, namespace NlsGge.GKDefinitionDesign.
   Head `G6001` VERBATIM from followup12 STATEMENTS/G6.md section G6-001 (round 14: "retain the existing complete head"); G6 shared
   context opens copied from that file.  No lexical repair.  jacobianAdjoint is the landed host G5012Host (no redefinition).
   Proof (GK Theorem 19.1 via the pairing half of Lemma F.7): G6001Aux.core6001 (G6001Sup1Core) with
   landed G5012 (A e_j = gradient of the physical coordinate), G5012Sup3.gradient_physicalCoordinate,
   landed G5032Sup1.star_pairGradientCLM_snd + fderiv_realSlice_im with the landed real-slice reality G4040 (X, Y real),
   and the canonical relations G5040.  No compactness is used (G5-015 is consumed by G6-002). -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Common
open scoped ENNReal InnerProductSpace

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G6001 (u : PhysicalL2) : Function.Injective (jacobianAdjoint u) := by
  have hre : ∀ (v : PhysicalL2) (n : ℤ),
      (cartesianX n (realSlice v)).im = 0 ∧ (cartesianY n (realSlice v)).im = 0 :=
    fun v n => ⟨(G4040 v n).1, (G4040 v n).2.1⟩
  exact G6001Aux.core6001 u (G5012.2.2 u) (gradient_physicalCoordinate u)
    (fun n => G5032Sup1.star_pairGradientCLM_snd _
      (G5032Sup1.fderiv_realSlice_im _ (fun v => (hre v n).1) u))
    (fun n => G5032Sup1.star_pairGradientCLM_snd _
      (G5032Sup1.fderiv_realSlice_im _ (fun v => (hre v n).2) u))
    (fun m n => G5040 u m n)

end
end NlsGge.GKDefinitionDesign
