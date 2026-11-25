import Mathlib
import NlsGge.Atomic.PhysicalSobolev
import NlsGge.Atomic.G6.G6002Sup1Core
import NlsGge.Atomic.G6.G6001
import NlsGge.Atomic.G5.G5015
import NlsGge.Atomic.G5.G5016
import NlsGge.Atomic.G4.G4042

/- G6-002 PACKET (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/Atomic/G6/G6002.lean, namespace NlsGge.GKDefinitionDesign.
   Head `G6002` VERBATIM from followup12 STATEMENTS/G6.md section G6-002 (round 14: "retain the existing complete head"); G6 shared
   context opens copied from that file.  No lexical repair.
   Proof (GK Theorem 19.1): the adjoint conjugate is injective (G6001) and a compact perturbation of the identity (landed G5015),
   hence an automorphism (G6002Aux.adjoint_equiv, Fredholm step of Lemma F.7); landed G5016 transfers this to the physical
   Jacobian; the Cartesian Jacobian is then an isomorphism through the explicit injective g5012_L_exists map and the
   differentiability of realBirkhoffCartesian (landed G4042) (G6002Aux.cart_equiv).  See G6002_ROUTE.md (G1-094 edge). -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Common
open scoped ENNReal InnerProductSpace

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G6002 (u : PhysicalL2) :
  (∃ e : PhysicalL2 ≃L[ℝ] Lib.L2Z,
    e.toContinuousLinearMap = fderiv ℝ physicalBirkhoff u) ∧
  (∃ e : PhysicalL2 ≃L[ℝ] CartesianReal,
    e.toContinuousLinearMap = fderiv ℝ realBirkhoffCartesian u) := by
  have h1 : ∃ e : PhysicalL2 ≃L[ℝ] Lib.L2Z,
      e.toContinuousLinearMap = fderiv ℝ physicalBirkhoff u :=
    (G5016 u).2 (G6002Aux.adjoint_equiv (jacobianAdjoint u) (G6001 u) (G5015 u))
  exact ⟨h1, G6002Aux.cart_equiv u ((G4042.2.2 u (Set.mem_univ u)).differentiableAt) h1⟩

end
end NlsGge.GKDefinitionDesign
