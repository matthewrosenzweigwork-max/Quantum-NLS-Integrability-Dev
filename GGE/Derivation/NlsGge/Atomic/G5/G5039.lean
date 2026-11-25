import Mathlib
import NlsGge.Atomic.G5.G5039Sup1Core
import NlsGge.Atomic.G4.G4041
import NlsGge.Atomic.G5.G5025Sup3
import NlsGge.Atomic.G5.G5017
import NlsGge.Atomic.G5.G5026
import NlsGge.Atomic.G5.G5038

/- G5-039 PACKET (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/Atomic/G5/G5039.lean, namespace NlsGge.GKDefinitionDesign.
   Head `G5039` VERBATIM from followup12 STATEMENTS/G5.md section G5-039 (round 14 cluster 5 retains unrestricted indices).
   No lexical repair.
   Proof (GK Theorem 18.8 chain rule on the open-gap chart): G5039Aux.core39 (G5039Sup1Core) with
   dI = X dX + Y dY from G4043 via G5039Aux.fderiv_action_eq (differentiability from landed G4041),
   X^2+Y^2 != 0 from landed G5025Sup3.radius_ne_zero, {I_a,I_b} = 0 from landed G5017,
   {theta_a,I_b} = delta from landed G5026, {theta_m,theta_n} = 0 from G5038. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G5039 (u : PhysicalL2) (m n : ℤ)
    (hm : gamma2 (realSlice u) m ≠ 0) (hn : gamma2 (realSlice u) n ≠ 0) :
  pairPoisson (cartesianX m) (cartesianX n) (realSlice u) = 0 ∧
  pairPoisson (cartesianX m) (cartesianY n) (realSlice u) =
    -(if m = n then (1 : ℂ) else 0) ∧
  pairPoisson (cartesianY m) (cartesianY n) (realSlice u) = 0 := by
  have hB : realSlice u ∈ sourceBetaW := sourceFamily.V_real (Set.mem_range_self u)
  refine G5039Aux.core39 (realSlice u) m n
    (fun j => G5039Aux.fderiv_action_eq j _ hB (((G4041 j).1 _ hB).differentiableAt)
      (((G4041 j).2 _ hB).differentiableAt))
    (G5025Sup3.radius_ne_zero u m hm) (G5025Sup3.radius_ne_zero u n hn)
    (fun a b => G5017 u a b) ?_ (G5038 u m n hm hn)
  intro a b hab
  rcases hab with rfl | rfl
  · exact G5026 u b a hm
  · exact G5026 u b a hn

end
end NlsGge.GKDefinitionDesign
