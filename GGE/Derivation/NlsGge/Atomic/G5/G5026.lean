import Mathlib
import NlsGge.Atomic.G5.G5025
import NlsGge.Atomic.G2.G2075
import NlsGge.Atomic.G5.G5026Sup1

/- G5-026 PACKET (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/Atomic/G5/G5026.lean, namespace NlsGge.GKDefinitionDesign.
   Head `G5026` VERBATIM from followup12 STATEMENTS/G5.md section G5-026 (round 14 retains the head; no lexical repair needed).
   Proof: G5026Sup1.core26 with the landed G5025 (second conjunct) and the Abelian period clause of landed G2_075 at the
   real-slice point (realSlice u ∈ sourceW). -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G5026 (u : PhysicalL2) (m n : ℤ)
    (hn : gamma2 (realSlice u) n ≠ 0) :
  pairPoissonCLM (angleDerivative n (realSlice u))
    (fderiv ℂ (fun φ => gkActionC38 φ m) (realSlice u)) =
      if m = n then 1 else 0 :=
  G5026Sup1.core26 u n m (G5025 u n hn).2
    (((G2_075.2.2.2.2.1 n (realSlice u) (sourceFamily.W_real (Set.mem_range_self u))).2.1 m).2)

end
end NlsGge.GKDefinitionDesign
