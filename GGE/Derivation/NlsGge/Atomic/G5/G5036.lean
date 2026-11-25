import Mathlib
import NlsGge.Atomic.G5.G5031Host
import NlsGge.Atomic.G5.G5FlowBridge
import NlsGge.Atomic.G5.G5035
import NlsGge.Atomic.G5.G5035Sup2
import NlsGge.Atomic.G5.G5036Sup1
import NlsGge.Atomic.G1.G1081
import NlsGge.Atomic.G1.G1081Sup3

/- G5-036 PACKET (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/Atomic/G5/G5036.lean, namespace NlsGge.GKDefinitionDesign.
   Head `G5036` VERBATIM from followup12 STATEMENTS/G5.md section G5-036 (round 14 cluster 5 row G5-036: retain the IsSpectralFlow
   body; the head contains no `λ` token, no lexical repair).  `IsSpectralFlow` is hosted in the landed G5FlowBridge; `anglePoisson` in
   the landed G5031Host.
   Proof (GK 18.7, Pro round 14 cluster 5 §4): the IsSpectralFlow curve solves the physical single-gap ODE
   (G5036Sup1.isSpectralFlow_hasDerivAt), hence equals the complete flow singleGapFlow k · (c 0) of landed G1-081 by landed ODE
   uniqueness (G1081Sup3.singleGapField_global_unique), hence is isospectral (G1-081 last conjunct); then G5036Sup1.core36 with
   G5035Sup2.angle_local_primitive and G5035. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G5036 (k m n : ℤ) (c : ℝ → PhysicalL2)
    (hflow : IsSpectralFlow k c)
    (hm : gamma2 (realSlice (c 0)) m ≠ 0) (hn : gamma2 (realSlice (c 0)) n ≠ 0) :
  ∀ t : ℝ, gamma2 (realSlice (c t)) m ≠ 0 ∧ gamma2 (realSlice (c t)) n ≠ 0 ∧
    anglePoisson m n (realSlice (c t)) = anglePoisson m n (realSlice (c 0)) := by
  obtain ⟨-, hcomp, -, -, hiso⟩ := G1_081 k
  have hc : c = fun t => singleGapFlow k t (c 0) :=
    NlsGge.Atomic.G1081Sup3.singleGapField_global_unique k
      (G5036Sup1.isSpectralFlow_hasDerivAt k c hflow) (fun t => hcomp.2 (c 0) t)
      (hcomp.1 (c 0)).symm
  refine G5036Sup1.core36 k m n c hflow hm hn (fun t => ?_) G5035Sup2.angle_local_primitive
    (fun u m' n' hm' hn' => G5035 u m' n' hm' hn')
  have hct : c t = singleGapFlow k t (c 0) := congrFun hc t
  rw [hct]
  exact hiso t (c 0)

end
end NlsGge.GKDefinitionDesign
