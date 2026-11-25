import Mathlib
import NlsGge.Atomic.G5.G5027
import NlsGge.Atomic.G5.G5028
import NlsGge.Atomic.G5.G5029Sup3
import NlsGge.Atomic.G5.G5029Sup4
import NlsGge.Atomic.G5.G5029Sup5
import NlsGge.Atomic.G5.G5029Sup6
import NlsGge.Atomic.G5.G5029Sup7Core

/- G5-029 PACKET (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/Atomic/G5/G5029.lean, namespace NlsGge.GKDefinitionDesign.
   Head `G5029` VERBATIM from followup12 STATEMENTS/G5.md section G5-029 (= PRO_DEFINITION_RESPONSE_FP80_14.md cluster 5,
   "G5029's complete retained head"; k, l unrestricted).  No lexical repair.
   Proof: G5029Sup7Aux.g5029_core (worker-lane compiled) with its hypotheses discharged by landed theorems:
     step 1 open_left_bracket_zero <- G5027, G5028, G5029Sup5 (approximation inside Iso(w), via G1-102), G5029Sup6
       ({mu,mu} = {lam,lam} = 0 via G1-073; psi continuity), G5028.mu_tendsto, G5029Sup4Aux.continuousAt_angleIntegralDerivative
       (G4041, betaSum_analyticOnNhd_sourceBetaW, G5020Aux.term_analytic), G5028.open_gap_lt;
     step 2 <- allDirichletLeft_openGaps_approximation (G5029Sup3, F = {k,l,m,n}) and continuousOn_angleIntegralBracket (G5029Sup4).
   No global inverse Birkhoff (G6) and no sourceFamily.XY_analytic field is used.  Closure exceeds the worker lane: root main probe needed. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G5029 (u : PhysicalL2) (k l m n : ℤ)
    (hleft : AllDirichletLeft u) (hm : gamma2 (realSlice u) m ≠ 0)
    (hn : gamma2 (realSlice u) n ≠ 0) :
  pairPoissonCLM (angleIntegralDerivative k m (realSlice u))
    (angleIntegralDerivative l n (realSlice u)) = 0 :=
  G5029Sup7Aux.g5029_core
    (fun w k' l' m' n' hw hk' hl' hm' hn' =>
      G5029Sup7Aux.open_left_bracket_zero G5027 G5028 G5029Sup5Aux.allLeft_interior_approx
        G5029Sup6Aux.pairPoisson_mu_mu G5029Sup6Aux.pairPoisson_lam_lam G5029Sup6Aux.psiAt_continuousAt
        NlsGge.Atomic.G5028.mu_tendsto
        (fun a b v hb => G5029Sup4Aux.continuousAt_angleIntegralDerivative a b v (G4041 b).1 (G4041 b).2
          (betaSum_analyticOnNhd_sourceBetaW b) (G5020Aux.term_analytic b a) hb)
        NlsGge.Atomic.G5028.open_gap_lt w k' l' m' n' hw hk' hl' hm' hn')
    allDirichletLeft_openGaps_approximation continuousOn_angleIntegralBracket u k l m n hleft hm hn

end
end NlsGge.GKDefinitionDesign
