import NlsGge.Atomic.G1.G1070
import NlsGge.GK38.PoissonMixedDiscriminantComplete

/- G1-071 PRODUCTION01 (proof development, AUTHOR; not reviewed). Target NlsGge/Atomic/G1/G1071.lean, namespace
   NlsGge.GKDefinitionDesign. Head from followup5 STATEMENTS/G1.md section G1-071, with lambda renamed lam.
   simpleDirichlet is the landed G1-070 predicate (NlsGge.Atomic.G1070.simpleDirichlet).
   Proof: production NlsGge.GK38.PoissonMixed38.discriminantDirichletMixedTarget, applied at z = muSeq phi n,
   zeta = lam, with the two conjuncts of simpleDirichlet. No hypothesis is added. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.GK38 NlsGge.GK38.GradEigen38 NlsGge.GK38.PoissonDirichlet38 NlsGge.GK38.PoissonMixed38
open NlsGge.Atomic.G1070

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G1_071 (φ : PotPair) (n : ℤ) (lam : ℂ)
    (hn : simpleDirichlet φ (muSeq φ n)) :
    Q (state φ (muSeq φ n) ![1,1]) ≠ 0 ∧
    2 * kernelPoisson38 (gradDiscrimCont38 φ lam)
      (dirEigenKernel38 φ (muSeq φ n)) =
      antiDiscrim φ (muSeq φ n) * dirInterpolation38 φ (muSeq φ n) lam :=
  NlsGge.GK38.PoissonMixed38.discriminantDirichletMixedTarget φ (muSeq φ n) lam hn.1 hn.2

end
end NlsGge.GKDefinitionDesign
