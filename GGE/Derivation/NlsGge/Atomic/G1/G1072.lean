import NlsGge.Atomic.G1.G1070
import NlsGge.Atomic.G1.G1073Host
import NlsGge.GK38.PoissonMixedDiscriminantComplete

/- G1-072 PRODUCTION01 (proof development, AUTHOR; not reviewed). Target NlsGge/Atomic/G1/G1072.lean, namespace
   NlsGge.GKDefinitionDesign. Head: STATEMENTS/G1.md section G1-072 (root/gpt6pro_followup7, no Pro round 6-9
   entry for G1-072 found by grep). Lexical repair only: the head's binder `λ` (a Lean keyword) is renamed
   `lam` and the hypothesis `hλ` is renamed `hlam`, as in landed G1-071 and G1-069.
   Predicates: simpleDirichlet (landed G1-070, NlsGge.Atomic.G1070.simpleDirichlet), simplePeriodic (landed
   G1-073 host G1073Host: perChar φ z = 0 ∧ deriv (perChar φ) z ≠ 0, verbatim Pro body).
   Proof: production NlsGge.GK38.PoissonMixed38.periodicDirichletMixedTarget (PoissonMixedDiscriminantComplete),
   applied at ζ = lam, z = muSeq φ n, with the two conjuncts of each predicate. No hypothesis is added.
   Prerequisites G1-071 and LIB-019 are accepted but not imported: the proof uses only the production
   periodic theorem above, so the import of G1-071 is dropped (mirror lacks it; not needed). -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.GK38 NlsGge.GK38.GradEigen38 NlsGge.GK38.PoissonDirichlet38 NlsGge.GK38.PoissonMixed38
open NlsGge.Atomic.G1070

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G1_072 (φ : PotPair) (n : ℤ) (lam : ℂ)
    (hlam : simplePeriodic φ lam)
    (hn : simpleDirichlet φ (muSeq φ n)) :
    deriv (discrim φ) lam ≠ 0 ∧
    2 * kernelPoisson38 (periodicKernel38 φ lam)
      (dirEigenKernel38 φ (muSeq φ n)) =
      -(antiDiscrim φ (muSeq φ n) * dirInterpolation38 φ (muSeq φ n) lam) /
        deriv (discrim φ) lam :=
  NlsGge.GK38.PoissonMixed38.periodicDirichletMixedTarget φ lam (muSeq φ n) hlam.1 hlam.2 hn.1 hn.2

end
end NlsGge.GKDefinitionDesign
