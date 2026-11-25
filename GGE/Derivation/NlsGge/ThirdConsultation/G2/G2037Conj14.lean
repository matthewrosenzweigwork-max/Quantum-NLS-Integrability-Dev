import Mathlib
import NlsGge.ThirdConsultation.G2.G2037Host
import NlsGge.ThirdConsultation.G2.G2037Support1
import NlsGge.ThirdConsultation.G2.G2037Support2
import NlsGge.ThirdConsultation.G2.G2037Support3

/- G2-037 CONJUNCTS 1-4 ASSEMBLY (proof development, AUTHOR; not self-reviewed; SUPPORTING, not the head).
   Assembles conjuncts (1), (2), (3) and (4) of the head `G2_037` (STATEMENTS/G2.md, section G2-037;
   no later Pro round restates it) from
     S1: (1) the finite set, (2) analyticity off the cuts, (4a) integrability, (4b) zero period for n ∉ S;
     S2: (3) the discriminant-derivative identity on rootDomain38;
     S3: (4c) zero period for n ∈ S.
   The case split on `n ∈ S` supplies (4). No hypothesis is added. Conjunct (5) is NOT claimed. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory SummationFilter
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

/-- Conjuncts (1)-(4) of `G2_037`, with the finite set `S` of conjunct (1). -/
theorem g2037_conj_1_to_4 (u : PhysicalL2) (hfg : NlsGge.ThirdConsultation.finiteGap u) :
    ∃ S : Finset ℤ,
      (∀ n : ℤ, n ∈ S ↔ actualGapLowerAllE02_38 u n ≠ actualGapUpperAllE02_38 u n) ∧
      AnalyticOnNhd ℂ (finiteGapDifferential u S) (finiteGapCuts u S)ᶜ ∧
      (∀ z : ℂ, (realSlice u, z) ∈ rootDomain38 →
        deriv (discrim (realSlice u)) z / canonRoot38 (realSlice u) z =
          finiteGapDifferential u S z) ∧
      (∀ (C : ℤ → ℂ) (R : ℤ → ℝ), IsolatingFamily38 (realSlice u) C R →
        ∀ n : ℤ, CircleIntegrable (finiteGapDifferential u S) (C n) (R n) ∧
          circleIntegral (finiteGapDifferential u S) (C n) (R n) = 0) := by
  obtain ⟨S, hS⟩ := g2037s1_finite_mem u hfg
  refine ⟨S, hS, g2037s1_fgd_analyticOn u S, fun z hz => g2037s2_deriv_eq_fgd u S hS z hz, ?_⟩
  intro C R hCR n
  refine ⟨g2037s1_circleIntegrable u S C R hCR n, ?_⟩
  by_cases hn : n ∈ S
  · exact g2037s3_zero_period_open u S hS C R hCR n hn
  · exact g2037s1_zero_period_off u S C R hCR n hn

end
end NlsGge.GKDefinitionDesign
