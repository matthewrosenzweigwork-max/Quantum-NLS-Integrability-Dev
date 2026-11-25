import Mathlib
import NlsGge.GK38.GradFundamentalStar
import NlsGge.GK38.PoissonMixedNormingMutual
import NlsGge.Atomic.G1.G1067
import NlsGge.ThirdConsultation.G1.G1WronskianHost
import NlsGge.ThirdConsultation.G1.G1068Host

/- G1-068 PRODUCTION01 (proof development, AUTHOR; not reviewed). Target NlsGge/Atomic/G1/G1068.lean, namespace
   NlsGge.GKDefinitionDesign. Head VERBATIM from followup4 STATEMENTS/G1.md section G1-068 (no sign-dependent
   G1-067 input: the proof uses the same-potential Lemma 8.2 star identity, whose potential terms cancel in pairs).
   Route: ae_hasDerivAt_starIdentity38 (NlsGge/GK38/GradFundamentalStar) and intervalIntegrable_starBracket38,
   applied to the actual state solutions (state_isPairSolution38). No hypothesis beyond the head. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38 NlsGge.GK38.PoissonMixed38
open scoped BigOperators Matrix

namespace NlsGge.GKDefinitionDesign
noncomputable section


theorem G1068_solution_eq_state (φ : PotPair) (z : ℂ) (a : PairVec38) (s : ℝ) :
    solution φ z a s = pairKernelExt38 (state φ z a) s := by
  funext i
  rw [state_ext]
  simp only [solution, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have : ext38 (fundContP φ z) s = Set.IccExtend zero_le_one (fundPair φ z) s := rfl
  rw [this]
  ring

theorem G1068_isPairSolution (φ : PotPair) (z : ℂ) (a : PairVec38) :
    IsPairSolution38 φ z (fun s => solution φ z a s) := by
  have h : (fun s => solution φ z a s) = pairKernelExt38 (state φ z a) := by
    funext s
    exact G1068_solution_eq_state φ z a s
  rw [h]
  exact state_isPairSolution38 φ z a

theorem G1_068 (φ ψ : PotPair) (μ ν : ℂ) (hμν : μ ≠ ν)
    (a b c d : PairVec38) :
    IntervalIntegrable (fourSolutionWronskianRhs φ ψ μ ν a b c d) volume 0 1 ∧
    (∀ᵐ t ∂volume.restrict (Set.Ioo (0 : ℝ) 1),
      HasDerivAt
        (fun s : ℝ =>
          wedge (solution φ μ a s) (solution φ ν b s) *
          wedge (solution ψ μ c s) (solution ψ ν d s))
        (fourSolutionWronskianRhs φ ψ μ ν a b c d t) t)
 := by
  have ha := G1068_isPairSolution φ μ a
  have hb := G1068_isPairSolution φ ν b
  have hc := G1068_isPairSolution ψ μ c
  have hd := G1068_isPairSolution ψ ν d
  constructor
  · exact (intervalIntegrable_starBracket38 ha hb hc hd).const_mul (2 * Complex.I * (μ - ν))
  · exact (ae_restrict_iff' measurableSet_Ioo).2
      ((ae_hasDerivAt_starIdentity38 ha hb hc hd).mono fun s h hs => h ⟨hs.1.le, hs.2.le⟩)

end
end NlsGge.GKDefinitionDesign
