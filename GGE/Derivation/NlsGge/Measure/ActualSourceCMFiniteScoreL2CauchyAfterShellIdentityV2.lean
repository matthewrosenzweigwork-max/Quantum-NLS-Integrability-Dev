import NlsGge.Measure.ActualSourceCMFiniteScoreCenteredL2ShellIdentityV1
import NlsGge.Measure.CommonSourceLikelihoodL2CauchyAfterRepresentativePrerequisite

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators

namespace NlsGge.Measure

/-- The actual source Cameron--Martin finite scores converge in the unchanged
countable-product `L²` space. This assembly uses the proved shell norm identity
and actual CM-energy summability, with no typical-sample Hilbert coercion. -/
theorem actualSourceCMFiniteScoreL2Cauchy_afterShellIdentity_v1
    {lower upper : ℝ} (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (x : NlsGge.Pilot.WeightedRealHilbert (NlsGge.Pilot.cmModeWeight c)) :
    CauchySeq (fun N : ℕ => actualSourceCMFiniteScorePartialLp c x N) := by
  let f : ℤ → ℝ := fun n => NlsGge.Pilot.cmModeWeight c n *
    ‖actualSourceCMSequence c x n‖ ^ 2
  have henergy : Summable f := by
    simpa [f] using actualSourceCMSequenceEnergySummable c x
  have hE := (henergy.hasSum).comp NlsGge.Pilot.symmetricModes_tendsto
  let Q := ∑' n : ℤ, f n
  let E : ℕ → ℝ := fun N =>
    ∑ n ∈ NlsGge.Pilot.symmetricModes N, f n
  have hEtendsto : Tendsto E atTop (nhds Q) := by
    simpa only [E, Q, f, Function.comp_def] using hE
  rw [Metric.cauchySeq_iff']
  intro ε hε
  let δ := ε ^ 2 / 8
  have hδ : 0 < δ := by positivity
  have hev : ∀ᶠ k : ℕ in atTop, dist (E k) Q < δ :=
    hEtendsto.eventually (Metric.ball_mem_nhds Q hδ)
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.1 hev
  refine ⟨K, ?_⟩
  intro m hm
  have hsubset : NlsGge.Pilot.symmetricModes K ⊆ NlsGge.Pilot.symmetricModes m := by
    intro n hn
    simp only [NlsGge.Pilot.symmetricModes, Finset.mem_Icc] at hn ⊢
    omega
  have henergyDiff : E m - E K =
      ∑ n ∈ NlsGge.Pilot.symmetricModes m \ NlsGge.Pilot.symmetricModes K, f n := by
    dsimp [E, f]
    rw [← Finset.sum_sdiff hsubset]
    ring
  have hdistSq :
      dist (actualSourceCMFiniteScorePartialLp c x m)
        (actualSourceCMFiniteScorePartialLp c x K) ^ 2 = E m - E K := by
    calc
      dist (actualSourceCMFiniteScorePartialLp c x m)
          (actualSourceCMFiniteScorePartialLp c x K) ^ 2 =
        ‖actualSourceCMFiniteScorePartialLp c x m -
          actualSourceCMFiniteScorePartialLp c x K‖ ^ 2 := by rw [dist_eq_norm]
      _ = ∑ n ∈ NlsGge.Pilot.symmetricModes m \ NlsGge.Pilot.symmetricModes K, f n := by
        simpa [f, NlsGge.Measure.actualSourceCMSequence] using
          actualSourceCMFiniteScoreCenteredL2ShellIdentity_v1 c x K m (by omega)
      _ = E m - E K := henergyDiff.symm
  have hEm : dist (E m) Q < δ := hK m hm
  have hEK : dist (E K) Q < δ := hK K le_rfl
  have hAbs : |E m - E K| < 2 * δ := by
    have hm' : |E m - Q| < δ := by simpa [Real.dist_eq] using hEm
    have hK' : |Q - E K| < δ := by
      simpa [Real.dist_eq, abs_sub_comm] using hEK
    calc
      |E m - E K| = |(E m - Q) + (Q - E K)| := by congr 1 <;> ring
      _ ≤ |E m - Q| + |Q - E K| := abs_add_le _ _
      _ < δ + δ := add_lt_add hm' hK'
      _ = 2 * δ := by ring
  have hdistSqLt :
      dist (actualSourceCMFiniteScorePartialLp c x m)
        (actualSourceCMFiniteScorePartialLp c x K) ^ 2 < ε ^ 2 := by
    rw [hdistSq]
    calc
      E m - E K ≤ |E m - E K| := le_abs_self _
      _ < 2 * δ := hAbs
      _ = ε ^ 2 / 4 := by simp [δ]; ring
      _ < ε ^ 2 := by nlinarith
  have hdist :
      dist (actualSourceCMFiniteScorePartialLp c x m)
        (actualSourceCMFiniteScorePartialLp c x K) < ε := by
    have hnonneg : 0 ≤ dist (actualSourceCMFiniteScorePartialLp c x m)
        (actualSourceCMFiniteScorePartialLp c x K) := dist_nonneg
    nlinarith [sq_nonneg
      (dist (actualSourceCMFiniteScorePartialLp c x m)
        (actualSourceCMFiniteScorePartialLp c x K) - ε)]
  exact hdist

end NlsGge.Measure
