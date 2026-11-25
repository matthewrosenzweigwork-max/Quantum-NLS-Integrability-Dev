import NlsGge.Measure.ActualSourceCMFiniteScoreL2CauchyContractV1
import NlsGge.Measure.ActualSourceCMFiniteScoreShellPrerequisiteV2
import NlsGge.Measure.ActualSourceCMFiniteScoreCovariancePrerequisiteV2
import NlsGge.Measure.FiniteScalarMoments
import NlsGge.Measure.RealLp2RepresentativeCalculus

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace ENNReal

namespace NlsGge.Measure

private lemma actualSourceCMFiniteScoreShellVariance_v1
    {lower upper : ℝ} (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (x : NlsGge.Pilot.WeightedRealHilbert (NlsGge.Pilot.cmModeWeight c))
    (N M : ℕ) (hNM : N ≤ M) :
    ProbabilityTheory.variance
      (fun z : ℤ → ℂ => actualSourceCMFiniteScorePartial c x M z -
        actualSourceCMFiniteScorePartial c x N z)
      (fullWeightSequenceGaussian c.val) =
      ∑ n ∈ NlsGge.Pilot.symmetricModes M \ NlsGge.Pilot.symmetricModes N,
        NlsGge.Pilot.cmModeWeight c n *
          ‖(show NlsGge.Pilot.WeightedHilbert
            (NlsGge.Pilot.cmModeWeight c) from x) n‖ ^ 2 := by
  classical
  let S := NlsGge.Pilot.symmetricModes M \ NlsGge.Pilot.symmetricModes N
  let xS : NlsGge.Pilot.WeightedRealHilbert (NlsGge.Pilot.cmModeWeight c) :=
    NlsGge.Pilot.weightedProjection (NlsGge.Pilot.cmModeWeight c) S
      (show NlsGge.Pilot.WeightedHilbert (NlsGge.Pilot.cmModeWeight c) from x)
  rw [actualSourceCMFiniteScorePartial_shell_v1 c x N M hNM]
  change ProbabilityTheory.variance
      (fun z : ℤ → ℂ => actualSourceCMFiniteScoreFunctional c xS
        (fullWeightedSequencePartial c 0 M z))
      (fullWeightSequenceGaussian c.val) = _
  rw [variance_fullWeightSequenceGaussian_partialScalar]
  have hterm (n : ℤ) :
      fullWeightedDualCovarianceTerm c 0
        (actualSourceCMFiniteScoreFunctional c xS)
        (actualSourceCMFiniteScoreFunctional c xS) n =
      NlsGge.Pilot.cmModeWeight c n *
        ‖(show NlsGge.Pilot.WeightedHilbert
          (NlsGge.Pilot.cmModeWeight c) from xS) n‖ ^ 2 :=
    actualSourceCMFiniteScoreFunctional_covarianceTerm_v1 c xS n
  rw [show (fun n : ℤ => fullWeightedDualCovarianceTerm c 0
      (actualSourceCMFiniteScoreFunctional c xS)
      (actualSourceCMFiniteScoreFunctional c xS) n) =
      (fun n : ℤ => NlsGge.Pilot.cmModeWeight c n *
        ‖(show NlsGge.Pilot.WeightedHilbert
          (NlsGge.Pilot.cmModeWeight c) from xS) n‖ ^ 2) by
        funext n
        exact hterm n]
  have hSsub : S ⊆ NlsGge.Pilot.symmetricModes M := Finset.sdiff_subset
  rw [← Finset.sum_sdiff hSsub]
  have htail :
      (∑ n ∈ NlsGge.Pilot.symmetricModes M \ S,
        NlsGge.Pilot.cmModeWeight c n *
          ‖(show NlsGge.Pilot.WeightedHilbert
            (NlsGge.Pilot.cmModeWeight c) from xS) n‖ ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    simp only [Finset.mem_sdiff] at hn
    simp [xS, NlsGge.Pilot.weightedProjection_apply, hn.2]
  rw [htail, zero_add]
  apply Finset.sum_congr rfl
  intro n hn
  simp [S, xS, NlsGge.Pilot.weightedProjection_apply, hn]

/-- The squared distance between two actual finite-score L² classes is
exactly the Cameron--Martin energy in the intervening finite shell. -/
theorem actualSourceCMFiniteScoreCenteredL2ShellIdentity_v1
    {lower upper : ℝ} (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (x : NlsGge.Pilot.WeightedRealHilbert (NlsGge.Pilot.cmModeWeight c))
    (N M : ℕ) (hNM : N ≤ M) :
    ‖actualSourceCMFiniteScorePartialLp c x M -
      actualSourceCMFiniteScorePartialLp c x N‖ ^ 2 =
      ∑ n ∈ NlsGge.Pilot.symmetricModes M \ NlsGge.Pilot.symmetricModes N,
        NlsGge.Pilot.cmModeWeight c n *
          ‖(show NlsGge.Pilot.WeightedHilbert
            (NlsGge.Pilot.cmModeWeight c) from x) n‖ ^ 2 := by
  let μ := fullWeightSequenceGaussian c.val
  have hmemM : MemLp (actualSourceCMFiniteScorePartial c x M) 2 μ :=
    (hasGaussianLaw_fullWeightSequenceGaussian_partialScalar c 0 M
      (actualSourceCMFiniteScoreFunctional c x)).memLp_two
  have hmemN : MemLp (actualSourceCMFiniteScorePartial c x N) 2 μ :=
    (hasGaussianLaw_fullWeightSequenceGaussian_partialScalar c 0 N
      (actualSourceCMFiniteScoreFunctional c x)).memLp_two
  have hdiffMem : MemLp
      (fun z : ℤ → ℂ => actualSourceCMFiniteScorePartial c x M z -
        actualSourceCMFiniteScorePartial c x N z) 2 μ := hmemM.sub hmemN
  have hrep := toLp_sub_eq_of_memLp hmemM hmemN hdiffMem
  have hnorm := norm_sq_toLp_eq_integral_sq hdiffMem
  have hmeanM : ∫ z, actualSourceCMFiniteScorePartial c x M z ∂μ = 0 :=
    integral_fullWeightSequenceGaussian_partialScalar c 0 M
      (actualSourceCMFiniteScoreFunctional c x)
  have hmeanN : ∫ z, actualSourceCMFiniteScorePartial c x N z ∂μ = 0 :=
    integral_fullWeightSequenceGaussian_partialScalar c 0 N
      (actualSourceCMFiniteScoreFunctional c x)
  have hmeanD : ∫ z, (actualSourceCMFiniteScorePartial c x M z -
      actualSourceCMFiniteScorePartial c x N z) ∂μ = 0 := by
    rw [integral_sub (hmemM.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))
      (hmemN.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)), hmeanM, hmeanN]
    simp
  have hvar := variance_of_integral_eq_zero hdiffMem.aemeasurable hmeanD
  have hvarShell := actualSourceCMFiniteScoreShellVariance_v1 c x N M hNM
  rw [show actualSourceCMFiniteScorePartialLp c x M =
      hmemM.toLp (actualSourceCMFiniteScorePartial c x M) by rfl,
    show actualSourceCMFiniteScorePartialLp c x N =
      hmemN.toLp (actualSourceCMFiniteScorePartial c x N) by rfl,
    hrep, hnorm, ← hvar, hvarShell]

end NlsGge.Measure
