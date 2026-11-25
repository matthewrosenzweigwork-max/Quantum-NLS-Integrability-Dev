import NlsGge.Measure.PhysicalWeightedLaw
import NlsGge.Measure.WeightedGaussianOmittedTsumPrerequisiteV1
import NlsGge.Measure.WeightedProjectionMaskedTailDefinitions
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

set_option autoImplicit false
set_option pp.maxSteps 10000000
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace NlsGge.Measure.WeightedGaussianFiniteTailChoiceOrdinaryDefinitionsV1

/-- Exact masked-energy expectation under the actual raw product law, written
as the summable Sobolev tail over the omitted coordinates. -/
lemma lintegral_maskedTail_eq_subtype_tsum
    {lower upper : ℝ} (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (s : ℝ) (hs : (1 : ℝ) / 2 < s) (S : Finset ℤ) :
    (∫⁻ z : ℤ → ℂ,
      NlsGge.Measure.sequenceEnergy
        (NlsGge.Measure.WeightedProjectionMaskedTailContracts.maskedFullModeWeight c s S) z
      ∂NlsGge.Measure.fullWeightSequenceGaussian c.val) =
      ∑' n : {n : ℤ // n ∉ S},
        ENNReal.ofReal (Real.rpow (NlsGge.Pilot.japaneseBracket n.1) (-2 * s)) := by
  let wS := NlsGge.Measure.WeightedProjectionMaskedTailContracts.maskedFullModeWeight c s S
  have hrate (n : ℤ) : 0 < NlsGge.Measure.fullWeightRate c.val n :=
    NlsGge.Pilot.sourceRate_pos c n
  have hwS (n : ℤ) : 0 ≤ wS n := by
    by_cases hn : n ∈ S
    · simp [wS, NlsGge.Measure.WeightedProjectionMaskedTailContracts.maskedFullModeWeight, hn]
    · simp [wS, NlsGge.Measure.WeightedProjectionMaskedTailContracts.maskedFullModeWeight, hn]
      exact (NlsGge.Pilot.fullModeWeight_pos c s n).le
  have hratio (n : ℤ) :
      NlsGge.Pilot.fullModeWeight c s n / NlsGge.Measure.fullWeightRate c.val n =
        Real.rpow (NlsGge.Pilot.japaneseBracket n) (-2 * s) := by
    rw [NlsGge.Pilot.fullModeWeight, NlsGge.Measure.fullWeightRate]
    exact mul_div_cancel_left₀ _ (NlsGge.Pilot.sourceRate_pos c n).ne'
  have hsupp : Function.support
      (fun n : ℤ => ENNReal.ofReal (wS n / NlsGge.Measure.fullWeightRate c.val n)) ⊆
      {n : ℤ | n ∉ S} := by
    intro n hn
    by_contra hmem
    have hnS : n ∈ S := by simpa using hmem
    apply hn
    simp [wS,
      NlsGge.Measure.WeightedProjectionMaskedTailContracts.maskedFullModeWeight, hnS]
  unfold NlsGge.Measure.fullWeightSequenceGaussian
  rw [NlsGge.Measure.lintegral_sequenceEnergy (NlsGge.Measure.fullWeightRate c.val)
    wS hrate hwS]
  calc
    (∑' n : ℤ, ENNReal.ofReal (wS n / NlsGge.Measure.fullWeightRate c.val n)) =
        ∑' n : {n : ℤ // n ∉ S},
          ENNReal.ofReal (wS n.1 / NlsGge.Measure.fullWeightRate c.val n.1) :=
      NlsGge.Measure.WeightedGaussianOmittedTsumPrerequisiteV1.tsum_eq_subtype_of_support_subset
        {n : ℤ | n ∉ S} _ hsupp
    _ = ∑' n : {n : ℤ // n ∉ S},
        ENNReal.ofReal (Real.rpow (NlsGge.Pilot.japaneseBracket n.1) (-2 * s)) := by
      apply tsum_congr
      intro n
      simp [wS, NlsGge.Measure.WeightedProjectionMaskedTailContracts.maskedFullModeWeight,
        n.2, hratio]

/-- For every positive threshold, a sufficiently large symmetric coordinate
head leaves the actual raw Gaussian tail expectation below that threshold. -/
lemma exists_symmetric_tail_lintegral_lt
    {lower upper : ℝ} (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (s : ℝ) (hs : (1 : ℝ) / 2 < s) (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ N : ℕ,
      (∫⁻ z : ℤ → ℂ,
        NlsGge.Measure.sequenceEnergy
          (NlsGge.Measure.WeightedProjectionMaskedTailContracts.maskedFullModeWeight
            c s (NlsGge.Pilot.symmetricModes N)) z
        ∂NlsGge.Measure.fullWeightSequenceGaussian c.val) < ε := by
  let f : ℤ → ℝ≥0∞ := fun n => ENNReal.ofReal
    (Real.rpow (NlsGge.Pilot.japaneseBracket n) (-2 * s))
  have hreal := NlsGge.Measure.summable_japaneseBracket_sobolev_decay s hs
  have hfinite : (∑' n : ℤ, f n) ≠ ∞ := by
    exact hreal.tsum_ofReal_ne_top
  have htail := (ENNReal.tendsto_tsum_compl_atTop_zero hfinite).comp
    NlsGge.Pilot.symmetricModes_tendsto
  obtain ⟨N, hN⟩ := htail.eventually (Iio_mem_nhds hε) |>.exists
  refine ⟨N, ?_⟩
  rw [lintegral_maskedTail_eq_subtype_tsum c s hs (NlsGge.Pilot.symmetricModes N)]
  simpa [f] using hN

#check @lintegral_maskedTail_eq_subtype_tsum
#check @exists_symmetric_tail_lintegral_lt

end NlsGge.Measure.WeightedGaussianFiniteTailChoiceOrdinaryDefinitionsV1
