import NlsGge.Measure.CountableGaussian
import NlsGge.Sobolev.SourceWeighted
import NlsGge.Sobolev.WeightedHilbert
import NlsGge.Measure.WeightedProjectionMaskedTailDefinitions
import NlsGge.Measure.WeightedGaussianFiniteTailChoiceOrdinaryDefinitionsV1
import NlsGge.Measure.WeightedGaussianFullWeightedProjectionDistanceBridgeV1

set_option autoImplicit false
set_option pp.maxSteps 10000000
noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators

namespace NlsGge.Measure.WeightedGaussianCommonHeadSelectionV6

/-- The masked raw energy expectation decreases when the symmetric head grows. -/
lemma maskedTail_lintegral_mono_symmetric
    {lower upper : ℝ} (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (s : ℝ) (N M : ℕ) (hNM : N ≤ M) :
    (∫⁻ z : ℤ → ℂ,
      NlsGge.Measure.sequenceEnergy
        (NlsGge.Measure.WeightedProjectionMaskedTailContracts.maskedFullModeWeight
          c s (NlsGge.Pilot.symmetricModes M)) z
      ∂NlsGge.Measure.fullWeightSequenceGaussian c.val) ≤
    (∫⁻ z : ℤ → ℂ,
      NlsGge.Measure.sequenceEnergy
        (NlsGge.Measure.WeightedProjectionMaskedTailContracts.maskedFullModeWeight
          c s (NlsGge.Pilot.symmetricModes N)) z
      ∂NlsGge.Measure.fullWeightSequenceGaussian c.val) := by
  have hsub : NlsGge.Pilot.symmetricModes N ⊆ NlsGge.Pilot.symmetricModes M := by
    intro n hn
    simp only [NlsGge.Pilot.symmetricModes, Finset.mem_Icc] at hn ⊢
    omega
  have hweight (n : ℤ) :
      NlsGge.Measure.WeightedProjectionMaskedTailContracts.maskedFullModeWeight
          c s (NlsGge.Pilot.symmetricModes M) n ≤
        NlsGge.Measure.WeightedProjectionMaskedTailContracts.maskedFullModeWeight
          c s (NlsGge.Pilot.symmetricModes N) n := by
    by_cases hn : n ∈ NlsGge.Pilot.symmetricModes N
    · have hm : n ∈ NlsGge.Pilot.symmetricModes M := hsub hn
      simp [NlsGge.Measure.WeightedProjectionMaskedTailContracts.maskedFullModeWeight, hn, hm]
    · by_cases hm : n ∈ NlsGge.Pilot.symmetricModes M
      · simp [NlsGge.Measure.WeightedProjectionMaskedTailContracts.maskedFullModeWeight, hn, hm]
        exact (NlsGge.Pilot.fullModeWeight_pos c s n).le
      · simp [NlsGge.Measure.WeightedProjectionMaskedTailContracts.maskedFullModeWeight, hn, hm]
  apply lintegral_mono
  intro z
  unfold NlsGge.Measure.sequenceEnergy
  apply ENNReal.tsum_le_tsum
  intro n
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right (hweight n) (sq_nonneg ‖z n‖)

/-- Choose one symmetric finite head that simultaneously approximates the
deterministic target in the actual weighted Hilbert norm and makes the actual
raw masked-tail expectation small. The larger head preserves the tail bound by
the preceding pointwise monotonicity theorem. -/
lemma exists_symmetric_head_target_and_random_tail_small
    {lower upper : ℝ} (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (s : ℝ) (hs : (1 : ℝ) / 2 < s)
    (x : NlsGge.Pilot.FullWeightedHilbert c s) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ,
      ‖x - (show NlsGge.Pilot.FullWeightedHilbert c s from
        NlsGge.Pilot.weightedProjection (NlsGge.Pilot.fullModeWeight c s)
          (NlsGge.Pilot.symmetricModes N) (show NlsGge.Pilot.WeightedHilbert
            (NlsGge.Pilot.fullModeWeight c s) from x))‖ < δ ∧
      (∫⁻ z : ℤ → ℂ,
        NlsGge.Measure.sequenceEnergy
          (NlsGge.Measure.WeightedProjectionMaskedTailContracts.maskedFullModeWeight
            c s (NlsGge.Pilot.symmetricModes N)) z
        ∂NlsGge.Measure.fullWeightSequenceGaussian c.val) < ENNReal.ofReal (δ ^ 2) := by
  obtain ⟨N₀, hN₀⟩ :=
    NlsGge.Measure.WeightedGaussianFiniteTailChoiceOrdinaryDefinitionsV1.exists_symmetric_tail_lintegral_lt
    c s hs (ENNReal.ofReal (δ ^ 2))
    (ENNReal.ofReal_pos.mpr (sq_pos_of_pos hδ))
  have hproj := NlsGge.Pilot.weightedProjection_tendsto
    (NlsGge.Pilot.fullModeWeight c s) (show NlsGge.Pilot.WeightedHilbert
      (NlsGge.Pilot.fullModeWeight c s) from x)
  have hprojEventually : ∀ᶠ N : ℕ in atTop,
      ‖x - (show NlsGge.Pilot.FullWeightedHilbert c s from
        NlsGge.Pilot.weightedProjection (NlsGge.Pilot.fullModeWeight c s)
          (NlsGge.Pilot.symmetricModes N) (show NlsGge.Pilot.WeightedHilbert
            (NlsGge.Pilot.fullModeWeight c s) from x))‖ < δ := by
    have hball := hproj.eventually (Metric.ball_mem_nhds _ hδ)
    filter_upwards [hball] with N hN
    rw [NlsGge.Measure.WeightedGaussianFullWeightedProjectionDistanceBridgeV1.projection_distance_eq_fullWeighted_norm
      c s x (NlsGge.Pilot.symmetricModes N)] at hN
    exact hN
  obtain ⟨N, hNproj, hNge⟩ :=
    (hprojEventually.and (eventually_ge_atTop N₀)).exists
  refine ⟨N, hNproj, ?_⟩
  calc
    (∫⁻ z : ℤ → ℂ,
      NlsGge.Measure.sequenceEnergy
        (NlsGge.Measure.WeightedProjectionMaskedTailContracts.maskedFullModeWeight
          c s (NlsGge.Pilot.symmetricModes N)) z
      ∂NlsGge.Measure.fullWeightSequenceGaussian c.val) ≤
      (∫⁻ z : ℤ → ℂ,
        NlsGge.Measure.sequenceEnergy
          (NlsGge.Measure.WeightedProjectionMaskedTailContracts.maskedFullModeWeight
            c s (NlsGge.Pilot.symmetricModes N₀)) z
        ∂NlsGge.Measure.fullWeightSequenceGaussian c.val) :=
          maskedTail_lintegral_mono_symmetric c s N₀ N hNge
    _ < ENNReal.ofReal (δ ^ 2) := hN₀

#check @maskedTail_lintegral_mono_symmetric
#check @exists_symmetric_head_target_and_random_tail_small

end NlsGge.Measure.WeightedGaussianCommonHeadSelectionV6
