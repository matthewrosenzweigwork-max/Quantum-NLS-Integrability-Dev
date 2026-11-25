import NlsGge.Measure.WeightedProjectionMaskedTailDefinitions
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

set_option autoImplicit false
set_option pp.maxSteps 10000000
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace NlsGge.Measure.WeightedProjectionMaskedTailMarkovV3

/-- If the actual raw Gaussian expected masked energy is below a positive
threshold, then its strict-small-energy event has positive probability. This
is Markov's inequality on the complementary event. -/
lemma positive_raw_masked_energy_lt_of_lintegral_lt
    {lower upper : ℝ} (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (s : ℝ) (hs : (1 : ℝ) / 2 < s) (S : Finset ℤ)
    (ε : ℝ≥0∞) (hε0 : ε ≠ 0) (hεtop : ε ≠ ∞)
    (hsmall : (∫⁻ z : ℤ → ℂ,
      NlsGge.Measure.sequenceEnergy
        (NlsGge.Measure.WeightedProjectionMaskedTailContracts.maskedFullModeWeight c s S) z
        ∂NlsGge.Measure.fullWeightSequenceGaussian c.val) < ε) :
    0 < NlsGge.Measure.fullWeightSequenceGaussian c.val
      {z : ℤ → ℂ |
        NlsGge.Measure.sequenceEnergy
          (NlsGge.Measure.WeightedProjectionMaskedTailContracts.maskedFullModeWeight c s S) z < ε} := by
  let μ := NlsGge.Measure.fullWeightSequenceGaussian c.val
  let wS := NlsGge.Measure.WeightedProjectionMaskedTailContracts.maskedFullModeWeight c s S
  let f := NlsGge.Measure.sequenceEnergy wS
  let E := {z : ℤ → ℂ | f z < ε}
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  have hmeas : MeasurableSet E := by
    exact measurableSet_lt (measurable_sequenceEnergy wS) measurable_const
  have hbadset : Eᶜ = {z : ℤ → ℂ | ε ≤ f z} := by
    ext z
    simp [E, not_lt]
  have hmarkov : μ {z : ℤ → ℂ | ε ≤ f z} ≤
      (∫⁻ z, f z ∂μ) / ε :=
    MeasureTheory.meas_ge_le_lintegral_div
      (measurable_sequenceEnergy wS).aemeasurable hε0 hεtop
  have hmarkovMul : ε * μ {z : ℤ → ℂ | ε ≤ f z} ≤
      ∫⁻ z, f z ∂μ :=
    MeasureTheory.mul_meas_ge_le_lintegral (measurable_sequenceEnergy wS) ε
  have hbadlt : μ Eᶜ < 1 := by
    rw [hbadset]
    by_contra hnot
    have hge : 1 ≤ μ {z : ℤ → ℂ | ε ≤ f z} := not_lt.mp hnot
    have hlow : ε ≤ ε * μ {z : ℤ → ℂ | ε ≤ f z} := by
      calc
        ε = ε * 1 := (mul_one ε).symm
        _ ≤ ε * μ {z : ℤ → ℂ | ε ≤ f z} := by gcongr
    have hupper : ε * μ {z : ℤ → ℂ | ε ≤ f z} < ε := by
      exact hmarkovMul.trans_lt (by simpa [μ, f, wS] using hsmall)
    exact (not_lt_of_ge hlow) hupper
  by_contra hnot
  have hzero : μ E = 0 := le_antisymm (not_lt.mp hnot) bot_le
  have hsum := MeasureTheory.measure_add_measure_compl (μ := μ) hmeas
  have hcompl : μ Eᶜ = 1 := by
    simpa [hzero] using hsum
  rw [hcompl] at hbadlt
  exact (lt_irrefl 1) hbadlt

#check @positive_raw_masked_energy_lt_of_lintegral_lt

end NlsGge.Measure.WeightedProjectionMaskedTailMarkovV3
