import NlsGge.Measure.CountableSupport
import NlsGge.Definitions.BorelWeighted
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators Topology

namespace NlsGge.Measure

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

lemma measurableSet_fullWeightedSequenceSupport {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ) :
    MeasurableSet {z : ℤ → ℂ |
      NlsGge.Pilot.WeightedSquareSummable (NlsGge.Pilot.sourceRate c) s z} := by
  simpa only [NlsGge.Pilot.WeightedSquareSummable, NlsGge.Pilot.fullModeWeight] using
    measurableSet_sequenceSummable (NlsGge.Pilot.fullModeWeight c s)
      (fun n => (NlsGge.Pilot.fullModeWeight_pos c s n).le)

def fullWeightedSequenceRealization {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ) (z : ℤ → ℂ) :
    NlsGge.Pilot.FullWeightedHilbert c s := by
  classical
  exact if hz : NlsGge.Pilot.WeightedSquareSummable (NlsGge.Pilot.sourceRate c) s z then
    (show NlsGge.Pilot.WeightedHilbert (NlsGge.Pilot.fullModeWeight c s) from
      ⟨z, (NlsGge.Pilot.fullWeightedHilbert_membership_iff c s z).2 hz⟩)
  else 0

lemma fullWeightedSequenceRealization_apply {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ) (z : ℤ → ℂ)
    (hz : NlsGge.Pilot.WeightedSquareSummable (NlsGge.Pilot.sourceRate c) s z) (n : ℤ) :
    (show NlsGge.Pilot.WeightedHilbert (NlsGge.Pilot.fullModeWeight c s) from
      fullWeightedSequenceRealization c s z) n = z n := by
  simp [fullWeightedSequenceRealization, hz]

def fullWeightedSequencePartial {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ) (N : ℕ) (z : ℤ → ℂ) :
    NlsGge.Pilot.FullWeightedHilbert c s :=
  (NlsGge.Pilot.weightedIsometry (NlsGge.Pilot.fullModeWeight c s)).symm
    (∑ n ∈ NlsGge.Pilot.symmetricModes N,
      lp.single 2 n (NlsGge.Pilot.weightedCoordinates (NlsGge.Pilot.fullModeWeight c s) z n))

lemma continuous_fullWeightedSequencePartial {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ) (N : ℕ) :
    Continuous (fullWeightedSequencePartial c s N) := by
  have hterm (n : ℤ) : Continuous (fun z : ℤ → ℂ =>
      lp.single (E := fun _ : ℤ => ℂ) 2 n
        (NlsGge.Pilot.weightedCoordinates (NlsGge.Pilot.fullModeWeight c s) z n)) := by
    have hc : Continuous (fun z : ℤ → ℂ =>
        NlsGge.Pilot.weightedCoordinates (NlsGge.Pilot.fullModeWeight c s) z n) :=
      continuous_const.mul (continuous_apply n)
    exact (lp.isometry_single (p := (2 : ℝ≥0∞)) (E := fun _ : ℤ => ℂ) n).continuous.comp hc
  have hsum : Continuous (fun z : ℤ → ℂ =>
      (∑ n ∈ NlsGge.Pilot.symmetricModes N,
        lp.single 2 n
          (NlsGge.Pilot.weightedCoordinates (NlsGge.Pilot.fullModeWeight c s) z n) :
        lp (fun _ : ℤ => ℂ) 2)) :=
    continuous_finsetSum (NlsGge.Pilot.symmetricModes N) (fun n _ => hterm n)
  exact (NlsGge.Pilot.weightedIsometry (NlsGge.Pilot.fullModeWeight c s)).symm.continuous.comp
    hsum

def fullWeightedSequenceApproximation {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ) (N : ℕ) (z : ℤ → ℂ) :
    NlsGge.Pilot.FullWeightedHilbert c s := by
  classical
  exact if NlsGge.Pilot.WeightedSquareSummable (NlsGge.Pilot.sourceRate c) s z then
    fullWeightedSequencePartial c s N z else 0

lemma measurable_fullWeightedSequenceApproximation {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ) (N : ℕ) :
    Measurable (fullWeightedSequenceApproximation c s N) := by
  classical
  exact Measurable.ite (measurableSet_fullWeightedSequenceSupport c s)
    (continuous_fullWeightedSequencePartial c s N).measurable measurable_const

lemma fullWeightedSequenceApproximation_tendsto {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ) (z : ℤ → ℂ) :
    Tendsto (fun N : ℕ => fullWeightedSequenceApproximation c s N z) atTop
      (𝓝 (fullWeightedSequenceRealization c s z)) := by
  classical
  by_cases hz : NlsGge.Pilot.WeightedSquareSummable (NlsGge.Pilot.sourceRate c) s z
  · have heq (N : ℕ) : fullWeightedSequencePartial c s N z =
        NlsGge.Pilot.weightedProjection (NlsGge.Pilot.fullModeWeight c s)
          (NlsGge.Pilot.symmetricModes N) (fullWeightedSequenceRealization c s z) := by
      unfold fullWeightedSequencePartial NlsGge.Pilot.weightedProjection
      apply congrArg (NlsGge.Pilot.weightedIsometry (NlsGge.Pilot.fullModeWeight c s)).symm
      apply Finset.sum_congr rfl
      intro n _
      apply congrArg (lp.single (E := fun _ : ℤ => ℂ) 2 n)
      change NlsGge.Pilot.weightedCoordinates (NlsGge.Pilot.fullModeWeight c s) z n =
        NlsGge.Pilot.weightedCoordinates (NlsGge.Pilot.fullModeWeight c s)
          (fun j => (show NlsGge.Pilot.WeightedHilbert (NlsGge.Pilot.fullModeWeight c s) from
            fullWeightedSequenceRealization c s z) j) n
      unfold NlsGge.Pilot.weightedCoordinates
      exact congrArg (fun value : ℂ =>
        (Real.sqrt (NlsGge.Pilot.fullModeWeight c s n) : ℂ) * value)
        (fullWeightedSequenceRealization_apply c s z hz n).symm
    have ht := NlsGge.Pilot.weightedProjection_tendsto (NlsGge.Pilot.fullModeWeight c s)
      (show NlsGge.Pilot.WeightedHilbert (NlsGge.Pilot.fullModeWeight c s) from
        fullWeightedSequenceRealization c s z)
    have ht' : Tendsto (fun N : ℕ =>
        (show NlsGge.Pilot.FullWeightedHilbert c s from
          NlsGge.Pilot.weightedProjection (NlsGge.Pilot.fullModeWeight c s)
            (NlsGge.Pilot.symmetricModes N) (fullWeightedSequenceRealization c s z))) atTop
          (𝓝 (fullWeightedSequenceRealization c s z)) := by
      convert! ht using 1
    simpa [fullWeightedSequenceApproximation, hz, heq] using
      ht'
  · simpa [fullWeightedSequenceApproximation, fullWeightedSequenceRealization, hz] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ =>
        (0 : NlsGge.Pilot.FullWeightedHilbert c s)) atTop (𝓝 0))

lemma measurable_fullWeightedSequenceRealization {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ) :
    Measurable (fullWeightedSequenceRealization c s) :=
  measurable_of_tendsto_metrizable (measurable_fullWeightedSequenceApproximation c s)
    (tendsto_pi_nhds.mpr (fullWeightedSequenceApproximation_tendsto c s))

lemma ae_fullWeightedSequenceRealization_apply {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) :
    ∀ᵐ z ∂fullWeightSequenceGaussian c.val, ∀ n : ℤ,
      (show NlsGge.Pilot.WeightedHilbert (NlsGge.Pilot.fullModeWeight c s) from
        fullWeightedSequenceRealization c s z) n = z n := by
  filter_upwards [ae_fullWeightSequenceGaussian_weighted lower upper c.val c.property.1
    (fun j => (c.property.2.2 j).1) (fun j => (c.property.2.2 j).2) s hs] with z hz
  exact fullWeightedSequenceRealization_apply c s z hz

def fullWeightedSequenceGaussian {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ) :
    MeasureTheory.Measure (NlsGge.Pilot.FullWeightedHilbert c s) :=
  (fullWeightSequenceGaussian c.val).map (fullWeightedSequenceRealization c s)

instance fullWeightedSequenceGaussian_probability {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ) :
    IsProbabilityMeasure (fullWeightedSequenceGaussian c s) where
  measure_univ := by
    unfold fullWeightedSequenceGaussian
    rw [Measure.map_apply (measurable_fullWeightedSequenceRealization c s) MeasurableSet.univ]
    simp

end NlsGge.Measure
