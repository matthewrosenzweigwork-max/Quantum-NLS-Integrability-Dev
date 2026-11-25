import NlsGge.Measure.CountableReconstruction

/-! Actual source-weighted Gaussian norm moments and physical reference law.
The norm is E_s, without Cameron-Martin factor2. Physical conclusions retain
1/2 < s < 3/4 and the actual minus-reflected Fourier inverse. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators

namespace NlsGge.Measure

lemma summable_fullModeWeight_div_rate {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) :
    Summable (fun n : ℤ => NlsGge.Pilot.fullModeWeight c s n / fullWeightRate c.val n) := by
  apply (summable_japaneseBracket_sobolev_decay s hs).congr
  intro n
  change Real.rpow (NlsGge.Pilot.japaneseBracket n) (-2 * s) =
    NlsGge.Pilot.sourceRate c n * Real.rpow (NlsGge.Pilot.japaneseBracket n) (-2 * s) /
      NlsGge.Pilot.sourceRate c n
  exact (mul_div_cancel_left₀ _ (NlsGge.Pilot.sourceRate_pos c n).ne').symm

lemma fullWeightedSequenceRealization_sqNorm {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ) (z : ℤ → ℂ)
    (hz : NlsGge.Pilot.WeightedSquareSummable (NlsGge.Pilot.sourceRate c) s z) :
    ‖fullWeightedSequenceRealization c s z‖ ^ 2 =
      (sequenceEnergy (NlsGge.Pilot.fullModeWeight c s) z).toReal := by
  have hsum : Summable (fun n : ℤ => NlsGge.Pilot.fullModeWeight c s n * ‖z n‖ ^ 2) := hz
  have hn : ∀ n : ℤ, 0 ≤ NlsGge.Pilot.fullModeWeight c s n * ‖z n‖ ^ 2 :=
    fun n => mul_nonneg (NlsGge.Pilot.fullModeWeight_pos c s n).le (sq_nonneg _)
  rw [sequenceEnergy, ← ENNReal.ofReal_tsum_of_nonneg hn hsum,
    ENNReal.toReal_ofReal (tsum_nonneg hn), NlsGge.Pilot.fullWeightedHilbert_norm_sq]
  apply tsum_congr
  intro n
  exact congrArg (fun value : ℂ =>
    NlsGge.Pilot.fullModeWeight c s n * ‖value‖ ^ 2)
    (fullWeightedSequenceRealization_apply c s z hz n)

lemma ae_fullWeightedSequenceRealization_sqNorm {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) :
    (fun z : ℤ → ℂ => ‖fullWeightedSequenceRealization c s z‖ ^ 2) =ᵐ[
      fullWeightSequenceGaussian c.val]
      (fun z => (sequenceEnergy (NlsGge.Pilot.fullModeWeight c s) z).toReal) := by
  filter_upwards [ae_fullWeightSequenceGaussian_weighted lower upper c.val c.property.1
    (fun j => (c.property.2.2 j).1) (fun j => (c.property.2.2 j).2) s hs] with z hz
  exact fullWeightedSequenceRealization_sqNorm c s z hz

lemma integrable_fullWeightedSequenceGaussian_sqNorm {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) :
    Integrable (fun z : NlsGge.Pilot.FullWeightedHilbert c s => ‖z‖ ^ 2)
      (fullWeightedSequenceGaussian c s) := by
  have hi := integrable_sequenceEnergy_toReal (fullWeightRate c.val)
    (NlsGge.Pilot.fullModeWeight c s) (fun n => NlsGge.Pilot.sourceRate_pos c n)
    (fun n => (NlsGge.Pilot.fullModeWeight_pos c s n).le)
    (summable_fullModeWeight_div_rate c s hs)
  unfold fullWeightedSequenceGaussian
  rw [integrable_map_measure (by fun_prop)
    (measurable_fullWeightedSequenceRealization c s).aemeasurable]
  exact hi.congr (ae_fullWeightedSequenceRealization_sqNorm c s hs).symm

lemma integral_fullWeightedSequenceGaussian_sqNorm {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) :
    (∫ z : NlsGge.Pilot.FullWeightedHilbert c s, ‖z‖ ^ 2 ∂fullWeightedSequenceGaussian c s) =
      ∑' n : ℤ, Real.rpow (NlsGge.Pilot.japaneseBracket n) (-2 * s) := by
  have _hi := integrable_fullWeightedSequenceGaussian_sqNorm c s hs
  unfold fullWeightedSequenceGaussian
  rw [integral_map (measurable_fullWeightedSequenceRealization c s).aemeasurable (by fun_prop),
    integral_congr_ae (ae_fullWeightedSequenceRealization_sqNorm c s hs)]
  unfold fullWeightSequenceGaussian
  rw [integral_sequenceEnergy_toReal (fullWeightRate c.val) (NlsGge.Pilot.fullModeWeight c s)
      (fun n => NlsGge.Pilot.sourceRate_pos c n)
      (fun n => (NlsGge.Pilot.fullModeWeight_pos c s n).le)
      (summable_fullModeWeight_div_rate c s hs)]
  apply tsum_congr
  intro n
  change NlsGge.Pilot.sourceRate c n *
    Real.rpow (NlsGge.Pilot.japaneseBracket n) (-2 * s) / NlsGge.Pilot.sourceRate c n = _
  exact mul_div_cancel_left₀ _ (NlsGge.Pilot.sourceRate_pos c n).ne'

def fullPhysicalWeightedSequenceRealization {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ) :
    (ℤ → ℂ) → NlsGge.Pilot.PhysicalWeighted c s :=
  (NlsGge.Pilot.physicalWeightedFourier c s).symm ∘ fullWeightedSequenceRealization c s

lemma measurable_fullPhysicalWeightedSequenceRealization {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ) :
    Measurable (fullPhysicalWeightedSequenceRealization c s) :=
  (NlsGge.Pilot.physicalWeightedFourier c s).symm.continuous.measurable.comp
    (measurable_fullWeightedSequenceRealization c s)

def fullWeightPhysicalWeightedGaussian {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ) :
    MeasureTheory.Measure (NlsGge.Pilot.PhysicalWeighted c s) :=
  (fullWeightedSequenceGaussian c s).map (NlsGge.Pilot.physicalWeightedFourier c s).symm

instance fullWeightPhysicalWeightedGaussian_probability {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ) :
    IsProbabilityMeasure (fullWeightPhysicalWeightedGaussian c s) where
  measure_univ := by
    unfold fullWeightPhysicalWeightedGaussian
    rw [Measure.map_apply (NlsGge.Pilot.physicalWeightedFourier c s).symm.continuous.measurable
      MeasurableSet.univ]
    simp

lemma fullWeightPhysicalWeightedGaussian_map_sequence {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ) :
    (fullWeightSequenceGaussian c.val).map (fullPhysicalWeightedSequenceRealization c s) =
      fullWeightPhysicalWeightedGaussian c s := by
  unfold fullPhysicalWeightedSequenceRealization fullWeightPhysicalWeightedGaussian
    fullWeightedSequenceGaussian
  exact (Measure.map_map (NlsGge.Pilot.physicalWeightedFourier c s).symm.continuous.measurable
    (measurable_fullWeightedSequenceRealization c s)).symm

lemma ae_fullPhysicalWeightedSequenceRealization_reflectedFourier {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) (_hsupper : s < (3 : ℝ) / 4) :
    ∀ᵐ z ∂fullWeightSequenceGaussian c.val, ∀ n : ℤ,
      NlsGge.Pilot.reflectedFourier (fullPhysicalWeightedSequenceRealization c s z).field n =
        z n := by
  filter_upwards [ae_fullWeightedSequenceRealization_apply c s hs] with z hz
  intro n
  calc
    NlsGge.Pilot.reflectedFourier (fullPhysicalWeightedSequenceRealization c s z).field n =
        (show NlsGge.Pilot.WeightedHilbert (NlsGge.Pilot.fullModeWeight c s) from
          NlsGge.Pilot.physicalWeightedFourier c s
            (fullPhysicalWeightedSequenceRealization c s z)) n :=
      (NlsGge.Pilot.physicalWeightedFourier_apply c s _ n).symm
    _ = (show NlsGge.Pilot.WeightedHilbert (NlsGge.Pilot.fullModeWeight c s) from
        fullWeightedSequenceRealization c s z) n := by
      unfold fullPhysicalWeightedSequenceRealization
      rw [Function.comp_apply, LinearIsometryEquiv.apply_symm_apply]
    _ = z n := hz n

lemma integrable_fullWeightPhysicalWeightedGaussian_sqNorm {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) (_hsupper : s < (3 : ℝ) / 4) :
    Integrable (fun u : NlsGge.Pilot.PhysicalWeighted c s => ‖u‖ ^ 2)
      (fullWeightPhysicalWeightedGaussian c s) := by
  unfold fullWeightPhysicalWeightedGaussian
  rw [integrable_map_measure (by fun_prop)
    (NlsGge.Pilot.physicalWeightedFourier c s).symm.continuous.measurable.aemeasurable]
  convert! integrable_fullWeightedSequenceGaussian_sqNorm c s hs using 1
  funext x
  rw [Function.comp_apply, (NlsGge.Pilot.physicalWeightedFourier c s).symm.norm_map]

lemma integral_fullWeightPhysicalWeightedGaussian_sqNorm {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) (hsupper : s < (3 : ℝ) / 4) :
    (∫ u : NlsGge.Pilot.PhysicalWeighted c s, ‖u‖ ^ 2
      ∂fullWeightPhysicalWeightedGaussian c s) =
      ∑' n : ℤ, Real.rpow (NlsGge.Pilot.japaneseBracket n) (-2 * s) := by
  have _hi := integrable_fullWeightPhysicalWeightedGaussian_sqNorm c s hs hsupper
  unfold fullWeightPhysicalWeightedGaussian
  rw [integral_map
    (NlsGge.Pilot.physicalWeightedFourier c s).symm.continuous.measurable.aemeasurable
    (by fun_prop)]
  simp_rw [(NlsGge.Pilot.physicalWeightedFourier c s).symm.norm_map]
  exact integral_fullWeightedSequenceGaussian_sqNorm c s hs

end NlsGge.Measure
