import NlsGge.Measure.CountableReconstruction
import NlsGge.Measure.WeightedProjectionMaskedTailDefinitions
import NlsGge.Measure.WeightedProjectionMaskedTailAEAssemblyV2
import NlsGge.Measure.WeightedProjectionMaskedTailMarkovV3
import NlsGge.Measure.WeightedGaussianFiniteHeadBoxPositivityAfterRestrictionV5
import NlsGge.Measure.WeightedGaussianPublicHeadTailEnergyFactorizationPrerequisiteV1
import NlsGge.Measure.WeightedGaussianCommonHeadSelectionV6
import NlsGge.Measure.WeightedProjectionFiniteHeadBoxNormBoundV2

set_option autoImplicit false
set_option pp.maxSteps 10000000
noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators Topology

namespace NlsGge.Measure.WeightedGaussianActualFullSupportAfterPrerequisitesV9

/-- Every nonempty open ball has positive measure under the actual weighted
Hilbert law. The proof uses the actual finite product head, the actual
head/complement independence, the actual masked-tail bound, and the AE
reconstruction into the weighted Hilbert carrier. -/
theorem actualWeightedGaussian_ball_pos
    {lower upper : ℝ} (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (s : ℝ) (hs : (1 : ℝ) / 2 < s)
    (x : NlsGge.Pilot.FullWeightedHilbert c s) (ε : ℝ) (hε : 0 < ε) :
    0 < NlsGge.Measure.fullWeightedSequenceGaussian c s (Metric.ball x ε) := by
  let δ : ℝ := ε / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨N, htargetTail, hrawTail⟩ :=
    NlsGge.Measure.WeightedGaussianCommonHeadSelectionV6.exists_symmetric_head_target_and_random_tail_small
      c s hs x δ hδ
  let S := NlsGge.Pilot.symmetricModes N
  let w := NlsGge.Pilot.fullModeWeight c s
  let xcoord : ℤ → ℂ := (show NlsGge.Pilot.WeightedHilbert w from x)
  let W : ℝ := ∑ n ∈ S, w n
  have hW : 0 ≤ W := by
    dsimp [W]
    apply Finset.sum_nonneg
    intro n hn
    exact (NlsGge.Pilot.fullModeWeight_pos c s n).le
  have hden : 0 < 1 + W := by positivity
  let r : ℝ := δ / (1 + W)
  have hr : 0 < r := div_pos hδ hden
  have hrad : r ^ 2 * W < δ ^ 2 := by
    dsimp [r]
    rw [div_pow, div_mul_eq_mul_div]
    apply (div_lt_iff₀ (sq_pos_of_pos hden)).2
    have hbase : W < (1 + W) ^ 2 := by nlinarith [sq_nonneg W]
    have hmul := mul_lt_mul_of_pos_left hbase (sq_pos_of_pos hδ)
    nlinarith
  let μ := NlsGge.Measure.fullWeightSequenceGaussian c.val
  let tailWeight := NlsGge.Measure.WeightedProjectionMaskedTailContracts.maskedFullModeWeight c s S
  let rawEnergy : (ℤ → ℂ) → ℝ≥0∞ := fun z => NlsGge.Measure.sequenceEnergy tailWeight z
  let H : Set ((i : S) → ℂ) :=
    Set.pi Set.univ (fun i => Metric.ball (xcoord i.1) r)
  let T : Set ℝ≥0∞ := Set.Iio (ENNReal.ofReal (δ ^ 2))
  have hH : MeasurableSet H := by
    dsimp [H]
    exact MeasurableSet.pi Set.countable_univ
      (fun i _ => Metric.isOpen_ball.measurableSet)
  have hT : MeasurableSet T := isOpen_Iio.measurableSet
  have hheadBox :
      0 < μ {z : ℤ → ℂ | ∀ i : S,
        ‖z i.1 - xcoord i.1‖ < r} := by
    exact NlsGge.Measure.WeightedGaussianFiniteHeadBoxPositivityAfterRestrictionV5.positive_raw_finite_head_box
      c S xcoord r hr
  have htailEvent :
      0 < μ {z : ℤ → ℂ | rawEnergy z < ENNReal.ofReal (δ ^ 2)} := by
    apply NlsGge.Measure.WeightedProjectionMaskedTailMarkovV3.positive_raw_masked_energy_lt_of_lintegral_lt
      c s hs S
      (ENNReal.ofReal (δ ^ 2)) (ne_of_gt (ENNReal.ofReal_pos.mpr (sq_pos_of_pos hδ)))
      ENNReal.ofReal_ne_top
    simpa [μ, rawEnergy, tailWeight] using hrawTail
  have hfactor := NlsGge.Measure.WeightedGaussianPublicHeadTailEnergyFactorizationPrerequisiteV1.measure_inter_preimage_head_tailEnergy_public
    c s S H T hH hT
  have hheadEventSet :
      {z : ℤ → ℂ | ∀ i : S, ‖z i.1 - xcoord i.1‖ < r} =
        (fun z : ℤ → ℂ => fun i : S => z i.1) ⁻¹' H := by
    ext z
    simp [H, Set.mem_pi, Metric.mem_ball, dist_eq_norm]
  have hfactorRaw :
      μ ({z : ℤ → ℂ | ∀ i : S,
          ‖z i.1 - xcoord i.1‖ < r} ∩
        {z : ℤ → ℂ | rawEnergy z < ENNReal.ofReal (δ ^ 2)}) =
      μ {z : ℤ → ℂ | ∀ i : S,
          ‖z i.1 - xcoord i.1‖ < r} *
      μ {z : ℤ → ℂ | rawEnergy z < ENNReal.ofReal (δ ^ 2)} := by
    rw [hheadEventSet]
    change (NlsGge.Measure.fullWeightSequenceGaussian c.val)
      (NlsGge.Measure.WeightedGaussianPublicHeadTailEnergyFactorizationPrerequisiteV1.headRestriction S ⁻¹' H ∩
        (fun z : ℤ → ℂ => rawEnergy z) ⁻¹' T) =
      (NlsGge.Measure.fullWeightSequenceGaussian c.val)
        (NlsGge.Measure.WeightedGaussianPublicHeadTailEnergyFactorizationPrerequisiteV1.headRestriction S ⁻¹' H) *
      (NlsGge.Measure.fullWeightSequenceGaussian c.val)
        ((fun z : ℤ → ℂ => rawEnergy z) ⁻¹' T)
    exact hfactor
  have hpositiveRaw :
      0 < μ ({z : ℤ → ℂ | ∀ i : S,
          ‖z i.1 - xcoord i.1‖ < r} ∩
        {z : ℤ → ℂ | rawEnergy z < ENNReal.ofReal (δ ^ 2)}) := by
    rw [hfactorRaw]
    exact ENNReal.mul_pos (ne_of_gt hheadBox) (ne_of_gt htailEvent)
  have hcoords := NlsGge.Measure.ae_fullWeightedSequenceRealization_apply c s hs
  have htailNorm := NlsGge.Measure.WeightedProjectionMaskedTailAEAssemblyV2.ae_weightedProjectionTailResidual_sqNorm
    c s hs S
  have hsubset :
      ({z : ℤ → ℂ | ∀ i : S,
          ‖z i.1 - xcoord i.1‖ < r} ∩
        {z : ℤ → ℂ | rawEnergy z < ENNReal.ofReal (δ ^ 2)}) ≤ᵐ[μ]
      (NlsGge.Measure.fullWeightedSequenceRealization c s) ⁻¹' Metric.ball x ε := by
    filter_upwards [hcoords, htailNorm] with z hzCoord hzTail
    intro hzEvents
    let y := NlsGge.Measure.fullWeightedSequenceRealization c s z
    let P (v : NlsGge.Pilot.FullWeightedHilbert c s) :
        NlsGge.Pilot.FullWeightedHilbert c s :=
      show NlsGge.Pilot.FullWeightedHilbert c s from
        NlsGge.Pilot.weightedProjection w S
          (show NlsGge.Pilot.WeightedHilbert w from v)
    have hyCoord (n : ℤ) : (show NlsGge.Pilot.WeightedHilbert w from y) n = z n :=
      hzCoord n
    have hrawHead : ∀ i : S, ‖z i.1 - xcoord i.1‖ < r := by
      simpa using hzEvents.1
    have hrawTail : rawEnergy z < ENNReal.ofReal (δ ^ 2) := hzEvents.2
    have hrealTail : (rawEnergy z).toReal < δ ^ 2 := by
      have hfinite : rawEnergy z ≠ ∞ :=
        ne_top_of_lt (hrawTail.trans ENNReal.ofReal_lt_top)
      have hfinite' : ENNReal.ofReal (δ ^ 2) ≠ ∞ := ENNReal.ofReal_ne_top
      have h := (ENNReal.toReal_lt_toReal hfinite hfinite').2 hrawTail
      simpa [ENNReal.toReal_ofReal (sq_nonneg δ)] using h
    have hyTail : ‖y - P y‖ < δ := by
      have hsquare := hzTail
      rw [show NlsGge.Measure.WeightedProjectionMaskedTailContracts.weightedProjectionTailResidual
          c s S y = y - P y by rfl] at hsquare
      have hsq : ‖y - P y‖ ^ 2 < δ ^ 2 := by
        rw [hsquare]
        simpa [rawEnergy, tailWeight] using hrealTail
      nlinarith [norm_nonneg (y - P y)]
    have hbox : ∀ n ∈ S,
        ‖((show NlsGge.Pilot.WeightedHilbert w from y) : ℤ → ℂ) n -
          ((show NlsGge.Pilot.WeightedHilbert w from x) : ℤ → ℂ) n‖ < r := by
      intro n hn
      simpa [xcoord, hyCoord n] using hrawHead ⟨n, hn⟩
    have hheadSq := NlsGge.Pilot.WeightedProjectionFiniteHeadBoxNormBoundV2.weightedProjection_diff_norm_sq_le
      w S
        (show NlsGge.Pilot.WeightedHilbert w from y)
        (show NlsGge.Pilot.WeightedHilbert w from x) r hr hbox
    have hyHead : ‖P y - P x‖ < δ := by
      have hsq : ‖P y - P x‖ ^ 2 < δ ^ 2 := by
        exact (hheadSq.trans_lt hrad)
      nlinarith [norm_nonneg (P y - P x)]
    have hxTail : ‖x - P x‖ < δ := by
      simpa [P, w] using htargetTail
    have hdecomp : y - x = (y - P y) + (P y - P x) + (P x - x) := by
      abel
    have hnorm : ‖y - x‖ ≤ ‖y - P y‖ + ‖P y - P x‖ + ‖P x - x‖ := by
      rw [hdecomp]
      calc
        ‖(y - P y) + (P y - P x) + (P x - x)‖ ≤
            ‖(y - P y) + (P y - P x)‖ + ‖P x - x‖ := norm_add_le _ _
        _ ≤ ‖y - P y‖ + ‖P y - P x‖ + ‖P x - x‖ := by
            gcongr
            exact norm_add_le _ _
    have hball : dist y x < ε := by
      rw [dist_eq_norm]
      have hxTail' : ‖P x - x‖ < δ := by simpa [norm_sub_rev] using hxTail
      dsimp [δ] at *
      linarith
    simpa [y] using hball
  have hprePos :
      0 < μ ((NlsGge.Measure.fullWeightedSequenceRealization c s) ⁻¹'
        Metric.ball x ε) := by
    exact lt_of_lt_of_le hpositiveRaw (measure_mono_ae hsubset)
  change 0 < (NlsGge.Measure.fullWeightSequenceGaussian c.val).map
    (NlsGge.Measure.fullWeightedSequenceRealization c s) (Metric.ball x ε)
  rw [Measure.map_apply (NlsGge.Measure.measurable_fullWeightedSequenceRealization c s)
    Metric.isOpen_ball.measurableSet]
  exact hprePos

#check @actualWeightedGaussian_ball_pos

end NlsGge.Measure.WeightedGaussianActualFullSupportAfterPrerequisitesV9
