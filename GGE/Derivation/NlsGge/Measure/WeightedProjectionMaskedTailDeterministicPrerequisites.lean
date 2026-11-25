import NlsGge.Measure.WeightedProjectionMaskedTailDefinitions

set_option autoImplicit false
set_option pp.maxSteps 10000000
noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators

namespace NlsGge.Measure.WeightedProjectionMaskedTailDeterministicPrerequisites

private abbrev maskWeight {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ) (S : Finset ℤ) :=
  NlsGge.Measure.WeightedProjectionMaskedTailContracts.maskedFullModeWeight c s S

private abbrev tailResidual {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ) (S : Finset ℤ)
    (x : NlsGge.Pilot.FullWeightedHilbert c s) :=
  NlsGge.Measure.WeightedProjectionMaskedTailContracts.weightedProjectionTailResidual c s S x

/-- The realified Hilbert tail has the expected pointwise coordinate mask. -/
lemma tailResidual_coordinate {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ) (S : Finset ℤ)
    (x : NlsGge.Pilot.FullWeightedHilbert c s) (n : ℤ) :
    (show NlsGge.Pilot.WeightedHilbert (NlsGge.Pilot.fullModeWeight c s) from
      tailResidual c s S x) n =
      if n ∈ S then 0 else
        (show NlsGge.Pilot.WeightedHilbert (NlsGge.Pilot.fullModeWeight c s) from x) n := by
  change
    (show NlsGge.Pilot.WeightedHilbert (NlsGge.Pilot.fullModeWeight c s) from x) n -
      (NlsGge.Pilot.weightedProjection (NlsGge.Pilot.fullModeWeight c s) S
        (show NlsGge.Pilot.WeightedHilbert (NlsGge.Pilot.fullModeWeight c s) from x) : ℤ → ℂ) n = _
  rw [NlsGge.Pilot.weightedProjection_apply]
  by_cases hn : n ∈ S <;> simp [hn]

/-- No probabilistic assumptions: the residual norm expands to the masked
Hilbert coefficient series. -/
lemma tailResidual_norm_sq_tsum {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ) (S : Finset ℤ)
    (x : NlsGge.Pilot.FullWeightedHilbert c s) :
    ‖tailResidual c s S x‖ ^ 2 =
      ∑' n : ℤ, maskWeight c s S n *
        ‖(show NlsGge.Pilot.WeightedHilbert (NlsGge.Pilot.fullModeWeight c s) from x) n‖ ^ 2 := by
  calc
    ‖tailResidual c s S x‖ ^ 2 =
        ∑' n : ℤ, NlsGge.Pilot.fullModeWeight c s n *
          ‖(show NlsGge.Pilot.WeightedHilbert (NlsGge.Pilot.fullModeWeight c s) from
            tailResidual c s S x) n‖ ^ 2 := by
          rw [NlsGge.Pilot.fullWeightedHilbert_norm_sq]
          apply tsum_congr
          intro n
          rfl
    _ = ∑' n : ℤ, maskWeight c s S n *
        ‖(show NlsGge.Pilot.WeightedHilbert (NlsGge.Pilot.fullModeWeight c s) from x) n‖ ^ 2 := by
          apply tsum_congr
          intro n
          by_cases hn : n ∈ S
          · simp [tailResidual_coordinate, maskWeight,
              NlsGge.Measure.WeightedProjectionMaskedTailContracts.maskedFullModeWeight, hn]
          · simp [tailResidual_coordinate, maskWeight,
              NlsGge.Measure.WeightedProjectionMaskedTailContracts.maskedFullModeWeight, hn]

/-- The finite mask preserves square summability of Hilbert coordinates. -/
lemma summable_maskedHilbertCoordinates {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ) (S : Finset ℤ)
    (x : NlsGge.Pilot.FullWeightedHilbert c s) :
    Summable (fun n : ℤ => maskWeight c s S n *
      ‖(show NlsGge.Pilot.WeightedHilbert (NlsGge.Pilot.fullModeWeight c s) from x) n‖ ^ 2) := by
  have hfull : Summable (fun n : ℤ =>
      NlsGge.Pilot.fullModeWeight c s n *
        ‖(show NlsGge.Pilot.WeightedHilbert (NlsGge.Pilot.fullModeWeight c s) from x) n‖ ^ 2) :=
    (NlsGge.Pilot.weightedHilbert_hasSum (NlsGge.Pilot.fullModeWeight c s)
      (show NlsGge.Pilot.WeightedHilbert (NlsGge.Pilot.fullModeWeight c s) from x)).summable
  have h := hfull.indicator (Sᶜ : Set ℤ)
  refine h.congr fun n => ?_
  by_cases hn : n ∈ S <;>
    simp [maskWeight,
      NlsGge.Measure.WeightedProjectionMaskedTailContracts.maskedFullModeWeight,
      Set.indicator, hn]

/-- ENNReal energy converts to the real coefficient series under its exact
nonnegativity and summability hypotheses. -/
lemma sequenceEnergy_toReal_eq_tsum (w : ℤ → ℝ) (z : ℤ → ℂ)
    (hw : ∀ n, 0 ≤ w n)
    (hs : Summable (fun n : ℤ => w n * ‖z n‖ ^ 2)) :
    (NlsGge.Measure.sequenceEnergy w z).toReal =
      ∑' n : ℤ, w n * ‖z n‖ ^ 2 := by
  have hnonneg (n : ℤ) : 0 ≤ w n * ‖z n‖ ^ 2 := mul_nonneg (hw n) (sq_nonneg _)
  rw [NlsGge.Measure.sequenceEnergy,
    ← ENNReal.ofReal_tsum_of_nonneg hnonneg hs,
    ENNReal.toReal_ofReal (tsum_nonneg hnonneg)]

#check @tailResidual_coordinate
#check @tailResidual_norm_sq_tsum
#check @summable_maskedHilbertCoordinates
#check @sequenceEnergy_toReal_eq_tsum

end NlsGge.Measure.WeightedProjectionMaskedTailDeterministicPrerequisites
