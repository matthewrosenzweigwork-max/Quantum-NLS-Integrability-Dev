import NlsGge.Measure.PhysicalWeightedLaw

set_option autoImplicit false
set_option pp.all true
set_option pp.explicit true
set_option pp.universes true
set_option pp.fullNames true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators

namespace NlsGge.Measure.WeightedProjectionMaskedTailContracts

/-- Raw energy weights after removing the finite projected head. -/
def maskedFullModeWeight {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ)
    (S : Finset ℤ) : ℤ → ℝ :=
  fun n => if n ∈ S then 0 else NlsGge.Pilot.fullModeWeight c s n

/-- Actual E_s Hilbert residual after the finite coordinate projection. -/
def weightedProjectionTailResidual {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ)
    (S : Finset ℤ) (x : NlsGge.Pilot.FullWeightedHilbert c s) :
    NlsGge.Pilot.FullWeightedHilbert c s :=
  x - (show NlsGge.Pilot.FullWeightedHilbert c s from
    NlsGge.Pilot.weightedProjection (NlsGge.Pilot.fullModeWeight c s) S
      (show NlsGge.Pilot.WeightedHilbert (NlsGge.Pilot.fullModeWeight c s) from x))

/-- Target AE bridge: the actual Hilbert tail norm is the masked raw energy. -/
def ae_weightedProjectionTailResidual_sqNorm {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) (S : Finset ℤ) : Prop :=
  ∀ᵐ z ∂fullWeightSequenceGaussian c.val,
    ‖weightedProjectionTailResidual c s S
        (fullWeightedSequenceRealization c s z)‖ ^ 2 =
      (sequenceEnergy (maskedFullModeWeight c s S) z).toReal

/-- Quantitative raw-source target; the right side is the omitted Sobolev tail. -/
def rawMaskedTailSecondMoment {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) (S : Finset ℤ) : Prop :=
  (∫ z : ℤ → ℂ,
    (sequenceEnergy (maskedFullModeWeight c s S) z).toReal
      ∂fullWeightSequenceGaussian c.val) =
    ∑' n : {n : ℤ // n ∉ S},
      Real.rpow (NlsGge.Pilot.japaneseBracket n.1) (-2 * s)

/-- Desired actual Hilbert-law consequence of the AE bridge and raw moment. -/
def weightedProjectionTailSecondMoment {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) (S : Finset ℤ) : Prop :=
  (∫ x : NlsGge.Pilot.FullWeightedHilbert c s,
    ‖weightedProjectionTailResidual c s S x‖ ^ 2
      ∂fullWeightedSequenceGaussian c s) =
    ∑' n : {n : ℤ // n ∉ S},
      Real.rpow (NlsGge.Pilot.japaneseBracket n.1) (-2 * s)

#check @NlsGge.Measure.integral_sequenceEnergy_toReal
#check @NlsGge.Measure.fullWeightedSequenceRealization_sqNorm
#check @NlsGge.Measure.ae_fullWeightedSequenceRealization_sqNorm
#check @NlsGge.Measure.summable_fullModeWeight_div_rate
#check @NlsGge.Measure.WeightedProjectionMaskedTailContracts.ae_weightedProjectionTailResidual_sqNorm
#check @NlsGge.Measure.WeightedProjectionMaskedTailContracts.rawMaskedTailSecondMoment
#check @NlsGge.Measure.WeightedProjectionMaskedTailContracts.weightedProjectionTailSecondMoment

end NlsGge.Measure.WeightedProjectionMaskedTailContracts
