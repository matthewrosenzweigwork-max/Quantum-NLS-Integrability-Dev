import NlsGge.Measure.CountableGaussian
import NlsGge.Sobolev.SourceWeighted
import NlsGge.Measure.ActualCountableGaussianFiniteRestriction
import Mathlib.Probability.ProductMeasure

set_option autoImplicit false
set_option pp.maxSteps 10000000
noncomputable section
open MeasureTheory

namespace NlsGge.Measure.WeightedGaussianFiniteRestrictionPrerequisiteV2

/-- Public finite-restriction map identity for the actual full source-rate
Gaussian law. -/
lemma fullWeightSequenceGaussian_map_restrict
    {lower upper : ℝ} (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (S : Finset ℤ) :
    (NlsGge.Measure.fullWeightSequenceGaussian c.val).map S.restrict =
      Measure.pi (fun i : S =>
        NlsGge.Measure.complexGaussian (NlsGge.Measure.fullWeightRate c.val i.1)) := by
  change (NlsGge.Measure.countableComplexGaussian
    (NlsGge.Measure.fullWeightRate c.val)).map S.restrict = _
  exact NlsGge.Measure.countableComplexGaussian_map_finiteRestriction
    (NlsGge.Measure.fullWeightRate c.val) S


/-- The set-restriction map and the finite-index restriction map are the same
coordinate function after coercing the finset to its carrier set. -/
lemma finset_restrict_eq_set_domRestrict (S : Finset ℤ) :
    (S.restrict : (ℤ → ℂ) → ((i : S) → ℂ)) =
      (Set.domRestrict (S : Set ℤ) : (ℤ → ℂ) → ((i : S) → ℂ)) := by
  funext z i
  rfl

/-- The actual source law pushed through the set-domRestrict spelling also has
the ordinary finite product law. -/
lemma fullWeightSequenceGaussian_map_domRestrict
    {lower upper : ℝ} (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (S : Finset ℤ) :
    (NlsGge.Measure.fullWeightSequenceGaussian c.val).map
        (Set.domRestrict (S : Set ℤ) : (ℤ → ℂ) → ((i : S) → ℂ)) =
      Measure.pi (fun i : S =>
        NlsGge.Measure.complexGaussian (NlsGge.Measure.fullWeightRate c.val i.1)) := by
  rw [← finset_restrict_eq_set_domRestrict S]
  exact fullWeightSequenceGaussian_map_restrict c S

#check @fullWeightSequenceGaussian_map_restrict
#check @finset_restrict_eq_set_domRestrict
#check @fullWeightSequenceGaussian_map_domRestrict

end NlsGge.Measure.WeightedGaussianFiniteRestrictionPrerequisiteV2
