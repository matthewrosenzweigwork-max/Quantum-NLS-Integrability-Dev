import NlsGge.Measure.FiniteScalarMoments
import NlsGge.Measure.CommonSourceLikelihoodFiniteAfterScalarPrerequisite
import NlsGge.Measure.CommonSourceLikelihoodL2Definitions
import NlsGge.Sobolev.CMWeightComparison

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators

namespace NlsGge.Measure

/-- The actual real-linear functional encoding the finite Cameron--Martin score.
It acts on finite random projections of the raw product sample; no assumption
that a typical raw sample belongs to a weighted Hilbert carrier is made. -/
def actualSourceCMFiniteScoreFunctional
    {lower upper : ℝ} (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (x : NlsGge.Pilot.WeightedRealHilbert (NlsGge.Pilot.cmModeWeight c)) :
    NlsGge.Pilot.FullWeightedHilbert c 0 →L[ℝ] ℝ :=
  (2 : ℝ) • innerSL ℝ
    (NlsGge.Pilot.cmToFullWeightedHilbert c 0 (by norm_num) x)

/-- Finite score as a random variable on the unchanged countable source law.
The public finite-scalar Gaussian theorem supplies its actual `L²` class. -/
def actualSourceCMFiniteScorePartial
    {lower upper : ℝ} (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (x : NlsGge.Pilot.WeightedRealHilbert (NlsGge.Pilot.cmModeWeight c))
    (N : ℕ) (z : ℤ → ℂ) : ℝ :=
  actualSourceCMFiniteScoreFunctional c x
    (fullWeightedSequencePartial c 0 N z)

noncomputable def actualSourceCMFiniteScorePartialLp
    {lower upper : ℝ} (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (x : NlsGge.Pilot.WeightedRealHilbert (NlsGge.Pilot.cmModeWeight c))
    (N : ℕ) : Lp ℝ 2 (fullWeightSequenceGaussian c.val) :=
  (hasGaussianLaw_fullWeightSequenceGaussian_partialScalar c 0 N
      (actualSourceCMFiniteScoreFunctional c x)).memLp_two.toLp
    (actualSourceCMFiniteScorePartial c x N)

end NlsGge.Measure
