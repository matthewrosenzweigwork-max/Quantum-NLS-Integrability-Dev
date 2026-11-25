import Mathlib
import NlsGge.ThirdConsultation.I.FiniteGapLaws
import NlsGge.Measure.GibbsVariational38
import NlsGge.Measure.CountableGaussian

/- I LIMIT-LAWS HOST01 (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/ThirdConsultation/I/LimitLaws.lean, namespace NlsGge.ThirdConsultation.I.
   Hosts ONLY sequenceRemainder, limitNormalizer, weightedSequenceLaw, physicalLaw; bodies verbatim from followup13
   DEFINITIONS/I.lean.md ("New convenience definitions"). grep NlsGge/ and Work/ (2026-11-02): none declared. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights

namespace NlsGge.ThirdConsultation.I

/-- A nonnegative everywhere-defined representative. I-024/025 and I-042 prove
    equality with the actual remainder on the respective probability-one sets.
    The max only chooses values where that equality has not yet been supplied. -/
def sequenceRemainder (W : ℝ → ℝ) (z : ℤ → ℂ) : ℝ :=
  max 0 (remainderForWeight W (physicalOfSequence z))

def limitNormalizer (W : ℝ → ℝ) : ℝ :=
  gibbsPartition38 (countableComplexGaussian (fun n : ℤ =>
    W (2 * Real.pi * (n : ℝ)))) (sequenceRemainder W)

def weightedSequenceLaw (W : ℝ → ℝ) : Measure (ℤ → ℂ) :=
  gibbsLaw38 (countableComplexGaussian (fun n : ℤ =>
    W (2 * Real.pi * (n : ℝ)))) (sequenceRemainder W)

def physicalLaw (W : ℝ → ℝ) : Measure PhysicalL2 :=
  (weightedSequenceLaw W).map physicalOfSequence

end NlsGge.ThirdConsultation.I
