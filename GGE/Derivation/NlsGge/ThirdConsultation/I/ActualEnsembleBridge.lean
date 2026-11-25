import Mathlib
import NlsGge.Atomic.I.IEnsembleCore
import NlsGge.ThirdConsultation.I.ActualInverseBridge
import NlsGge.ThirdConsultation.PDE.ActualEnsemble

/- I ACTUAL-ENSEMBLE BRIDGES PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). GLUE (root main probe).
   Target NlsGge/ThirdConsultation/I/ActualEnsembleBridge.lean, namespace NlsGge.ThirdConsultation.I.
   Round-14 heads VERBATIM (followup13 STATEMENTS/I.md "Round-14 I/T/PDE/F bridges"): actual_finiteGapField_eq,
   actual_remainder_ae_eq, actual_ensemble_eq_I.  Each is the lane-checked B-generic core (IEnsC) specialised to
   PDE.actualBirkhoffTop38 through actual_inverse_eq_physicalOfSequence; PDE.finiteGapField / actualNu / actualMuW
   are the PDE.lean.md bodies hosted in PDE/ActualEnsemble (definitional unfolding only). -/
set_option autoImplicit false
open MeasureTheory
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights
open NlsGge.Birkhoff NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation

namespace NlsGge.ThirdConsultation.I

theorem actual_finiteGapField_eq (Λ : Finset ℤ) (w : Λ → ℂ) :
    PDE.finiteGapField Λ w = I.finiteGapField Λ w :=
  actual_inverse_eq_physicalOfSequence (extZero38 Λ w)

theorem actual_remainder_ae_eq
    (lo up : ℝ) (c : BoundedCoefficients lo up) :
    PDE.actualBirkhoffTop38.Rbar38 c.val =ᵐ[fullWeightSequenceGaussian c.val]
      I.sequenceRemainder (weight c.val) :=
  NlsGge.ThirdConsultation.IEnsC.remainder_ae_of PDE.actualBirkhoffTop38
    actual_inverse_eq_physicalOfSequence lo up c

theorem actual_ensemble_eq_I
    (lo up : ℝ) (c : BoundedCoefficients lo up) :
    PDE.actualBirkhoffTop38.ZW38 c.val = I.limitNormalizer (weight c.val) ∧
    PDE.actualBirkhoffTop38.muHatW38 c.val = I.weightedSequenceLaw (weight c.val) ∧
    PDE.actualMuW c.val = I.physicalLaw (weight c.val) ∧
    (∀ Λ : Finset ℤ,
      PDE.actualBirkhoffTop38.ZΛ38 c.val Λ =
        I.finiteRelativeNormalizer (weight c.val) Λ ∧
      PDE.actualBirkhoffTop38.nuHat38 c.val Λ =
        I.finiteGapCoordinateLaw (weight c.val) Λ ∧
      PDE.actualNu c.val Λ = I.finiteGapLaw (weight c.val) Λ) :=
  ⟨NlsGge.ThirdConsultation.IEnsC.ZW_eq_of PDE.actualBirkhoffTop38 actual_inverse_eq_physicalOfSequence lo up c,
    NlsGge.ThirdConsultation.IEnsC.muHat_eq_of PDE.actualBirkhoffTop38 actual_inverse_eq_physicalOfSequence lo up c,
    NlsGge.ThirdConsultation.IEnsC.muW_eq_of PDE.actualBirkhoffTop38 actual_inverse_eq_physicalOfSequence lo up c,
    fun Λ => NlsGge.ThirdConsultation.IEnsC.ensemble_finite_of PDE.actualBirkhoffTop38
      actual_inverse_eq_physicalOfSequence lo up c Λ⟩

end NlsGge.ThirdConsultation.I
