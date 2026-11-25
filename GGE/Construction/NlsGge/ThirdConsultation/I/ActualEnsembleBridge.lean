import Mathlib
import NlsGge.Atomic.I.IEnsembleCore
import NlsGge.ThirdConsultation.I.ActualInverseBridge
import NlsGge.ThirdConsultation.PDE.ActualEnsemble

                                                                                                                         
                                                                                                     
                                                                                                               
                                                                                                                
                                                                                                                  
                                                                                            
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
