import Mathlib
import NlsGge.Atomic.I.I027Core
import NlsGge.ThirdConsultation.I.ActualInverseBridge

/- I-027 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). GLUE (root main probe).
   Target NlsGge/Atomic/I/I027.lean, namespace NlsGge.ThirdConsultation.I.
   Head `i027` verbatim from followup13 STATEMENTS/I.md "## I-027".  Specializes the lane-checked core
   I027C.i027_of to PDE.actualBirkhoffTop38 through the round-14 bridge actual_inverse_eq_physicalOfSequence;
   no Birkhoff binder. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights
open NlsGge.SpectralFoundations
open NlsGge.Birkhoff NlsGge.Sobolev38 NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation

namespace NlsGge.ThirdConsultation.I

theorem i027 (lower upper : ℝ) (c : BoundedCoefficients lower upper)
    (Λ : ℕ → Finset ℤ) (hΛ : IsExhaustion38 Λ) :
    let W := weight c.val
    let ρ := fun z : ℤ → ℂ => Real.exp (-sequenceRemainder W z) / limitNormalizer W
    let ρN := fun (N : ℕ) (z : ℤ → ℂ) =>
      Real.exp (-remainderForWeight W (physicalOfSequence (projFin38 (Λ N) z))) /
        finiteRelativeNormalizer W (Λ N)
    (∀ N : ℕ, Integrable (fun z : ℤ → ℂ => |ρN N z - ρ z|)
      (fullWeightSequenceGaussian c.val)) ∧
    Tendsto (fun N : ℕ => ∫ z : ℤ → ℂ, |ρN N z - ρ z|
      ∂fullWeightSequenceGaussian c.val) atTop (𝓝 0) ∧
    (∀ᵐ u ∂physicalLaw W, ∀ n : ℤ, 0 < actualGapActionAllE02_38 u n) ∧
    ∀ S : Finset ℤ, (finiteGapLaw W S).MutuallySingular (physicalLaw W) :=
  NlsGge.ThirdConsultation.I027C.i027_of PDE.actualBirkhoffTop38 actual_inverse_eq_physicalOfSequence lower upper c Λ hΛ

end NlsGge.ThirdConsultation.I
