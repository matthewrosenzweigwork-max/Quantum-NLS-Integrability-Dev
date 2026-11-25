import NlsGge.Spectral.ActualSourceWeightedDomainLInfRepresentativeMatchesSourceV5
import NlsGge.Spectral.ActualSourceWeightedDomainPerturbedImaginaryRangeAlgebraV7
import NlsGge.Spectral.ActualSourceWeightedDomainPotentialInterfaceAfterAEV1
import NlsGge.Spectral.ActualL2PotentialParityPairSourceOperatorV2

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory

namespace NlsGge.Schur
open NlsGge.Pilot
open TransportBridgeV4

/-- Public-measure form of the source weighted-domain L∞/L² representative
identity, with the exact recovered-domain sequence map used by the potential. -/
theorem actualSourceWeightedDomainRepresentative_matches_source_ae
    (n : ℤ) (x : recoveredActualSourceFreeWeightedDomain n) (upper : Bool) :
    (actualSourceWeightedDomainLInfRepresentativeMap n
      (recoveredActualSourceWeightedDomainSequenceMapAfterAE n x) upper : ℝ → ℂ) =ᵐ[
        volume.restrict (Set.Ioc (0 : ℝ) 1)] (x.val upper : ℝ → ℂ) := by
  change (actualSourceWeightedDomainLInfRepresentativeMap n
      ⟨(sourcePairRepr n).toLinearEquiv x.val, x.property⟩ upper : ℝ → ℂ) =ᵐ[
        volume.restrict (Set.Ioc (0 : ℝ) 1)] (x.val upper : ℝ → ℂ)
  have h := actualSourceWeightedDomainLInfRepresentativeMap_matches_source_ae n x upper
  convert h using 1 <;> rfl

/-- The source-domain potential linear map evaluates to the actual bounded
source-pair L² multiplier on the corresponding continuous representative. -/
theorem actualSourcePotentialOnRecoveredWeightedDomain_apply
    (n : ℤ) (u₁ u₂ : PhysicalL2) (x : recoveredActualSourceFreeWeightedDomain n) :
    actualSourcePotentialOnRecoveredWeightedDomainAfterAE n u₁ u₂ x =
      actualL2PotentialParityPairSourceOperator u₁ u₂
        (actualSourceWeightedDomainLInfRepresentativeMap n
          (recoveredActualSourceWeightedDomainSequenceMapAfterAE n x)) := by
  rfl

end NlsGge.Schur

end
