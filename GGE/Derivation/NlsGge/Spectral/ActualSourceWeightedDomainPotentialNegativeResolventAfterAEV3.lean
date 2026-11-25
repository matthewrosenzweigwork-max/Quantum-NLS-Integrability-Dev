import NlsGge.Spectral.ActualSourceWeightedDomainPotentialInterfaceAfterAEV1
import NlsGge.Spectral.ActualFullNegativeImaginaryResolventLInfCLMV1
import NlsGge.Spectral.ActualRoughL2PotentialTimesFullNegativeImaginaryResolventV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace NlsGge.Schur
open NlsGge.Pilot

/-- Evaluate the actual full negative-imaginary coordinate resolvent into the
weighted free-domain subtype. This is a linear map into that subtype, with no
claim of boundedness for the unbounded free differential operator. -/
def actualSourceFullNegativeImaginaryResolventDomainLinearMapAfterAE
    (n : ℤ) (y : ℝ) (hy : 1 ≤ y) :
    SourcePairL2 →ₗ[ℂ] freeWeightedDomainPointwise n where
  toFun x :=
    ⟨sourceFullNegativeImaginaryResolventSquare n y hy (sourcePairRepr n x),
      sourceFullNegativeImaginaryResolventSquare_mem_freeWeightedDomain n y hy
        (sourcePairRepr n x)⟩
  map_add' x z := by
    apply Subtype.ext
    change sourceFullNegativeImaginaryResolventSquare n y hy
        (sourcePairRepr n (x + z)) =
      sourceFullNegativeImaginaryResolventSquare n y hy (sourcePairRepr n x) +
        sourceFullNegativeImaginaryResolventSquare n y hy (sourcePairRepr n z)
    rw [(sourcePairRepr n).map_add, map_add]
  map_smul' a x := by
    apply Subtype.ext
    change sourceFullNegativeImaginaryResolventSquare n y hy
        (sourcePairRepr n (a • x)) =
      a • sourceFullNegativeImaginaryResolventSquare n y hy (sourcePairRepr n x)
    rw [(sourcePairRepr n).map_smul, map_smul]

/-- The continuous Fourier representative of the negative full resolvent is
the same actual source L-infinity class as its interval CLM. The proof compares
the two classes through their checked AE representatives. -/
theorem actualSourceWeightedDomainLInfRepresentativeMap_fullNegativeResolvent
    (n : ℤ) (y : ℝ) (hy : 1 ≤ y) (x : SourcePairL2) :
    actualSourceWeightedDomainLInfRepresentativeMap n
      (actualSourceFullNegativeImaginaryResolventDomainLinearMapAfterAE n y hy x) =
        actualFullNegativeImaginaryResolventIntervalLInfCLM n y hy x := by
  apply PiLp.ext
  intro upper
  apply Lp.ext
  filter_upwards [
    actualSourceWeightedDomainLInfRepresentativeMap_ae n
      (actualSourceFullNegativeImaginaryResolventDomainLinearMapAfterAE n y hy x)
      upper,
    actualFullNegativeImaginaryResolventIntervalLInf_ae n y hy x upper]
      with t hDomain hResolvent
  calc
    actualSourceWeightedDomainLInfRepresentativeMap n
        (actualSourceFullNegativeImaginaryResolventDomainLinearMapAfterAE n y hy x)
        upper t = freeDomainContinuousComponent n
          (sourceFullNegativeImaginaryResolventSquare n y hy (sourcePairRepr n x)) upper
          ((t : ℝ) : SpectralCircle) := hDomain
    _ = actualFullNegativeImaginaryResolventIntervalLInf n y hy x upper t :=
      hResolvent.symm

/-- Applying the actual physical potential to the negative-imaginary free
resolvent agrees with the source-space negative `V R₀` CLM. -/
theorem actualSourcePotentialOnWeightedDomain_fullNegativeResolvent
    (n : ℤ) (y : ℝ) (hy : 1 ≤ y) (u₁ u₂ : PhysicalL2) (x : SourcePairL2) :
    actualSourcePotentialOnWeightedDomain n u₁ u₂
      (actualSourceFullNegativeImaginaryResolventDomainLinearMapAfterAE n y hy x) =
        actualRoughL2PotentialFullNegativeImaginaryResolventCLM n y hy u₁ u₂ x := by
  change actualL2PotentialParityPairSourceOperator u₁ u₂
      (actualSourceWeightedDomainLInfRepresentativeMap n
        (actualSourceFullNegativeImaginaryResolventDomainLinearMapAfterAE n y hy x)) = _
  rw [actualSourceWeightedDomainLInfRepresentativeMap_fullNegativeResolvent]
  rfl

end NlsGge.Schur

end
