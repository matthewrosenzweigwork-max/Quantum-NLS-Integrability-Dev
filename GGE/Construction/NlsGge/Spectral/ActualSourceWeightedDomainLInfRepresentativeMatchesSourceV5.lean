import NlsGge.Spectral.ActualSourceWeightedDomainPotentialInterfaceAfterAEV1
import NlsGge.Spectral.SpectralHaarIsProbabilityMeasureV2
import NlsGge.Spectral.ActualSourceWeightedDomainTransportBridgeV4
import NlsGge.Schur.SignedInterval

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace NlsGge.Schur
open NlsGge.Pilot
open TransportBridgeV4
local instance : IsProbabilityMeasure spectralHaar := spectralHaar_isProbabilityMeasure

private abbrev actualSourceRepresentativeMeasure : Measure ℝ :=
  volume.restrict (Set.Ioc (0 : ℝ) 1)

/-- The continuous Fourier representative of a vector in the actual recovered
source weighted domain is the same source L² vector. This identifies the L∞
representative used by the potential with the domain element itself. -/
theorem actualSourceWeightedDomainLInfRepresentativeMap_matches_source_ae
    (n : ℤ) (x : recoveredActualSourceFreeWeightedDomain n) (upper : Bool) :
    (actualSourceWeightedDomainLInfRepresentativeMap n
      ⟨(sourcePairRepr n).toLinearEquiv x.val, x.property⟩ upper : ℝ → ℂ) =ᵐ[
        actualSourceRepresentativeMeasure] (x.val upper : ℝ → ℂ) := by
  let seq : freeWeightedDomainPointwise n :=
    ⟨(sourcePairRepr n).toLinearEquiv x.val, x.property⟩
  let F := freeDomainContinuousComponent n seq.val upper
  have hcoord : sourceCoordinateComponent n seq.val upper = x.val upper := by
    change scalarParityRestrict n
      ((parityPairRepr n).symm
        ((parityPairRepr n) ((parityPairIntervalEquiv n).symm x.val)) upper) = _
    rw [(parityPairRepr n).symm_apply_apply]
    change scalarParityIntervalEquiv n
      ((scalarParityIntervalEquiv n).symm (x.val upper)) = x.val upper
    exact (scalarParityIntervalEquiv n).apply_symm_apply _
  have hcoordAE := Lp.ext_iff.mp hcoord
  have hRep := actualSourceWeightedDomainLInfRepresentativeMap_ae n seq upper
  have hLp := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) spectralHaar F
  have hCircle := spectral_ae_pullback_first_half hLp
  have hSource := freeDomainContinuousComponent_toSourceInterval_ae
    n seq.val seq.property upper
  filter_upwards [hRep, hCircle, hSource, hcoordAE]
    with t hRep_t hCircle_t hSource_t hcoord_t
  change (actualSourceWeightedDomainLInfRepresentativeMap n seq upper : ℝ → ℂ) t = _
  calc
    (actualSourceWeightedDomainLInfRepresentativeMap n seq upper : ℝ → ℂ) t =
        F ((t : ℝ) : SpectralCircle) := hRep_t
    _ = ((ContinuousMap.toLp 2 spectralHaar ℂ F :
        Lp ℂ 2 spectralHaar) ((t : ℝ) : SpectralCircle)) := hCircle_t.symm
    _ = (sourceCoordinateComponent n seq.val upper : ℝ → ℂ) t := hSource_t
    _ = (x.val upper : ℝ → ℂ) t := hcoord_t

end NlsGge.Schur

end
