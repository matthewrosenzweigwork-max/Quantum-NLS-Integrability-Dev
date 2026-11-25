import NlsGge.Spectral.ActualSourceWeightedDomainPotentialAECoherenceMinimumV2
import NlsGge.Schur.CoveredH1ParityPairOperatorFromAE

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory

namespace NlsGge.Schur
open NlsGge.Pilot NlsGge.Analysis
open TransportBridgeV4

/-- The source-interval component of a parity-pair vector is a.e. the
restriction of its scalar-parity component to the first period. -/
theorem parityPairIntervalEquiv_apply_ae (n : ℤ) (w : ParityPair n) (b : Bool) :
    (parityPairIntervalEquiv n w b : ℝ → ℂ) =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)]
      fun t : ℝ => (w b).val (t : SpectralCircle) :=
  scalarParityRestrictValue_ae n (w b)

/-- Source-interval and Schur-side channel conventions agree: the `true`
component of the potential is `u₁` times the `false` component, and the
`false` component is `u₂` times the `true` component, with no reflection or
conjugation. -/
theorem actualSourcePotentialOnWeightedDomain_eq_coveredH1ParityPairPotential
    (n : ℤ) (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (x : freeWeightedDomainPointwise n) :
    actualSourcePotentialOnWeightedDomain n u₁ u₂ x =
      parityPairIntervalEquiv n
        (coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n
          ((parityPairRepr n).symm x.val)) := by
  let y : ParityPair n := (parityPairRepr n).symm x.val
  have hxy : (sourcePairRepr n) (parityPairIntervalEquiv n y) = x.val := by
    change (parityPairRepr n) ((parityPairIntervalEquiv n).symm
      (parityPairIntervalEquiv n y)) = x.val
    rw [LinearIsometryEquiv.symm_apply_apply]
    exact (parityPairRepr n).apply_symm_apply _
  let x' : recoveredActualSourceFreeWeightedDomain n :=
    ⟨parityPairIntervalEquiv n y, by
      change (sourcePairRepr n) (parityPairIntervalEquiv n y) ∈
        freeWeightedDomainPointwise n
      rw [hxy]; exact x.property⟩
  have hseq : recoveredActualSourceWeightedDomainSequenceMapAfterAE n x' = x :=
    Subtype.ext hxy
  have hmatch := actualSourceWeightedDomainRepresentative_matches_source_ae n x'
  rw [hseq] at hmatch
  have hup := actualSourcePotentialOnWeightedDomain_upper_ae n u₁ u₂ x
  have hlo := actualSourcePotentialOnWeightedDomain_lower_ae n u₁ u₂ x
  have hrep := actualSourceWeightedDomainLInfRepresentativeMap_ae n x
  apply PiLp.ext
  intro b
  apply Lp.ext
  cases b
  · -- lower component: `u₂` times the upper component
    have hm := hmatch true
    have hmult := spectral_ae_pullback_first_half
      (coveredH1SpectralMultiplier_ae u₂ hu₂ (y true).val)
    have hres := parityPairIntervalEquiv_apply_ae n
      (coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n y) false
    have hH1 := spectral_ae_pullback_first_half
      (naturalPhysicalCoverH1Bounded_ae u₂ hu₂)
    have hy := parityPairIntervalEquiv_apply_ae n y true
    filter_upwards [hlo, hrep true, hm, hmult, hres, hH1, hy]
      with t hlo hrep hm hmult hres hH1 hy
    rw [hlo, hres]
    simp only [coveredH1ParityPairPotential_apply_false,
      coveredH1ScalarParityMultiplier_coe_apply]
    rw [hmult, hH1, naturalPhysicalCover_coe]
    rw [← hrep, hm]
    change _ * ((parityPairIntervalEquiv n y) true : ℝ → ℂ) t = _
    rw [hy]
  · -- upper component: `u₁` times the lower component
    have hm := hmatch false
    have hmult := spectral_ae_pullback_first_half
      (coveredH1SpectralMultiplier_ae u₁ hu₁ (y false).val)
    have hres := parityPairIntervalEquiv_apply_ae n
      (coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n y) true
    have hH1 := spectral_ae_pullback_first_half
      (naturalPhysicalCoverH1Bounded_ae u₁ hu₁)
    have hy := parityPairIntervalEquiv_apply_ae n y false
    filter_upwards [hup, hrep false, hm, hmult, hres, hH1, hy]
      with t hup hrep hm hmult hres hH1 hy
    rw [hup, hres]
    simp only [coveredH1ParityPairPotential_apply_true,
      coveredH1ScalarParityMultiplier_coe_apply]
    rw [hmult, hH1, naturalPhysicalCover_coe]
    rw [← hrep, hm]
    change _ * ((parityPairIntervalEquiv n y) false : ℝ → ℂ) t = _
    rw [hy]

end NlsGge.Schur

end
