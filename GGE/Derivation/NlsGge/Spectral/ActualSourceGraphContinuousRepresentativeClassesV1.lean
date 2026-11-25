import NlsGge.Spectral.ActualFreeGraphContinuousACDerivativeV3
import NlsGge.Spectral.ActualReflectedPhysicalL2ColumnOperatorEigenpairV2
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Filter
namespace NlsGge.Schur
open NlsGge.Pilot NlsGge.Analysis TransportBridgeV4

/-- Actual continuous reconstruction of an arbitrary recovered source graph
vector, with the reflected Boolean Fourier convention. -/
def actualSourceGraphContinuousRepresentative
    (n : ℤ) (X : recoveredActualSourceFreeWeightedDomain n) (b : Bool) (t : ℝ) : ℂ :=
  freeDomainContinuousComponent n (sourcePairRepr n X.val) b (t : SpectralCircle)

theorem continuous_actualSourceGraphContinuousRepresentative
    (n : ℤ) (X : recoveredActualSourceFreeWeightedDomain n) (b : Bool) :
    Continuous (actualSourceGraphContinuousRepresentative n X b) :=
  (freeDomainContinuousComponent n (sourcePairRepr n X.val) b).continuous.comp
    (AddCircle.continuous_mk' (2 : ℝ))

theorem actualSourceGraphContinuousRepresentative_ae_source_class
    (n : ℤ) (X : recoveredActualSourceFreeWeightedDomain n) (b : Bool) :
    actualSourceGraphContinuousRepresentative n X b =ᵐ[
      volume.restrict (Set.Ioc (0 : ℝ) 1)] (X.val b : ℝ → ℂ) := by
  have hr := actualSourceWeightedDomainLInfRepresentativeMap_ae n
    (recoveredActualSourceWeightedDomainSequenceMapAfterAE n X) b
  have hs := actualSourceWeightedDomainRepresentative_matches_source_ae n X b
  exact hr.symm.trans hs

theorem actualSourceGraphContinuousRepresentative_L2_eq
    (n : ℤ) (X : recoveredActualSourceFreeWeightedDomain n) (b : Bool) :
    sourceIntervalL2OfContinuousOn (actualSourceGraphContinuousRepresentative n X b)
      (continuous_actualSourceGraphContinuousRepresentative n X b).continuousOn = X.val b := by
  apply Lp.ext
  exact (sourceIntervalL2OfContinuousOn_ae _
    (continuous_actualSourceGraphContinuousRepresentative n X b).continuousOn).trans
    (actualSourceGraphContinuousRepresentative_ae_source_class n X b)

theorem actualSourceGraphContinuousRepresentative_LInf_eq
    (n : ℤ) (X : recoveredActualSourceFreeWeightedDomain n) (b : Bool) :
    actualSourceWeightedDomainLInfRepresentativeMap n
      (recoveredActualSourceWeightedDomainSequenceMapAfterAE n X) b =
    sourceIntervalLInfOfContinuousOn (actualSourceGraphContinuousRepresentative n X b)
      (continuous_actualSourceGraphContinuousRepresentative n X b).continuousOn := by
  apply Lp.ext
  have hr := actualSourceWeightedDomainLInfRepresentativeMap_ae n
    (recoveredActualSourceWeightedDomainSequenceMapAfterAE n X) b
  exact hr.trans (sourceIntervalLInfOfContinuousOn_ae _
    (continuous_actualSourceGraphContinuousRepresentative n X b).continuousOn).symm

/-- The existing source free map and the weak-derivative free action coincide
on every actual recovered graph vector, rather than only constructed columns. -/
theorem actualSourceFreeDiracMapAfterAE_component_eq_sourceFreeDiracAction
    (n : ℤ) (X : recoveredActualSourceFreeWeightedDomain n) (b : Bool) :
    actualSourceFreeDiracMapAfterAE n X b =
    sourceFreeDiracAction n (sourcePairRepr n X.val) X.property b := by
  calc
    actualSourceFreeDiracMapAfterAE n X b =
        sourceCoordinateComponent n (sourcePairRepr n (actualSourceFreeDiracMapAfterAE n X)) b :=
      (sourceCoordinateComponent_sourcePairRepr n _ b).symm
    _ = sourceFreeDiracAction n (sourcePairRepr n X.val) X.property b := by
      rw [actualSourceFreeDiracMapAfterAE_repr_apply]
      exact (sourceFreeDiracAction_eq_coordinate n _ X.property b).symm

end NlsGge.Schur
end
