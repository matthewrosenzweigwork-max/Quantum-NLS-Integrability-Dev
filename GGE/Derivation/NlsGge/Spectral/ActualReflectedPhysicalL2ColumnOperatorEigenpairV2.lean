import NlsGge.Spectral.ActualReflectedPhysicalL2ColumnGraphRealizationV2
import NlsGge.Spectral.ActualFullPeriodTwoSourceBlockOperatorV4
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Filter
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis
open NlsGge.Schur.TransportBridgeV4

/-- Actual domain element obtained from the concrete monodromy boundary. -/
def actualReflectedPhysicalL2ColumnSourceDomainElement
    (n : ℤ) (u : PhysicalL2) (z : ℂ) (v : Fin 2 → ℂ)
    (hboundary : actualReflectedPhysicalL2ZsColumn u z v 1 = spectralSign n • v) :
    recoveredActualSourceFreeWeightedDomain n :=
  ⟨actualReflectedPhysicalL2ColumnSourcePair u z v,
    actualReflectedPhysicalL2Column_in_freeWeightedDomain n u z v hboundary⟩

/-- Equality of genuine L-infinity classes suffices for the rough potential
product; no pointwise linearity of chosen Lp representatives is asserted. -/
theorem actualReflectedPhysicalL2Column_domainLInf_eq
    (n : ℤ) (u : PhysicalL2) (z : ℂ) (v : Fin 2 → ℂ)
    (hboundary : actualReflectedPhysicalL2ZsColumn u z v 1 = spectralSign n • v)
    (b : Bool) :
    actualSourceWeightedDomainLInfRepresentativeMap n
      (recoveredActualSourceWeightedDomainSequenceMapAfterAE n
        (actualReflectedPhysicalL2ColumnSourceDomainElement n u z v hboundary)) b =
      sourceIntervalLInfOfContinuousOn
        (fun t => actualReflectedPhysicalL2ZsColumn u z v t (if b then 0 else 1))
        (continuousOn_actualReflectedPhysicalL2ZsColumn u z v (if b then 0 else 1)) := by
  apply Lp.ext
  exact (actualSourceWeightedDomainRepresentative_matches_source_ae n
    (actualReflectedPhysicalL2ColumnSourceDomainElement n u z v hboundary) b).trans
    ((actualReflectedPhysicalL2ColumnSourcePair_component_ae u z v b).trans
      (sourceIntervalLInfOfContinuousOn_ae _ _).symm)

/-- The actual source free action is identified from the full weak derivative
predicate, retaining every Fourier coefficient, including zero. -/
theorem actualReflectedPhysicalL2Column_sourceFreeAction
    (n : ℤ) (u : PhysicalL2) (z : ℂ) (v : Fin 2 → ℂ)
    (hboundary : actualReflectedPhysicalL2ZsColumn u z v 1 = spectralSign n • v)
    (b : Bool) :
    actualSourceFreeDiracMapAfterAE n
      (actualReflectedPhysicalL2ColumnSourceDomainElement n u z v hboundary) b =
    (if b then -Complex.I else Complex.I) •
      actualContinuousReflectedDiracDerivativeClass u z
        (fun t => actualReflectedPhysicalL2ZsColumn u z v t 0)
        (fun t => actualReflectedPhysicalL2ZsColumn u z v t 1)
        (continuousOn_actualReflectedPhysicalL2ZsColumn u z v 0)
        (continuousOn_actualReflectedPhysicalL2ZsColumn u z v 1) b := by
  let X := actualReflectedPhysicalL2ColumnSourceDomainElement n u z v hboundary
  let C := actualReflectedPhysicalL2ZsColumn u z v
  let G := actualContinuousReflectedDiracDerivativeClass u z
    (fun t => C t 0) (fun t => C t 1)
    (continuousOn_actualReflectedPhysicalL2ZsColumn u z v 0)
    (continuousOn_actualReflectedPhysicalL2ZsColumn u z v 1)
  have hweak : SourceTwistedWeakDerivative n
      (sourceCoordinateComponent n (sourcePairRepr n X.val) b) (G b) := by
    apply sourceTwistedWeakDerivative_of_actualAC_representatives n _ (G b)
      (fun t => C t (if b then 0 else 1))
      (actualContinuousReflectedDiracDerivativeRepresentative u z
        (fun t => C t 0) (fun t => C t 1) b)
    · exact absolutelyContinuous_actualReflectedPhysicalL2ZsColumn u z v _
    · exact actualContinuousReflectedDiracDerivativeRepresentative_intervalIntegrable
        u z _ _ (continuousOn_actualReflectedPhysicalL2ZsColumn u z v 0)
        (continuousOn_actualReflectedPhysicalL2ZsColumn u z v 1) b
    · exact actualReflectedPhysicalL2ZsColumn_ae_actual_source_derivative u z v b
    · rw [sourceCoordinateComponent_sourcePairRepr]
      exact actualReflectedPhysicalL2ColumnSourcePair_component_ae u z v b
    · exact actualContinuousReflectedDiracDerivativeClass_ae
        u z _ _ (continuousOn_actualReflectedPhysicalL2ZsColumn u z v 0)
        (continuousOn_actualReflectedPhysicalL2ZsColumn u z v 1) b
    · dsimp only [C]
      rw [hboundary, actualReflectedPhysicalL2ZsColumn_initial]
      rfl
  calc
    actualSourceFreeDiracMapAfterAE n X b =
        sourceCoordinateComponent n (sourcePairRepr n (actualSourceFreeDiracMapAfterAE n X)) b :=
      (sourceCoordinateComponent_sourcePairRepr n _ b).symm
    _ = sourceFreeDiracAction n (sourcePairRepr n X.val) X.property b := by
      rw [actualSourceFreeDiracMapAfterAE_repr_apply]
      exact (sourceFreeDiracAction_eq_coordinate n _ X.property b).symm
    _ = (if b then -Complex.I else Complex.I) • G b :=
      sourceFreeDiracAction_eq_actual_weak_derivative n _ X.property b (G b) hweak

/-- A concrete nonzero monodromy column satisfying its actual twisted trace
is an eigenvector of the genuine reflected source D+V_u operator. This is a
forward realization theorem, not the reverse spectral identification. -/
theorem actualReflectedPhysicalL2Column_actualSourceOperator_eigenaction
    (n : ℤ) (u : PhysicalL2) (z : ℂ) (v : Fin 2 → ℂ)
    (hboundary : actualReflectedPhysicalL2ZsColumn u z v 1 = spectralSign n • v) :
    actualSourcePerturbedDiracPMapAfterAE n u (star u)
      (actualReflectedPhysicalL2ColumnSourceDomainElement n u z v hboundary) =
      z • actualReflectedPhysicalL2ColumnSourcePair u z v := by
  let X := actualReflectedPhysicalL2ColumnSourceDomainElement n u z v hboundary
  apply PiLp.ext
  intro b
  change actualSourceFreeDiracMapAfterAE n X b +
    actualSourcePotentialOnRecoveredWeightedDomainAfterAE n u (star u) X b = _
  rw [actualReflectedPhysicalL2Column_sourceFreeAction,
    actualSourcePotentialOnRecoveredWeightedDomain_apply]
  cases b
  · rw [actualL2PotentialParityPairSourceOperator_apply_false,
      actualReflectedPhysicalL2Column_domainLInf_eq]
    let F := sourceIntervalL2OfContinuousOn
      (fun t => actualReflectedPhysicalL2ZsColumn u z v t 1)
      (continuousOn_actualReflectedPhysicalL2ZsColumn u z v 1)
    let P := actualSourceL2PotentialTimesLInf (star u)
      (sourceIntervalLInfOfContinuousOn
        (fun t => actualReflectedPhysicalL2ZsColumn u z v t 0)
        (continuousOn_actualReflectedPhysicalL2ZsColumn u z v 0))
    change Complex.I • (Complex.I • (P - z • F)) + P = z • F
    simp only [smul_smul, Complex.I_mul_I, neg_one_smul]
    abel
  · rw [actualL2PotentialParityPairSourceOperator_apply_true,
      actualReflectedPhysicalL2Column_domainLInf_eq]
    let F := sourceIntervalL2OfContinuousOn
      (fun t => actualReflectedPhysicalL2ZsColumn u z v t 0)
      (continuousOn_actualReflectedPhysicalL2ZsColumn u z v 0)
    let P := actualSourceL2PotentialTimesLInf u
      (sourceIntervalLInfOfContinuousOn
        (fun t => actualReflectedPhysicalL2ZsColumn u z v t 1)
        (continuousOn_actualReflectedPhysicalL2ZsColumn u z v 1))
    change (-Complex.I) • (Complex.I • (z • F - P)) + P = z • F
    simp only [smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul]
    abel

end NlsGge.SpectralFoundations
end
