import NlsGge.Spectral.ActualReflectedPhysicalL2ZsColumnSourceDerivativeV3
import NlsGge.Spectral.ActualSourcePairCoordinateTransportV1
import NlsGge.Schur.SourceIntervalContinuousRepresentativeNonzeroV2
import NlsGge.Spectral.ActualACTwistedWeakDerivativeV1
import NlsGge.Spectral.ActualSourceTwistedWeakDerivativeUniquenessV1
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Filter
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-- Genuine source-interval L² classes of the original (-u,-z) column. -/
def actualReflectedPhysicalL2ColumnSourcePair
    (u : PhysicalL2) (z : ℂ) (v : Fin 2 → ℂ) : SourcePairL2 :=
  WithLp.toLp 2 (fun b : Bool => sourceIntervalL2OfContinuousOn
    (fun t => actualReflectedPhysicalL2ZsColumn u z v t (if b then 0 else 1))
    (continuousOn_actualReflectedPhysicalL2ZsColumn u z v (if b then 0 else 1)))

theorem actualReflectedPhysicalL2ColumnSourcePair_component_ae
    (u : PhysicalL2) (z : ℂ) (v : Fin 2 → ℂ) (b : Bool) :
    (actualReflectedPhysicalL2ColumnSourcePair u z v b : ℝ → ℂ) =ᵐ[
      volume.restrict (Set.Ioc (0 : ℝ) 1)]
      (fun t => actualReflectedPhysicalL2ZsColumn u z v t (if b then 0 else 1)) :=
  sourceIntervalL2OfContinuousOn_ae _
    (continuousOn_actualReflectedPhysicalL2ZsColumn u z v (if b then 0 else 1))

/-- A nonzero initial column realizes a nonzero actual L² vector, including
when its initial endpoint is outside the Ioc integration carrier. -/
theorem actualReflectedPhysicalL2ColumnSourcePair_ne_zero
    (u : PhysicalL2) (z : ℂ) (v : Fin 2 → ℂ) (hv : v ≠ 0) :
    actualReflectedPhysicalL2ColumnSourcePair u z v ≠ 0 := by
  intro h
  have hz (b : Bool) : v (if b then 0 else 1) = 0 := by
    by_contra hval
    have hinitial : actualReflectedPhysicalL2ZsColumn u z v 0 (if b then 0 else 1) ≠ 0 := by
      rw [actualReflectedPhysicalL2ZsColumn_initial]
      exact hval
    have hne := sourceIntervalL2OfContinuousOn_ne_zero_of_initial
      (fun t => actualReflectedPhysicalL2ZsColumn u z v t (if b then 0 else 1))
      (continuousOn_actualReflectedPhysicalL2ZsColumn u z v (if b then 0 else 1)) hinitial
    apply hne
    exact congrArg (fun P : SourcePairL2 => P b) h
  apply hv
  funext i
  fin_cases i
  · exact hz true
  · exact hz false

/-- The actual monodromy twisted-endpoint equation yields the true signed
Fourier graph domain. Domain membership is a conclusion, not a hypothesis. -/
theorem actualReflectedPhysicalL2Column_in_freeWeightedDomain
    (n : ℤ) (u : PhysicalL2) (z : ℂ) (v : Fin 2 → ℂ)
    (hboundary : actualReflectedPhysicalL2ZsColumn u z v 1 = spectralSign n • v) :
    sourcePairRepr n (actualReflectedPhysicalL2ColumnSourcePair u z v) ∈
      freeWeightedDomainPointwise n := by
  let C := actualReflectedPhysicalL2ZsColumn u z v
  let f : Bool → ℝ → ℂ := fun b t => C t (if b then 0 else 1)
  let G := actualContinuousReflectedDiracDerivativeClass u z
    (fun t => C t 0) (fun t => C t 1)
    (continuousOn_actualReflectedPhysicalL2ZsColumn u z v 0)
    (continuousOn_actualReflectedPhysicalL2ZsColumn u z v 1)
  let g := actualContinuousReflectedDiracDerivativeRepresentative u z
    (fun t => C t 0) (fun t => C t 1)
  apply sourceFreeDomain_of_actualAC_components n _ G f g
  · intro b
    exact absolutelyContinuous_actualReflectedPhysicalL2ZsColumn u z v _
  · intro b
    exact actualContinuousReflectedDiracDerivativeRepresentative_intervalIntegrable
      u z (fun t => C t 0) (fun t => C t 1)
      (continuousOn_actualReflectedPhysicalL2ZsColumn u z v 0)
      (continuousOn_actualReflectedPhysicalL2ZsColumn u z v 1) b
  · intro b
    exact actualReflectedPhysicalL2ZsColumn_ae_actual_source_derivative u z v b
  · intro b
    rw [sourceCoordinateComponent_sourcePairRepr]
    exact actualReflectedPhysicalL2ColumnSourcePair_component_ae u z v b
  · intro b
    exact actualContinuousReflectedDiracDerivativeClass_ae u z _ _ _ _ b
  · intro b
    change C 1 (if b then 0 else 1) = spectralSign n * C 0 (if b then 0 else 1)
    dsimp only [C]
    rw [hboundary, actualReflectedPhysicalL2ZsColumn_initial]
    rfl

end NlsGge.SpectralFoundations
end
