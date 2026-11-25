import Mathlib.Analysis.InnerProductSpace.LinearPMap
import NlsGge.Schur.PhysicalSector
import NlsGge.Spectral.ActualSourceWeightedDomainTransportBridgeV4
import NlsGge.Spectral.ActualSourceWeightedDomainPerturbedImaginaryRangeAlgebraV7
import NlsGge.Spectral.ActualFreeWeightedDiracFormalSymmetryV4
import NlsGge.Spectral.ActualParityPairPotentialFormalAdjointSourceV5
import NlsGge.Spectral.ActualSourceWeightedDomainLInfRepresentativeMatchesSourceV5
import NlsGge.Spectral.ActualSourceWeightedDomainPotentialAECoherenceMinimumV2

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory

namespace NlsGge.Schur
open NlsGge.Pilot
open TransportBridgeV4

/-- The source realization of the free diagonal on the recovered actual
weighted domain. This is a linear map on that domain, not a bounded ambient-L²
operator. -/
def actualSourceFreeDiracMapAfterAE (n : ℤ) :
    recoveredActualSourceFreeWeightedDomain n →ₗ[ℂ] SourcePairL2 :=
  (sourcePairRepr n).toLinearEquiv.symm.toLinearMap.comp
    ((freeCoordinateDirac n).comp
      (recoveredActualSourceWeightedDomainSequenceMapAfterAE n))

theorem actualSourceFreeDiracMapAfterAE_repr_apply
    (n : ℤ) (x : recoveredActualSourceFreeWeightedDomain n) :
    sourcePairRepr n (actualSourceFreeDiracMapAfterAE n x) =
      freeCoordinateDirac n (recoveredActualSourceWeightedDomainSequenceMapAfterAE n x) := by
  exact (sourcePairRepr n).toLinearEquiv.apply_symm_apply _

/-- The actual source-domain realization of `D + V` is formally symmetric on
the physical real-potential slice. This is the domain-level inner-product
identity only; the uniform imaginary ranges are a separate result. -/
def actualSourcePerturbedDiracPMapAfterAE (n : ℤ) (u₁ u₂ : PhysicalL2) :
    SourcePairL2 →ₗ.[ℂ] SourcePairL2 :=
  ⟨recoveredActualSourceFreeWeightedDomain n,
    actualSourceFreeDiracMapAfterAE n +
      actualSourcePotentialOnRecoveredWeightedDomainAfterAE n u₁ u₂⟩

theorem actualSourcePerturbedDirac_formalSelfAdjoint_of_physical_slice
    (n : ℤ) (u₁ u₂ : PhysicalL2) (hphysical : u₂ = star u₁) :
    (actualSourcePerturbedDiracPMapAfterAE n u₁ u₂).IsFormalAdjoint
      (actualSourcePerturbedDiracPMapAfterAE n u₁ u₂) := by
  intro x y
  change inner ℂ
      (actualSourceFreeDiracMapAfterAE n x +
        actualSourcePotentialOnRecoveredWeightedDomainAfterAE n u₁ u₂ x)
      y.val =
    inner ℂ x.val
      (actualSourceFreeDiracMapAfterAE n y +
        actualSourcePotentialOnRecoveredWeightedDomainAfterAE n u₁ u₂ y)
  let f : ActualSourceIntervalLInfPair :=
    actualSourceWeightedDomainLInfRepresentativeMap n
      (recoveredActualSourceWeightedDomainSequenceMapAfterAE n x)
  let g : ActualSourceIntervalLInfPair :=
    actualSourceWeightedDomainLInfRepresentativeMap n
      (recoveredActualSourceWeightedDomainSequenceMapAfterAE n y)
  have hf : ∀ b : Bool,
      (f b : ℝ → ℂ) =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] (x.val b : ℝ → ℂ) := by
    intro b
    simpa only [f] using
      actualSourceWeightedDomainRepresentative_matches_source_ae n x b
  have hg : ∀ b : Bool,
      (g b : ℝ → ℂ) =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] (y.val b : ℝ → ℂ) := by
    intro b
    simpa only [g] using
      actualSourceWeightedDomainRepresentative_matches_source_ae n y b
  have hV := actualL2PotentialParityPairSourceOperator_formal_adjoint_of_source_conjugacy
    u₁ u₂ hphysical f g x.val y.val hf hg
  have hPotential :
      inner ℂ (actualSourcePotentialOnRecoveredWeightedDomainAfterAE n u₁ u₂ x) y.val =
        inner ℂ x.val (actualSourcePotentialOnRecoveredWeightedDomainAfterAE n u₁ u₂ y) := by
    rw [actualSourcePotentialOnRecoveredWeightedDomain_apply,
      actualSourcePotentialOnRecoveredWeightedDomain_apply]
    simpa only [f, g] using hV
  have hFree :
      inner ℂ (actualSourceFreeDiracMapAfterAE n x) y.val =
        inner ℂ x.val (actualSourceFreeDiracMapAfterAE n y) := by
    let sx := recoveredActualSourceWeightedDomainSequenceMapAfterAE n x
    let sy := recoveredActualSourceWeightedDomainSequenceMapAfterAE n y
    have hcoord := actualFreeWeightedDirac_formalSelfAdjoint n sx sy
    calc
      inner ℂ (actualSourceFreeDiracMapAfterAE n x) y.val =
          inner ℂ (sourcePairRepr n (actualSourceFreeDiracMapAfterAE n x))
            (sourcePairRepr n y.val) :=
        ((sourcePairRepr n).inner_map_map
          (actualSourceFreeDiracMapAfterAE n x) y.val).symm
      _ = inner ℂ (freeCoordinateDirac n sx) sy := by
        rw [actualSourceFreeDiracMapAfterAE_repr_apply]
        rfl
      _ = inner ℂ sx.val (freeCoordinateDirac n sy) := hcoord
      _ = inner ℂ (sourcePairRepr n x.val)
          (sourcePairRepr n (actualSourceFreeDiracMapAfterAE n y)) := by
        rw [← actualSourceFreeDiracMapAfterAE_repr_apply]
        rfl
      _ = inner ℂ x.val (actualSourceFreeDiracMapAfterAE n y) :=
        (sourcePairRepr n).inner_map_map x.val
          (actualSourceFreeDiracMapAfterAE n y)
  rw [inner_add_left, inner_add_right, hFree, hPotential]

end NlsGge.Schur

end
