import Mathlib.Analysis.InnerProductSpace.LinearPMap
import NlsGge.Spectral.TwoImaginaryRangesSelfAdjointV2
import NlsGge.Spectral.ActualSourcePerturbedDiracFormalSymmetryPhysicalSliceV6
import NlsGge.Spectral.ActualSourceWeightedDomainDenseV2
import NlsGge.Spectral.ActualSourcePerturbedImaginaryShiftsUniformRangeV4
import NlsGge.Spectral.ActualSourceWeightedDomainTransportBridgeV4
import NlsGge.Schur.FreeCoordinateDomainInverse

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped LinearPMap

namespace NlsGge.Schur
open NlsGge.Pilot
open TransportBridgeV4

/-- The transported free source shift is `z - D` on its genuine weighted
source domain. -/
theorem actualSourceFreeShiftedDirac_eq_smul_sub_freeDirac
    (n : ℤ) (z : ℂ) (x : recoveredActualSourceFreeWeightedDomain n) :
    recoveredActualSourceFreeShiftedDirac n z x =
      z • (x : SourcePairL2) - actualSourceFreeDiracMapAfterAE n x := by
  apply (sourcePairRepr n).injective
  rw [recoveredActualSourceFreeShiftedDirac_repr_apply,
    (sourcePairRepr n).map_sub, (sourcePairRepr n).map_smul,
    actualSourceFreeDiracMapAfterAE_repr_apply]
  simp [freeShiftedCoordinateDirac,
    recoveredActualSourceWeightedDomainSequenceMapAfterAE]

/-- The actual source perturbed shift is `z - (D + V)` on the recovered
weighted domain. -/
theorem actualSourcePerturbedShiftedDirac_eq_smul_sub_sourcePMap
    (n : ℤ) (z : ℂ) (u₁ u₂ : PhysicalL2)
    (x : recoveredActualSourceFreeWeightedDomain n) :
    actualSourcePerturbedShiftedDiracAfterAE n z u₁ u₂ x =
      z • (x : SourcePairL2) - actualSourcePerturbedDiracPMapAfterAE n u₁ u₂ x := by
  change recoveredActualSourceFreeShiftedDirac n z x -
      actualSourcePotentialOnRecoveredWeightedDomainAfterAE n u₁ u₂ x =
    z • (x : SourcePairL2) -
      (actualSourceFreeDiracMapAfterAE n x +
        actualSourcePotentialOnRecoveredWeightedDomainAfterAE n u₁ u₂ x)
  rw [actualSourceFreeShiftedDirac_eq_smul_sub_freeDirac]
  abel

/-- For each fixed sector, the actual source realization of the perturbed
Dirac operator is self-adjoint on the recovered weighted domain, for a
physical real-potential pair. This is a fixed-sector realization result; it
does not assert the assembled period-two theorem. -/
theorem actualSourcePerturbedDirac_selfAdjoint_of_physical_slice
    (n : ℤ) (u₁ u₂ : PhysicalL2) (hphysical : u₂ = star u₁) :
    IsSelfAdjoint (actualSourcePerturbedDiracPMapAfterAE n u₁ u₂) := by
  obtain ⟨η, hη, hranges⟩ := actualSourcePerturbedImaginaryShifts_surjective_uniform_y u₁ u₂
  apply NlsGge.Spectral.partialMap_selfAdjoint_of_two_imaginary_ranges
    (actualSourcePerturbedDiracPMapAfterAE n u₁ u₂) η
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hη)
    (recoveredActualSourceFreeWeightedDomain_dense n)
    (actualSourcePerturbedDirac_formalSelfAdjoint_of_physical_slice n u₁ u₂ hphysical)
  · intro v
    obtain ⟨w, hw⟩ := (hranges n).1 (-v)
    refine ⟨w, ?_⟩
    calc
      actualSourcePerturbedDiracPMapAfterAE n u₁ u₂ w -
          (Complex.I * (η : ℂ)) • (w : SourcePairL2) =
        -(actualSourcePerturbedShiftedDiracAfterAE n
          (Complex.I * (η : ℂ)) u₁ u₂ w) := by
            rw [actualSourcePerturbedShiftedDirac_eq_smul_sub_sourcePMap]
            abel
      _ = v := by rw [hw]; simp
  · intro v
    obtain ⟨w, hw⟩ := (hranges n).2 (-v)
    refine ⟨w, ?_⟩
    calc
      actualSourcePerturbedDiracPMapAfterAE n u₁ u₂ w +
          (Complex.I * (η : ℂ)) • (w : SourcePairL2) =
        -(actualSourcePerturbedShiftedDiracAfterAE n
          (-Complex.I * (η : ℂ)) u₁ u₂ w) := by
            rw [actualSourcePerturbedShiftedDirac_eq_smul_sub_sourcePMap]
            rw [neg_mul, neg_smul]
            abel
      _ = v := by rw [hw]; simp

end NlsGge.Schur

end
