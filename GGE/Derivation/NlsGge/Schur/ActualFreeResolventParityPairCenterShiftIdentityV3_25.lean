import NlsGge.Schur.FreeResolventPotentialBlocks
import NlsGge.Schur.FreeResolventPotentialMatrixEntriesAfterInnerScalar
import NlsGge.Schur.ActualFreeResolventCenterScalarPrerequisitesV2_24
import NlsGge.Schur.ActualCenterShiftRightAssociatedVectorActionPrerequisiteV1_25

set_option autoImplicit false
noncomputable section
open scoped InnerProduct InnerProductSpace

namespace NlsGge.Schur

/-- The actual transported paired-carrier diagonal satisfies the center-shift
identity on the full signed disk. The proof checks the identity on the actual
complete Fourier basis using the pinned scalar coefficient law. -/
theorem freeResolventParityPair_center_shift_identity_v3_25
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n) :
    (1 + (z - spectralCenter n) •
        freeResolventParityPair n (spectralCenter n)
          (spectralCenter_mem_spectralDisk_scalarV2_24 n)) *
      freeResolventParityPair n z hz =
        freeResolventParityPair n (spectralCenter n)
          (spectralCenter_mem_spectralDisk_scalarV2_24 n) := by
  have hdense : Dense
      (↑(Submodule.span ℂ (Set.range (parityPairFourierBasis n))) : Set (ParityPair n)) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr
      (parityPairFourierBasis n).dense_span
  apply ContinuousLinearMap.ext_on hdense
  intro x hx
  rcases hx with ⟨j, rfl⟩
  have hj : parityPairFourierBasis n j = parityPairVector n j := by
    simp only [parityPairFourierBasis, HilbertBasis.coe_mkOfOrthogonalEqBot]
  rw [hj]
  have hcoef := freeResolventCoeff_center_shift_identity_scalarV2_24 n z hz j.2
  have hcenter := freeResolventParityPair_apply_basis n (spectralCenter n)
    (spectralCenter_mem_spectralDisk_scalarV2_24 n) j
  have hzj := freeResolventParityPair_apply_basis n z hz j
  rw [ContinuousLinearMap.mul_def]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    one_apply_eq_self, ContinuousLinearMap.smul_apply]
  rw [hzj, map_smul, hcenter]
  simp only [smul_smul]
  have hscalar :
      freeResolventCoeff n z j.2 +
        (z - spectralCenter n) *
          (freeResolventCoeff n z j.2 * freeResolventCoeff n (spectralCenter n) j.2) =
        freeResolventCoeff n (spectralCenter n) j.2 := by
    calc
      _ = (1 + (z - spectralCenter n) *
          freeResolventCoeff n (spectralCenter n) j.2) *
            freeResolventCoeff n z j.2 := by ring
      _ = _ := hcoef
  calc
    freeResolventCoeff n z j.2 • parityPairVector n j +
        ((z - spectralCenter n) *
          (freeResolventCoeff n z j.2 * freeResolventCoeff n (spectralCenter n) j.2)) •
          parityPairVector n j =
      (freeResolventCoeff n z j.2 +
        (z - spectralCenter n) *
          (freeResolventCoeff n z j.2 * freeResolventCoeff n (spectralCenter n) j.2)) •
        parityPairVector n j := by
          exact actualCenterShiftRightAssociatedVectorActionPrerequisiteV1_25
            n (freeResolventCoeff n z j.2) (z - spectralCenter n)
            (freeResolventCoeff n z j.2)
            (freeResolventCoeff n (spectralCenter n) j.2)
            (parityPairVector n j)
    _ = freeResolventCoeff n (spectralCenter n) j.2 • parityPairVector n j := by
      rw [hscalar]

end NlsGge.Schur
