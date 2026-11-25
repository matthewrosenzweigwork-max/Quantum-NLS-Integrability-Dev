import NlsGge.Schur.FreeResolventPotentialBlocks
import NlsGge.Schur.ActualFreeResolventCenterScalarPrerequisitesV2_24
import Mathlib.Analysis.Normed.Operator.ContinuousAlgEquiv

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur

/-- The actual Fourier isometry transports endomorphisms of the coordinate
carrier to endomorphisms of the paired carrier. -/
def actualCoordinatePairEndomorphismConjugacyV2_26 (n : ℤ) :
    (SectorSquare n →L[ℂ] SectorSquare n) ≃A[ℂ]
      (ParityPair n →L[ℂ] ParityPair n) :=
  (parityPairRepr n).toContinuousLinearEquiv.symm.conjContinuousAlgEquiv

/-- The actual center factor on the paired carrier is the image of the actual
coordinate center factor under the Fourier-isometry algebra equivalence. -/
theorem actualCoordinatePairCenterFactor_conjugacyV2_26
    (n : ℤ) (z : ℂ) :
    actualCoordinatePairEndomorphismConjugacyV2_26 n
        (1 + (z - spectralCenter n) •
          freeResolventSquare n (spectralCenter n)
            (spectralCenter_mem_spectralDisk_scalarV2_24 n)) =
      1 + (z - spectralCenter n) •
        freeResolventParityPair n (spectralCenter n)
          (spectralCenter_mem_spectralDisk_scalarV2_24 n) := by
  simp only [actualCoordinatePairEndomorphismConjugacyV2_26,
    map_add, map_one, map_smul]
  congr 1

end NlsGge.Schur
