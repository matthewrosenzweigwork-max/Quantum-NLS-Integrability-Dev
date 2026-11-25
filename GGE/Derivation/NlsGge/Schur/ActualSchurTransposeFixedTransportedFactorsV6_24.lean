import NlsGge.Schur.FreeResolventPotentialBlocks
import NlsGge.Schur.FreeResolventComplementaryQDTransportAfterCoordinateRange
import NlsGge.Schur.ResonantParityPairBasisAction
import NlsGge.Schur.ActualSchurCoordinateTransposePrerequisites23
import NlsGge.Schur.ActualPotentialTransposeAfterMatrixEntryPrerequisiteV2_24

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur

open NlsGge.Pilot

private theorem actualPairTranspose_transport_fixed_v6_24
    (n : ℤ) (T : ParityPair n →L[ℂ] ParityPair n)
    (F : SectorSquare n →L[ℂ] SectorSquare n)
    (htransport :
      ((parityPairRepr n).toContinuousLinearEquiv.toContinuousLinearMap).comp
        (T.comp ((parityPairRepr n).toContinuousLinearEquiv.symm.toContinuousLinearMap)) = F)
    (hF : actualCoordinateTranspose23 n F = F) :
    actualPairTransposeAfterCoordinate23 n T = T := by
  let Ec : ParityPair n →L[ℂ] SectorSquare n :=
    (parityPairRepr n).toContinuousLinearEquiv.toContinuousLinearMap
  let Es : SectorSquare n →L[ℂ] ParityPair n :=
    (parityPairRepr n).toContinuousLinearEquiv.symm.toContinuousLinearMap
  apply ContinuousLinearMap.ext
  intro x
  change Es (actualCoordinateTranspose23 n (Ec.comp (T.comp Es)) (Ec x)) = T x
  have hF' :
      actualCoordinateTranspose23 n (Ec.comp (T.comp Es)) =
        Ec.comp (T.comp Es) := by
    calc
      actualCoordinateTranspose23 n (Ec.comp (T.comp Es)) =
          actualCoordinateTranspose23 n F := by rw [htransport]
      _ = F := hF
      _ = Ec.comp (T.comp Es) := htransport.symm
  rw [hF']
  change Es (Ec (T (Es (Ec x)))) = T x
  simp [Ec, Es]

/-- The actual free diagonal is fixed by the transported `J Tᵀ J` operation. -/
theorem actualPairTranspose_freeResolvent_v6_24
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n) :
    actualPairTransposeAfterCoordinate23 n (freeResolventParityPair n z hz) =
      freeResolventParityPair n z hz := by
  let Ec : ParityPair n →L[ℂ] SectorSquare n :=
    (parityPairRepr n).toContinuousLinearEquiv.toContinuousLinearMap
  let Es : SectorSquare n →L[ℂ] ParityPair n :=
    (parityPairRepr n).toContinuousLinearEquiv.symm.toContinuousLinearMap
  have htransport : Ec.comp
      ((freeResolventParityPair n z hz).comp Es) = freeResolventSquare n z hz := by
    ext x i
    simp [Ec, Es, freeResolventParityPair, ContinuousLinearMap.comp_apply]
  exact actualPairTranspose_transport_fixed_v6_24 n _ _ htransport
    (actualCoordinateTranspose23_freeResolvent n z hz)

/-- The actual resonant projection is fixed by the transported transpose. -/
theorem actualPairTranspose_resonant_v6_24 (n : ℤ) :
    actualPairTransposeAfterCoordinate23 n (resonantParityPair n) =
      resonantParityPair n := by
  let Ec : ParityPair n →L[ℂ] SectorSquare n :=
    (parityPairRepr n).toContinuousLinearEquiv.toContinuousLinearMap
  let Es : SectorSquare n →L[ℂ] ParityPair n :=
    (parityPairRepr n).toContinuousLinearEquiv.symm.toContinuousLinearMap
  have htransport : Ec.comp ((resonantParityPair n).comp Es) = resonantSquare n := by
    ext x i
    simp [Ec, Es, resonantParityPair, ContinuousLinearMap.comp_apply]
  exact actualPairTranspose_transport_fixed_v6_24 n _ _ htransport
    (actualCoordinateTranspose23_resonant n)

/-- The actual complementary projection is fixed by the transported transpose. -/
theorem actualPairTranspose_complementary_v6_24 (n : ℤ) :
    actualPairTransposeAfterCoordinate23 n
        (freeResolventComplementaryProjectionTransported n) =
      freeResolventComplementaryProjectionTransported n := by
  let Ec : ParityPair n →L[ℂ] SectorSquare n :=
    (parityPairRepr n).toContinuousLinearEquiv.toContinuousLinearMap
  let Es : SectorSquare n →L[ℂ] ParityPair n :=
    (parityPairRepr n).toContinuousLinearEquiv.symm.toContinuousLinearMap
  have htransport : Ec.comp
      ((freeResolventComplementaryProjectionTransported n).comp Es) =
        complementarySquare n := by
    ext x i
    simp [Ec, Es, freeResolventComplementaryProjectionTransported,
      ContinuousLinearMap.comp_apply]
  exact actualPairTranspose_transport_fixed_v6_24 n _ _ htransport
    (actualCoordinateTranspose23_complementary n)

/-- The passed actual independent-field potential symmetry expressed on the
same `J Tᵀ J` operation used for Schur products. -/
theorem actualPairTranspose_coveredPotential_v6_24
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂)) (n : ℤ) :
    actualPairTransposeAfterCoordinate23 n
        (coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n) =
      coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n :=
  actualPairTransposeAfterMatrixEntryPrerequisiteV2_24_coveredPotential
    u₁ u₂ hu₁ hu₂ n

end NlsGge.Schur
