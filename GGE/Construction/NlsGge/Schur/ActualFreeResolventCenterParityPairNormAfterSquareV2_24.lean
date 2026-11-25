import NlsGge.Schur.FreeResolventPotentialBlocks
import NlsGge.Schur.ActualFreeResolventCenterSquareNormAfterScalarV3_24

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur

/-- The sharper coordinate center estimate transports to the actual paired
parity carrier through the existing complete Fourier isometry. -/
theorem freeResolventParityPair_center_norm_le_afterSquareV2_24 (n : ℤ) :
    ‖freeResolventParityPair n (spectralCenter n)
      (spectralCenter_mem_spectralDisk_scalarV2_24 n)‖ ≤ 1 / (2 * Real.pi) := by
  let E := parityPairRepr n
  let F := freeResolventSquare n (spectralCenter n)
    (spectralCenter_mem_spectralDisk_scalarV2_24 n)
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  change ‖E.symm (F (E x))‖ ≤ (1 / (2 * Real.pi)) * ‖x‖
  calc
    ‖E.symm (F (E x))‖ = ‖F (E x)‖ := E.symm.norm_map _
    _ ≤ ‖F‖ * ‖E x‖ := F.le_opNorm _
    _ ≤ (1 / (2 * Real.pi)) * ‖x‖ := by
      rw [E.norm_map]
      gcongr
      exact freeResolventSquare_center_norm_le_scalarV3_24 n

end NlsGge.Schur
