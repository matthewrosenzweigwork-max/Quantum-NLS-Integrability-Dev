import NlsGge.Schur.FreeResolvent
import NlsGge.Schur.ActualFreeResolventCenterScalarPrerequisitesV2_24

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur

/-- The actual center diagonal on the coordinate ℓ² carrier inherits the
sharp signed-gap bound from its scalar coefficients. The sharper bound is
proved on a matching `lp.mapCLM` and transported by equality of operators. -/
theorem freeResolventSquare_center_norm_le_scalarV3_24 (n : ℤ) :
    ‖freeResolventSquare n (spectralCenter n)
      (spectralCenter_mem_spectralDisk_scalarV2_24 n)‖ ≤ 1 / (2 * Real.pi) := by
  let K : ℝ := 1 / (2 * Real.pi)
  let T : ∀ i : Bool × Sector n, ℂ →L[ℂ] ℂ := fun i =>
    freeResolventCoeff n (spectralCenter n) i.2 • ContinuousLinearMap.id ℂ ℂ
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hT : ∀ i : Bool × Sector n, ‖T i‖ ≤ K := by
    intro i
    dsimp [T, K]
    simpa only [norm_smul, ContinuousLinearMap.norm_id, mul_one] using
      freeResolventCoeff_center_norm_le_scalarV2_24 n i.2
  let M : SectorSquare n →L[ℂ] SectorSquare n := lp.mapCLM 2 T hK hT
  have hM : freeResolventSquare n (spectralCenter n)
      (spectralCenter_mem_spectralDisk_scalarV2_24 n) = M := by
    ext x i
    simp [M, T, freeResolventSquare, lp.mapCLM]
  rw [hM]
  simpa only [M, K] using (lp.norm_mapCLM_le 2 T hK hT)

end NlsGge.Schur
