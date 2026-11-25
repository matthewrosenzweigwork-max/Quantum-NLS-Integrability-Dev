import NlsGge.Spectral.ActualPhysicalL2SourcePotentialRepresentativeV1
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace NlsGge.Schur
open NlsGge.Pilot NlsGge.Analysis
/-- Public version of the actual accepted parity-restriction representative bridge. -/
theorem actualPhysicalSourcePotential_rawCover_ae32 (u : PhysicalL2) :
    (actualPhysicalL2SourcePotential u : ℝ → ℂ) =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)]
      fun x => naturalPhysicalCoverL2 u (x : SpectralCircle) := by
  change scalarParityRestrictValue 0
    ⟨naturalPhysicalCoverL2 u, naturalPhysicalCoverL2_mem_even u⟩ =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)]
      fun x => naturalPhysicalCoverL2 u (x : SpectralCircle)
  exact scalarParityRestrictValue_ae 0
    ⟨naturalPhysicalCoverL2 u, naturalPhysicalCoverL2_mem_even u⟩
/-- The actual raw Dyson potential has exactly the physical squared norm on the unit interval. -/
theorem actualPhysicalRawCover_unitIntegral_norm_sq32 (u : PhysicalL2) :
    (∫ x in Set.Ioc (0 : ℝ) 1, ‖naturalPhysicalCoverL2 u (x : SpectralCircle)‖ ^ 2) = ‖u‖ ^ 2 := by
  calc
    (∫ x in Set.Ioc (0 : ℝ) 1, ‖naturalPhysicalCoverL2 u (x : SpectralCircle)‖ ^ 2) =
        ∫ x in Set.Ioc (0 : ℝ) 1, ‖actualPhysicalL2SourcePotential u x‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [actualPhysicalSourcePotential_rawCover_ae32 u] with x hx
      rw [hx]
    _ = ‖actualPhysicalL2SourcePotential u‖ ^ 2 := (sourceInterval_norm_sq _).symm
    _ = ‖u‖ ^ 2 := by rw [actualPhysicalL2SourcePotential_norm]
end NlsGge.Schur
end
