import NlsGge.Spectral.ActualL2PotentialTimesLInfStateV1

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace NlsGge.Schur
open NlsGge.Pilot NlsGge.Analysis

/-- The source-interval parity representative of the physical L² potential is
the actual physical field pulled back to the unit interval, almost everywhere.
This makes the cover and parity-restriction construction source-faithful. -/
theorem actualPhysicalL2SourcePotential_ae (u : PhysicalL2) :
    (actualPhysicalL2SourcePotential u : ℝ → ℂ) =ᵐ[
      volume.restrict (Set.Ioc (0 : ℝ) 1)]
      fun x => u ((x : ℝ) : PhysicalCircle) := by
  have hrestrict :
      (actualPhysicalL2SourcePotential u : ℝ → ℂ) =ᵐ[
        volume.restrict (Set.Ioc (0 : ℝ) 1)]
        fun x => naturalPhysicalCoverL2 u ((x : ℝ) : SpectralCircle) := by
    change scalarParityRestrictValue 0
        ⟨naturalPhysicalCoverL2 u, naturalPhysicalCoverL2_mem_even u⟩ =ᵐ[
          volume.restrict (Set.Ioc (0 : ℝ) 1)]
      fun x => naturalPhysicalCoverL2 u ((x : ℝ) : SpectralCircle)
    exact scalarParityRestrictValue_ae 0
      ⟨naturalPhysicalCoverL2 u, naturalPhysicalCoverL2_mem_even u⟩
  have hcover := spectral_ae_pullback_first_half (naturalPhysicalCoverL2_ae u)
  filter_upwards [hrestrict, hcover] with x hx hcoverx
  calc
    actualPhysicalL2SourcePotential u x =
        naturalPhysicalCoverL2 u ((x : ℝ) : SpectralCircle) := hx
    _ = u (naturalPhysicalCover ((x : ℝ) : SpectralCircle)) := hcoverx
    _ = u ((x : ℝ) : PhysicalCircle) := by rw [naturalPhysicalCover_coe]

end NlsGge.Schur

end
