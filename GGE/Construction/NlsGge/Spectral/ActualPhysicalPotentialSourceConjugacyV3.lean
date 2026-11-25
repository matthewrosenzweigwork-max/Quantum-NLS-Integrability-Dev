import NlsGge.Spectral.ActualPhysicalL2SourcePotentialRepresentativeV1
import NlsGge.Analysis.NaturalCoverCoefficients
import Mathlib.MeasureTheory.Function.LpSpace.Basic

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace NlsGge.Schur
open NlsGge.Pilot NlsGge.Analysis

/-- On the physical real-potential slice, the two actual source-interval
representatives are conjugate almost everywhere. The identity is derived from
the physical L² equality and the degree-two measure-preserving cover. -/
theorem actualPhysicalL2SourcePotential_star_ae
    (u₁ u₂ : PhysicalL2) (h : u₂ = star u₁) :
    (actualPhysicalL2SourcePotential u₂ : ℝ → ℂ) =ᵐ[
      volume.restrict (Set.Ioc (0 : ℝ) 1)]
      fun t => star (actualPhysicalL2SourcePotential u₁ t) := by
  have hclass : (u₂ : PhysicalCircle → ℂ) =ᵐ[spatialMeasure]
      (star u₁ : PhysicalCircle → ℂ) :=
    (Lp.ext_iff.mp h).trans (Lp.coeFn_star u₁)
  have hclassCover :=
    naturalPhysicalCover_preserving.quasiMeasurePreserving.ae_eq_comp hclass
  have hcover := spectral_ae_pullback_first_half hclassCover
  have h₁ := actualPhysicalL2SourcePotential_ae u₁
  have h₂ := actualPhysicalL2SourcePotential_ae u₂
  filter_upwards [h₁, h₂, hcover] with t h₁t h₂t hcovert
  calc
    actualPhysicalL2SourcePotential u₂ t = u₂ ((t : ℝ) : PhysicalCircle) := h₂t
    _ = star (u₁ ((t : ℝ) : PhysicalCircle)) := by
      simpa only [Function.comp_apply, naturalPhysicalCover_coe, Pi.star_apply] using hcovert
    _ = star (actualPhysicalL2SourcePotential u₁ t) := by rw [← h₁t]


end NlsGge.Schur

end
