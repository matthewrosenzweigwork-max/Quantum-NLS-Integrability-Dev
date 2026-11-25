import NlsGge.Definitions.PilotInterfaces
import NlsGge.Schur.FourierMultiplier
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.Algebra.Group.Quotient

/-! Actual degree-two Haar cover.  Real coordinates are unchanged: this is
x mod 2 ↦ x mod 1, and its L2 pullback is an embedding, not an equivalence. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace NlsGge.Analysis
open NlsGge.Pilot NlsGge.Schur

theorem doublePeriod_subgroup_le :
    AddSubgroup.zmultiples (2 : ℝ) ≤
      (AddSubgroup.zmultiples (1 : ℝ)).comap (AddMonoidHom.id ℝ) := by
  apply AddSubgroup.zmultiples_le.mpr
  change (2 : ℝ) ∈ AddSubgroup.zmultiples (1 : ℝ)
  exact AddSubgroup.mem_zmultiples_iff.mpr ⟨(2 : ℤ), by norm_num⟩

def naturalPhysicalCover : SpectralCircle →+ PhysicalCircle :=
  QuotientAddGroup.map (AddSubgroup.zmultiples (2 : ℝ))
    (AddSubgroup.zmultiples (1 : ℝ)) (AddMonoidHom.id ℝ) doublePeriod_subgroup_le

theorem naturalPhysicalCover_coe (x : ℝ) :
    naturalPhysicalCover (x : SpectralCircle) = (x : PhysicalCircle) := rfl

theorem naturalPhysicalCover_continuous : Continuous naturalPhysicalCover := by
  rw [(QuotientAddGroup.isQuotientMap_mk
    (AddSubgroup.zmultiples (2 : ℝ))).continuous_iff]
  change Continuous (fun x : ℝ => (x : PhysicalCircle))
  exact QuotientAddGroup.continuous_mk

theorem naturalPhysicalCover_surjective : Function.Surjective naturalPhysicalCover := by
  intro y
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
  exact ⟨(x : SpectralCircle), rfl⟩

theorem naturalPhysicalCover_preserving :
    MeasurePreserving naturalPhysicalCover spectralHaar spatialMeasure := by
  haveI : spectralHaar.IsAddHaarMeasure := by unfold spectralHaar; infer_instance
  haveI : spatialMeasure.IsAddHaarMeasure := by unfold spatialMeasure; infer_instance
  exact AddMonoidHom.measurePreserving naturalPhysicalCover_continuous
    naturalPhysicalCover_surjective (by simp [spectralHaar, spatialMeasure])

theorem naturalPhysicalCover_halfShift (x : SpectralCircle) :
    naturalPhysicalCover (x + ((1 : ℝ) : SpectralCircle)) = naturalPhysicalCover x := by
  rw [map_add, naturalPhysicalCover_coe, AddCircle.coe_period, add_zero]

def naturalPhysicalCoverL2 : PhysicalL2 →ₗᵢ[ℂ] SpectralScalarL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ naturalPhysicalCover naturalPhysicalCover_preserving

theorem naturalPhysicalCoverL2_ae (u : PhysicalL2) :
    (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) =ᵐ[spectralHaar]
      fun x => u (naturalPhysicalCover x) :=
  Lp.coeFn_compMeasurePreserving u naturalPhysicalCover_preserving

theorem naturalPhysicalCoverL2_norm (u : PhysicalL2) :
    ‖naturalPhysicalCoverL2 u‖ = ‖u‖ := naturalPhysicalCoverL2.norm_map u

theorem naturalPhysicalCover_fourier (p : ℤ) (x : SpectralCircle) :
    fourier p (naturalPhysicalCover x) = fourier (2 * p) x := by
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [naturalPhysicalCover_coe, fourier_coe_apply, fourier_coe_apply]
  congr 1
  push_cast
  ring

end NlsGge.Analysis
