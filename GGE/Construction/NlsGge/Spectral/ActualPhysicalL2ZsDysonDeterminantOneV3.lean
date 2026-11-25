import NlsGge.Spectral.ActualPhysicalL2ZsDysonAEODEV2
import NlsGge.Spectral.ActualComplexZsDeterminantDerivativeCancellationV3
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter MeasureTheory
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-- The determinant of the actual rough-L² Dyson fundamental matrix is
absolutely continuous on the doubled interval. -/
theorem absolutelyContinuous_actualPhysicalL2ZsDysonTsum_det
    (u : PhysicalL2) (z : ℂ) :
    AbsolutelyContinuousOnInterval (fun t => Matrix.det (actualComplexZsDysonTsum
      (fun x => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (x : SpectralCircle))
      z t)) 0 2 := by
  have h00 := absolutelyContinuous_actualPhysicalL2ZsDysonTsum_entry u z 0 0
  have h01 := absolutelyContinuous_actualPhysicalL2ZsDysonTsum_entry u z 0 1
  have h10 := absolutelyContinuous_actualPhysicalL2ZsDysonTsum_entry u z 1 0
  have h11 := absolutelyContinuous_actualPhysicalL2ZsDysonTsum_entry u z 1 1
  simpa only [Matrix.det_fin_two, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] using!
    (h00.smul h11).sub (h01.smul h10)

/-- Tracelessness of the genuine ZS coefficient gives zero determinant
derivative almost everywhere for every physical L² input and complex z. -/
theorem actualPhysicalL2ZsDysonTsum_det_ae_hasDerivAt_zero
    (u : PhysicalL2) (z : ℂ) :
    ∀ᵐ t ∂volume, t ∈ Set.uIcc (0 : ℝ) 2 →
      HasDerivAt (fun s => Matrix.det (actualComplexZsDysonTsum
        (fun x => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (x : SpectralCircle))
        z s)) 0 t := by
  filter_upwards [actualPhysicalL2ZsDysonTsum_ae_hasDerivAt_entry u z 0 0,
    actualPhysicalL2ZsDysonTsum_ae_hasDerivAt_entry u z 0 1,
    actualPhysicalL2ZsDysonTsum_ae_hasDerivAt_entry u z 1 0,
    actualPhysicalL2ZsDysonTsum_ae_hasDerivAt_entry u z 1 1] with t h00 h01 h10 h11
  intro ht
  apply actualComplexZsDeterminant_hasDerivAt_zero
  intro i j
  fin_cases i <;> fin_cases j
  · exact h00 ht
  · exact h01 ht
  · exact h10 ht
  · exact h11 ht

/-- The actual normalized rough-L² fundamental matrix has determinant one
everywhere on the doubled interval. No pointwise continuous field, uniqueness,
gap, quasimomentum or spectral identification assumption is used. -/
theorem actualPhysicalL2ZsDysonTsum_det_one
    (u : PhysicalL2) (z : ℂ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 2) :
    Matrix.det (actualComplexZsDysonTsum
      (fun x => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (x : SpectralCircle))
      z t) = 1 := by
  let U : ℝ → ℂ := fun x =>
    (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (x : SpectralCircle)
  obtain ⟨C, hC⟩ :=
    (absolutelyContinuous_actualPhysicalL2ZsDysonTsum_det u z).const_of_ae_hasDerivAt_zero
      (actualPhysicalL2ZsDysonTsum_det_ae_hasDerivAt_zero u z)
  have hinit : actualComplexZsDysonTsum U z 0 = 1 := by
    ext i j
    exact actualPhysicalL2ZsDysonTsum_initial_entry u z i j
  have hC1 : C = 1 := by
    have h0 := hC 0 (Set.left_mem_uIcc : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) 2)
    change Matrix.det (actualComplexZsDysonTsum U z 0) = C at h0
    rw [hinit, Matrix.det_one] at h0
    exact h0.symm
  have htu : t ∈ Set.uIcc (0 : ℝ) 2 := by
    simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using ht
  exact (hC t htu).trans hC1
end NlsGge.SpectralFoundations
end
