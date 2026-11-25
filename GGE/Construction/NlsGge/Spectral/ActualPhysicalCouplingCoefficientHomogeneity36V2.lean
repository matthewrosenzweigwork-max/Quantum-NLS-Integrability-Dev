import NlsGge.Spectral.ActualInteractionPairKernel32V2
import NlsGge.Spectral.ActualPhysicalUnitRawCoverNorm32V1
import NlsGge.Spectral.GenericRoughDysonScalarHomogeneity36V2
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis
/-- Scalar multiplication of actual L² equivalence classes commutes with the
raw cover representative only almost everywhere on the unit source interval. -/
theorem actualPhysicalRawCover_scalarCoupling_ae36V2 (u : PhysicalL2) (c : ℂ) :
    (fun t : ℝ => naturalPhysicalCoverL2 (c • u) (t : SpectralCircle))
      =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)]
    (fun t : ℝ => c * naturalPhysicalCoverL2 u (t : SpectralCircle)) := by
  rw [naturalPhysicalCoverL2.map_smul]
  simpa only [Pi.smul_apply, smul_eq_mul] using
    spectral_ae_pullback_first_half (Lp.coeFn_smul c (naturalPhysicalCoverL2 u))
/-- REAL coupling scales both U and star(U) by the same real coefficient.
The statement does not change the ensemble or allow arbitrary complex scaling
of the conjugated source channel. -/
theorem actualInteractionCoefficient_realCoupling36V2
    (U : ℝ → ℂ) (τ : ℝ) (z : ℂ) (t : ℝ) :
    actualZsInteractionCoefficient32 (fun s => (τ : ℂ)*U s) z t =
      (τ : ℂ) • actualZsInteractionCoefficient32 U z t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [actualZsInteractionCoefficient32, zsCoefficientComplex,
      Pi.smul_apply, smul_eq_mul, star_mul] <;> ring
/-- Every finite ordered Dyson term of the actual-defined interaction matrix
scales by τ^n along the real coupling path. Transfer to raw representatives of
τ•u uses the separate AE lemma and still requires finite-order integral congruence. -/
theorem actualInteractionDysonTerm_realCoupling36V2
    (U : ℝ → ℂ) (τ : ℝ) (z : ℂ) (n : ℕ) (t : ℝ) :
    genericRoughMatrixDysonTerm32
      (actualZsInteractionCoefficient32 (fun s => (τ : ℂ)*U s) z) n t =
    (τ : ℂ)^n • genericRoughMatrixDysonTerm32
      (actualZsInteractionCoefficient32 U z) n t := by
  have hB : actualZsInteractionCoefficient32 (fun s => (τ : ℂ)*U s) z =
      (fun s => (τ : ℂ) • actualZsInteractionCoefficient32 U z s) := by
    funext s
    exact actualInteractionCoefficient_realCoupling36V2 U τ z s
  rw [hB]
  exact genericRoughMatrixDysonTerm_scalarHomogeneity36V2
    (actualZsInteractionCoefficient32 U z) (τ : ℂ) n t
end NlsGge.SpectralFoundations
end
