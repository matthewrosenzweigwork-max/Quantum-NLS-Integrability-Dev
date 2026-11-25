import NlsGge.Schur.CoveredH1FourierIntegrand
import NlsGge.Analysis.FullCoverFourier
import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace NlsGge.Schur
open NlsGge.Pilot NlsGge.Analysis

/-- The H¹ cover representative and the actual cover-L² representative have
the same Fourier coefficients. -/
theorem naturalPhysicalCoverH1Bounded_fourierCoeff (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) (k : ℤ) :
    fourierCoeff (naturalPhysicalCoverH1Bounded u hu) k =
      if k % 2 = 0 then physicalFourier u (k / 2) else 0 := by
  have hae : (naturalPhysicalCoverH1Bounded u hu : SpectralCircle → ℂ) =ᵐ[spectralHaar]
      (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) :=
    (naturalPhysicalCoverH1Bounded_ae u hu).trans (naturalPhysicalCoverL2_ae u).symm
  have hcoeff : fourierCoeff (naturalPhysicalCoverH1Bounded u hu) k =
      fourierCoeff (naturalPhysicalCoverL2 u) k := by
    rw [fourierCoeff, fourierCoeff]
    apply integral_congr_ae
    filter_upwards [hae] with x hx
    rw [hx]
  rw [hcoeff]
  exact naturalPhysicalCoverL2_fourier_all u k

/-- The scalar Fourier multiplier matrix entry, assembled from the proved
AE integrand identity and the actual probability-Haar coefficient integral. -/
theorem coveredH1SpectralMultiplier_matrix_entry (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) (m l : ℤ) :
    inner ℂ (spectralBasis m)
        (coveredH1SpectralMultiplier u hu (spectralBasis (-l))) =
      fourierCoeff (naturalPhysicalCoverH1Bounded u hu) (m + l) := by
  rw [L2.inner_def]
  calc
    (∫ x : SpectralCircle,
        inner ℂ (spectralBasis m x)
          (coveredH1SpectralMultiplier u hu (spectralBasis (-l)) x) ∂spectralHaar) =
      ∫ x : SpectralCircle,
        fourier (-(m + l)) x * naturalPhysicalCoverH1Bounded u hu x ∂spectralHaar := by
          exact integral_congr_ae
            (coveredH1SpectralMultiplier_character_integrand_ae u hu m l)
    _ = fourierCoeff (naturalPhysicalCoverH1Bounded u hu) (m + l) := by
      rw [fourierCoeff]
      change (∫ x : AddCircle (2 : ℝ),
          fourier (-(m + l)) x * naturalPhysicalCoverH1Bounded u hu x
            ∂AddCircle.haarAddCircle) = _
      simp only [smul_eq_mul]

/-- Upper off-diagonal source convention: the lower input has frequency `-l`. -/
theorem coveredH1SpectralMultiplier_upper_entry (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) (m l : ℤ) :
    inner ℂ (spectralBasis m)
        (coveredH1SpectralMultiplier u hu (spectralBasis (-l))) =
      if (m + l) % 2 = 0 then physicalFourier u ((m + l) / 2) else 0 := by
  rw [coveredH1SpectralMultiplier_matrix_entry, naturalPhysicalCoverH1Bounded_fourierCoeff]

/-- Lower off-diagonal source convention: reflected output frequency is `-m`. -/
theorem coveredH1SpectralMultiplier_lower_entry (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) (m l : ℤ) :
    inner ℂ (spectralBasis (-m))
        (coveredH1SpectralMultiplier u hu (spectralBasis l)) =
      if (m + l) % 2 = 0 then physicalFourier u (-(m + l) / 2) else 0 := by
  have hentry := coveredH1SpectralMultiplier_matrix_entry u hu (m := -m) (l := -l)
  have hindex : -m + -l = -(m + l) := by ring
  rw [hindex] at hentry
  have hentry' : inner ℂ (spectralBasis (-m))
      (coveredH1SpectralMultiplier u hu (spectralBasis l)) =
      fourierCoeff (naturalPhysicalCoverH1Bounded u hu) (-(m + l)) := by
    simpa only [Int.neg_neg] using hentry
  rw [hentry', naturalPhysicalCoverH1Bounded_fourierCoeff]
  by_cases h : (m + l) % 2 = 0
  · have hneg : (-(m + l)) % 2 = 0 := by omega
    rw [if_pos h, if_pos hneg]
  · have hneg : (-(m + l)) % 2 ≠ 0 := by omega
    rw [if_neg h, if_neg hneg]

end NlsGge.Schur
