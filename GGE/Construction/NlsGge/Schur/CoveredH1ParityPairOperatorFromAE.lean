import NlsGge.Schur.CoveredH1SpectralMultiplier
import NlsGge.Schur.CoveredH1ParityProductRepresentative
import NlsGge.Schur.PhysicalSector
import Mathlib.Analysis.Normed.Lp.PiLp

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace NlsGge.Schur
open NlsGge.Pilot NlsGge.Analysis

/-- The actual cover multiplier commutes with the actual half-period translation,
assembled from the checked AE product-representative bridge. -/
theorem coveredH1SpectralMultiplier_halfTranslation
    (u : PhysicalL2) (hu : SobolevSquareSummable 1 (physicalFourier u))
    (n : ℤ) (f : scalarParity n) :
    halfTranslation (coveredH1SpectralMultiplier u hu f.val) =
      spectralSign n • coveredH1SpectralMultiplier u hu f.val := by
  apply Lp.ext
  have hmult := coveredH1SpectralMultiplier_ae u hu f.val
  have hmultShift := halfShift_preserving.quasiMeasurePreserving.ae_eq_comp hmult
  have hproduct := coveredH1SpectralMultiplier_parity_product_smul_ae u hu n f
  filter_upwards [halfTranslation_ae (coveredH1SpectralMultiplier u hu f.val),
    hmultShift, hproduct] with x hout hmulShift hproduct
  change halfTranslation (coveredH1SpectralMultiplier u hu f.val) x =
    (spectralSign n • coveredH1SpectralMultiplier u hu f.val) x
  change halfTranslation (coveredH1SpectralMultiplier u hu f.val) x =
    coveredH1SpectralMultiplier u hu f.val (x + ((1 : ℝ) : SpectralCircle)) at hout
  change coveredH1SpectralMultiplier u hu f.val (x + ((1 : ℝ) : SpectralCircle)) =
    naturalPhysicalCoverH1Bounded u hu (x + ((1 : ℝ) : SpectralCircle)) *
      f.val (x + ((1 : ℝ) : SpectralCircle)) at hmulShift
  rw [hout, hmulShift, hproduct]

/-- The scalar multiplier restricted to the actual parity eigenspace. -/
def coveredH1ScalarParityMultiplier (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) (n : ℤ) :
    scalarParity n →L[ℂ] scalarParity n :=
  ((coveredH1SpectralMultiplier u hu).comp (scalarParity n).subtypeL).codRestrict
    (scalarParity n)
    (fun f => (mem_scalarParity n _).mpr
      (coveredH1SpectralMultiplier_halfTranslation u hu n f))

@[simp] theorem coveredH1ScalarParityMultiplier_coe_apply
    (u : PhysicalL2) (hu : SobolevSquareSummable 1 (physicalFourier u))
    (n : ℤ) (f : scalarParity n) :
    (coveredH1ScalarParityMultiplier u hu n f : SpectralScalarL2) =
      coveredH1SpectralMultiplier u hu f.val := rfl

/-- The two actual independent cover fields define the off-diagonal CLM on
the complete paired parity space. -/
def coveredH1ParityPairPotential (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂)) (n : ℤ) :
    ParityPair n →L[ℂ] ParityPair n := by
  let e := PiLp.continuousLinearEquiv 2 ℂ (fun _ : Bool => scalarParity n)
  let f : (Bool → scalarParity n) →L[ℂ] (Bool → scalarParity n) :=
    ContinuousLinearMap.pi (fun b : Bool =>
      if b then
        (coveredH1ScalarParityMultiplier u₁ hu₁ n).comp
          (ContinuousLinearMap.proj false)
      else
        (coveredH1ScalarParityMultiplier u₂ hu₂ n).comp
          (ContinuousLinearMap.proj true))
  exact e.symm.toContinuousLinearMap.comp (f.comp e.toContinuousLinearMap)

@[simp] theorem coveredH1ParityPairPotential_apply_true
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂)) (n : ℤ)
    (f : ParityPair n) :
    coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n f true =
      coveredH1ScalarParityMultiplier u₁ hu₁ n (f false) := by
  simp [coveredH1ParityPairPotential]

@[simp] theorem coveredH1ParityPairPotential_apply_false
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂)) (n : ℤ)
    (f : ParityPair n) :
    coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n f false =
      coveredH1ScalarParityMultiplier u₂ hu₂ n (f true) := by
  simp [coveredH1ParityPairPotential]

end NlsGge.Schur
