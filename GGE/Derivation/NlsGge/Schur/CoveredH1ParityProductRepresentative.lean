import NlsGge.Schur.CoveredH1SpectralMultiplier
import NlsGge.Schur.SourceInterval

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace NlsGge.Schur
open NlsGge.Pilot NlsGge.Analysis

/-- The shifted pointwise product of the actual cover multiplier and an
actual parity vector represents the scalar multiple of its L² output. This
isolates the AE representative bridge used by parity commutation. -/
theorem coveredH1SpectralMultiplier_parity_product_smul_ae
    (u : PhysicalL2) (hu : SobolevSquareSummable 1 (physicalFourier u))
    (n : ℤ) (f : scalarParity n) :
    (fun x : SpectralCircle =>
      naturalPhysicalCoverH1Bounded u hu (x + ((1 : ℝ) : SpectralCircle)) *
        f.val (x + ((1 : ℝ) : SpectralCircle))) =ᵐ[spectralHaar]
      fun x => (spectralSign n • coveredH1SpectralMultiplier u hu f.val) x := by
  have hfieldClass := naturalPhysicalCoverH1Bounded_halfShift u hu
  have hfieldEq := Lp.ext_iff.mp hfieldClass
  have hfieldComp := Lp.coeFn_compMeasurePreserving
    (naturalPhysicalCoverH1Bounded u hu) halfShift_preserving
  have hfieldShift :
      (fun x : SpectralCircle => naturalPhysicalCoverH1Bounded u hu
        (x + ((1 : ℝ) : SpectralCircle))) =ᵐ[spectralHaar]
        (fun x => naturalPhysicalCoverH1Bounded u hu x) := by
    filter_upwards [hfieldComp, hfieldEq] with x hc he
    exact hc.symm.trans he
  have hpar := scalarParity_ae_halfShift n f
  have hmult := coveredH1SpectralMultiplier_ae u hu f.val
  filter_upwards [hfieldShift, hpar, hmult,
    Lp.coeFn_smul (spectralSign n) (coveredH1SpectralMultiplier u hu f.val)]
    with x hfield hparx hmul hsmul
  change naturalPhysicalCoverH1Bounded u hu
      (x + ((1 : ℝ) : SpectralCircle)) =
    naturalPhysicalCoverH1Bounded u hu x at hfield
  change f.val (x + ((1 : ℝ) : SpectralCircle)) =
    spectralSign n * f.val x at hparx
  change coveredH1SpectralMultiplier u hu f.val x =
    naturalPhysicalCoverH1Bounded u hu x * f.val x at hmul
  rw [hfield, hparx, hsmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hmul]
  ring

end NlsGge.Schur
