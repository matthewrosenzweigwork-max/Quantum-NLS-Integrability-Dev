import NlsGge.Schur.PhysicalH1ComplexCarrierSchurBridge
import NlsGge.Analysis.H1Fourier
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur

open NlsGge.Pilot NlsGge.Analysis

local notation "H1WeightRep22" => sobolevModeWeight (1 : ℝ)

private theorem physicalH1ComplexCarrier_sobolev_norm22
    (x : WeightedHilbert H1WeightRep22) :
    ‖physicalSobolevL2 1 (physicalH1ComplexCarrierToL2Actual22 x)
      (physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable x)‖ = ‖x‖ := by
  have hrepr :
      physicalSobolevL2 1 (physicalH1ComplexCarrierToL2Actual22 x)
          (physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable x) =
        weightedLinearMap H1WeightRep22 x := by
    apply lp.ext
    funext n
    change weightedCoordinates H1WeightRep22
        (physicalFourier (physicalH1ComplexCarrierToL2Actual22 x)) n =
      weightedCoordinates H1WeightRep22 (x : ℤ → ℂ) n
    simpa only [weightedCoordinates] using
      congrArg (fun z : ℂ => (Real.sqrt (H1WeightRep22 n) : ℂ) * z)
        (physicalH1ComplexCarrierToL2Actual22_fourier x n)
  rw [hrepr]
  exact (weightedIsometry H1WeightRep22).norm_map x

private theorem physicalH1ComplexCarrier_fourier_add22
    (x y : WeightedHilbert H1WeightRep22) (n : ℤ) :
    physicalFourier (physicalH1ComplexCarrierToL2Actual22 (x + y)) n =
      physicalFourier (physicalH1ComplexCarrierToL2Actual22 x) n +
        physicalFourier (physicalH1ComplexCarrierToL2Actual22 y) n := by
  rw [physicalH1ComplexCarrierToL2Actual22_fourier,
    physicalH1ComplexCarrierToL2Actual22_fourier,
    physicalH1ComplexCarrierToL2Actual22_fourier]
  rfl

private theorem physicalH1ComplexCarrier_fourier_smul22
    (c : ℂ) (x : WeightedHilbert H1WeightRep22) (n : ℤ) :
    physicalFourier (physicalH1ComplexCarrierToL2Actual22 (c • x)) n =
      c * physicalFourier (physicalH1ComplexCarrierToL2Actual22 x) n := by
  rw [physicalH1ComplexCarrierToL2Actual22_fourier,
    physicalH1ComplexCarrierToL2Actual22_fourier]
  rfl

private theorem complex_smul_fourierTerm22
    (c a : ℂ) (f : C(PhysicalCircle, ℂ)) :
    (c * a) • f = c • (a • f) := by
  ext x
  change (c * a) * f x = c * (a * f x)
  ring

/-- The actual continuous H¹ representative depends complex-linearly on the
weighted complex Fourier carrier. Its proof argument records genuine H¹
summability and is supplied by the carrier construction. -/
def physicalH1ComplexCanonicalRepresentativeCLM22 :
    WeightedHilbert H1WeightRep22 →L[ℂ] C(PhysicalCircle, ℂ) := by
  let f : WeightedHilbert H1WeightRep22 →ₗ[ℂ] C(PhysicalCircle, ℂ) := {
    toFun := fun x => physicalH1Continuous
      (physicalH1ComplexCarrierToL2Actual22 x)
      (physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable x)
    map_add' := by
      intro x y
      unfold physicalH1Continuous
      have hx := physicalH1_continuous_fourier_summable
        (physicalH1ComplexCarrierToL2Actual22 x)
        (physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable x)
      have hy := physicalH1_continuous_fourier_summable
        (physicalH1ComplexCarrierToL2Actual22 y)
        (physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable y)
      rw [← hx.tsum_add hy]
      apply tsum_congr
      intro n
      rw [physicalH1ComplexCarrier_fourier_add22]
      exact add_smul
        (physicalFourier (physicalH1ComplexCarrierToL2Actual22 x) n)
        (physicalFourier (physicalH1ComplexCarrierToL2Actual22 y) n)
        (fourier (T := (1 : ℝ)) n)
    map_smul' := by
      intro c x
      unfold physicalH1Continuous
      have hx := physicalH1_continuous_fourier_summable
        (physicalH1ComplexCarrierToL2Actual22 x)
        (physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable x)
      simp only [RingHom.id_apply]
      rw [← hx.tsum_const_smul c]
      apply tsum_congr
      intro n
      rw [physicalH1ComplexCarrier_fourier_smul22]
      exact complex_smul_fourierTerm22 c
        (physicalFourier (physicalH1ComplexCarrierToL2Actual22 x) n)
        (fourier (T := (1 : ℝ)) n)
  }
  exact f.mkContinuous ‖reciprocalBracketL2‖ (by
    intro x
    dsimp [f]
    calc
      ‖physicalH1Continuous
          (physicalH1ComplexCarrierToL2Actual22 x)
          (physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable x)‖ ≤
        ‖physicalSobolevL2 1 (physicalH1ComplexCarrierToL2Actual22 x)
          (physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable x)‖ *
            ‖reciprocalBracketL2‖ :=
        physicalH1Continuous_norm_bound _ _
      _ = ‖reciprocalBracketL2‖ * ‖x‖ := by
        rw [physicalH1ComplexCarrier_sobolev_norm22]
        ring)

theorem physicalH1ComplexCanonicalRepresentativeCLM22_apply
    (x : WeightedHilbert H1WeightRep22) :
    physicalH1ComplexCanonicalRepresentativeCLM22 x =
      physicalH1Continuous (physicalH1ComplexCarrierToL2Actual22 x)
        (physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable x) := rfl

end NlsGge.Schur
