import NlsGge.Hierarchy.RiccatiUnweightedRealIsometryCoordinateSecond
import NlsGge.Hierarchy.RiccatiPhysicalFourierL2SymmCoefficientsSecond
import NlsGge.Hierarchy.RiccatiPhysicalH1EnergyCandidateAfterFourierCoefficientPrerequisite
import NlsGge.Analysis.PhysicalH1Bounds
import NlsGge.Sobolev.SourceEmbeddings
import NlsGge.Sobolev.WeightedHilbert
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

/-! The actual weighted-real Sobolev carrier is mapped to PhysicalL2 using
the accepted real-restricted constant-weight coordinate isometry. The source
H¹ summability, norm identity, and canonical representative/energy estimates
are then transported without adding hypotheses. Weak-derivative identification
and continuity/equality with the source Q₂ charge remain separate theorems. -/

namespace NlsGge.Pilot

open NlsGge.Analysis

local notation "H1Weight" => (sobolevModeWeight (1 : ℝ))
local instance : Fact (∀ n : ℤ, 0 < (1 : ℝ)) := ⟨by norm_num⟩

private theorem physicalH1Weight_ge_one (n : ℤ) : (1 : ℝ) ≤ H1Weight n := by
  change 1 ≤ Real.rpow (japaneseBracket n) (2 * (1 : ℝ))
  rw [japaneseBracket_h1_weight]
  nlinarith [sq_nonneg (n : ℝ)]

def physicalH1CarrierToUnweighted :
    WeightedRealHilbert H1Weight →L[ℝ]
      WeightedRealHilbert (fun _ : ℤ => (1 : ℝ)) :=
  weightedRealComparisonContinuous H1Weight (fun _ : ℤ => (1 : ℝ)) 1
    (by norm_num) (fun n => by simpa only [one_mul] using physicalH1Weight_ge_one n)

def physicalH1UnweightedToLp :
    WeightedRealHilbert (fun _ : ℤ => (1 : ℝ)) →L[ℝ]
      lp (fun _ : ℤ => ℂ) 2 := by
  let U : WeightedHilbert (fun _ : ℤ => (1 : ℝ)) ≃ₗᵢ[ℂ]
      lp (fun _ : ℤ => ℂ) 2 := weightedIsometry (fun _ : ℤ => (1 : ℝ))
  let Uclm : WeightedHilbert (fun _ : ℤ => (1 : ℝ)) →L[ℂ]
      lp (fun _ : ℤ => ℂ) 2 := U.toContinuousLinearEquiv.toContinuousLinearMap
  exact Uclm.restrictScalars ℝ

theorem physicalH1CarrierToLp_coordinate (x : SobolevHilbert 1) (n : ℤ) :
    (physicalH1UnweightedToLp (physicalH1CarrierToUnweighted x)) n =
      (show WeightedHilbert H1Weight from x) n := by
  change (weightedIsometry (fun _ : ℤ => (1 : ℝ))
    (show WeightedHilbert (fun _ : ℤ => (1 : ℝ)) from physicalH1CarrierToUnweighted x)) n = _
  rw [unweightedRealIsometry_coordinateSecond]
  exact weightedRealComparison_apply H1Weight (fun _ : ℤ => (1 : ℝ)) 1
    (by norm_num)
    (fun k => by simpa only [one_mul] using physicalH1Weight_ge_one k) x n

def physicalH1CarrierToL2AfterAcceptedCoordinate :
    SobolevHilbert 1 →L[ℝ] PhysicalL2 :=
  ((physicalFourierL2.symm.toContinuousLinearEquiv.toContinuousLinearMap).restrictScalars ℝ).comp
    (physicalH1UnweightedToLp.comp
      (physicalH1CarrierToUnweighted : SobolevHilbert 1 →L[ℝ]
        WeightedRealHilbert (fun _ : ℤ => (1 : ℝ))))

theorem physicalH1CarrierToL2AfterAcceptedCoordinate_fourier
    (x : SobolevHilbert 1) (n : ℤ) :
    physicalFourier (physicalH1CarrierToL2AfterAcceptedCoordinate x) n =
      (show WeightedHilbert H1Weight from x) n := by
  change physicalFourier (physicalFourierL2.symm
    (physicalH1UnweightedToLp (physicalH1CarrierToUnweighted x))) n = _
  rw [physicalFourier_symm_apply, physicalH1CarrierToLp_coordinate]

theorem physicalH1CarrierToL2AfterAcceptedCoordinate_sobolevSquareSummable
    (x : SobolevHilbert 1) :
    SobolevSquareSummable 1
      (physicalFourier (physicalH1CarrierToL2AfterAcceptedCoordinate x)) := by
  unfold SobolevSquareSummable
  have hs := (weightedHilbert_hasSum H1Weight
    (show WeightedHilbert H1Weight from x)).summable
  change Summable (fun n : ℤ =>
    Real.rpow (japaneseBracket n) (2 * (1 : ℝ)) *
      ‖physicalFourier (physicalH1CarrierToL2AfterAcceptedCoordinate x) n‖ ^ 2)
  apply hs.congr
  intro n
  rw [physicalH1CarrierToL2AfterAcceptedCoordinate_fourier]
  simp only [sobolevModeWeight]

theorem physicalH1CarrierSobolevL2_norm_afterAcceptedCoordinate
    (x : SobolevHilbert 1) :
    ‖physicalSobolevL2 1 (physicalH1CarrierToL2AfterAcceptedCoordinate x)
      (physicalH1CarrierToL2AfterAcceptedCoordinate_sobolevSquareSummable x)‖ = ‖x‖ := by
  have hleft := physicalSobolevL2_norm_sq 1
    (physicalH1CarrierToL2AfterAcceptedCoordinate x)
    (physicalH1CarrierToL2AfterAcceptedCoordinate_sobolevSquareSummable x)
  have hright := weightedHilbert_norm_sq H1Weight
    (show WeightedHilbert H1Weight from x)
  have hsquare :
      ‖physicalSobolevL2 1 (physicalH1CarrierToL2AfterAcceptedCoordinate x)
        (physicalH1CarrierToL2AfterAcceptedCoordinate_sobolevSquareSummable x)‖ ^ 2 = ‖x‖ ^ 2 := by
    calc
      _ = ∑' n : ℤ,
          Real.rpow (japaneseBracket n) (2 * (1 : ℝ)) *
            ‖physicalFourier (physicalH1CarrierToL2AfterAcceptedCoordinate x) n‖ ^ 2 := hleft
      _ = ∑' n : ℤ,
          H1Weight n * ‖(show WeightedHilbert H1Weight from x) n‖ ^ 2 := by
        apply tsum_congr
        intro n
        rw [physicalH1CarrierToL2AfterAcceptedCoordinate_fourier]
        simp only [sobolevModeWeight]
      _ = ‖x‖ ^ 2 := hright.symm
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsquare

def physicalH1CarrierContinuousAfterAcceptedCoordinate (x : SobolevHilbert 1) :
    C(PhysicalCircle, ℂ) :=
  physicalH1Continuous (physicalH1CarrierToL2AfterAcceptedCoordinate x)
    (physicalH1CarrierToL2AfterAcceptedCoordinate_sobolevSquareSummable x)

theorem physicalH1CarrierContinuousAfterAcceptedCoordinate_norm_le
    (x : SobolevHilbert 1) :
    ‖physicalH1CarrierContinuousAfterAcceptedCoordinate x‖ ≤
      ‖x‖ * ‖reciprocalBracketL2‖ := by
  have h := physicalH1Continuous_norm_bound
    (physicalH1CarrierToL2AfterAcceptedCoordinate x)
    (physicalH1CarrierToL2AfterAcceptedCoordinate_sobolevSquareSummable x)
  rw [physicalH1CarrierSobolevL2_norm_afterAcceptedCoordinate] at h
  exact h

theorem physicalH1CarrierDerivativeClass_norm_leAfterAcceptedCoordinate
    (x : SobolevHilbert 1) :
    ‖physicalH1FourierDerivativeClass
      (physicalH1CarrierToL2AfterAcceptedCoordinate x)
      (physicalH1CarrierToL2AfterAcceptedCoordinate_sobolevSquareSummable x)‖ ≤
        (2 * Real.pi) * ‖x‖ := by
  have h := physicalH1FourierDerivativeClass_norm_le
    (physicalH1CarrierToL2AfterAcceptedCoordinate x)
    (physicalH1CarrierToL2AfterAcceptedCoordinate_sobolevSquareSummable x)
  rw [physicalH1CarrierSobolevL2_norm_afterAcceptedCoordinate] at h
  exact h

def physicalH1CarrierEnergyCandidateAfterAcceptedCoordinate
    (x : SobolevHilbert 1) : ℝ :=
  physicalH1EnergyCandidate (physicalH1CarrierToL2AfterAcceptedCoordinate x)
    (physicalH1CarrierToL2AfterAcceptedCoordinate_sobolevSquareSummable x)

theorem physicalH1CarrierEnergyCandidate_boundAfterAcceptedCoordinate
    (x : SobolevHilbert 1) :
    physicalH1CarrierEnergyCandidateAfterAcceptedCoordinate x ≤
      ((2 * Real.pi) * ‖x‖) ^ 2 +
        (‖x‖ * ‖reciprocalBracketL2‖) ^ 4 := by
  have h := physicalH1EnergyCandidate_bound
    (physicalH1CarrierToL2AfterAcceptedCoordinate x)
    (physicalH1CarrierToL2AfterAcceptedCoordinate_sobolevSquareSummable x)
  simpa only [physicalH1CarrierEnergyCandidateAfterAcceptedCoordinate,
    physicalH1CarrierSobolevL2_norm_afterAcceptedCoordinate] using h

end NlsGge.Pilot
