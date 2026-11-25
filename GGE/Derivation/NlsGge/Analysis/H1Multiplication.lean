import NlsGge.Analysis.H1Fourier
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Analysis.Normed.Operator.Mul

/-! Actual varying physical H1 multiplication on the period-one complex L2 space.
The source parity/paired potential and resolvent/HS realizations are separate. -/
set_option autoImplicit false
noncomputable section

namespace NlsGge.Analysis
open MeasureTheory
open NlsGge.Pilot
open scoped ENNReal

local instance : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure
  infer_instance

/-- The genuine essentially bounded class of the proved continuous H1 representative. -/
def physicalH1Bounded (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) : Lp ℂ ∞ spatialMeasure :=
  ContinuousMap.toLp ∞ spatialMeasure ℂ (physicalH1Continuous u hu)

theorem physicalH1Bounded_coe_ae (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    (physicalH1Bounded u hu : PhysicalCircle → ℂ) =ᵐ[spatialMeasure] u := by
  have htop := ContinuousMap.coeFn_toLp (p := ∞) (𝕜 := ℂ) spatialMeasure (physicalH1Continuous u hu)
  have htwo := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) spatialMeasure (physicalH1Continuous u hu)
  rw [physicalH1Continuous_toLp] at htwo
  exact htop.trans htwo.symm

theorem physicalH1Bounded_norm_le (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    ‖physicalH1Bounded u hu‖ ≤ ‖physicalH1Continuous u hu‖ := by
  have hp : ∀ᵐ x ∂spatialMeasure,
      ‖physicalH1Bounded u hu x‖ ≤ ‖physicalH1Continuous u hu‖ := by
    filter_upwards [ContinuousMap.coeFn_toLp (p := ∞) (𝕜 := ℂ)
      spatialMeasure (physicalH1Continuous u hu)] with x hx
    change physicalH1Bounded u hu x = physicalH1Continuous u hu x at hx
    rw [hx]
    exact (physicalH1Continuous u hu).norm_coe_le_norm x
  have h := Lp.norm_le_of_ae_bound (f := physicalH1Bounded u hu)
    (norm_nonneg (physicalH1Continuous u hu)) hp
  simpa only [ENNReal.toReal_top, inv_zero, Real.rpow_zero, one_mul] using h

/-- Actual multiplication by the varying H1 field, constructed by Holder infinity,2,2. -/
def physicalH1Multiplier (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) : PhysicalL2 →L[ℂ] PhysicalL2 :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL spatialMeasure ∞ 2 2 (physicalH1Bounded u hu)

theorem physicalH1Multiplier_coe_ae (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) (f : PhysicalL2) :
    (physicalH1Multiplier u hu f : PhysicalCircle → ℂ) =ᵐ[spatialMeasure]
      fun x => u x * f x := by
  have hm := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder
    (r := (2 : ℝ≥0∞)) (physicalH1Bounded u hu) f
  change (physicalH1Multiplier u hu f : PhysicalCircle → ℂ) =ᵐ[spatialMeasure]
    (fun x => physicalH1Bounded u hu x * f x) at hm
  filter_upwards [hm, physicalH1Bounded_coe_ae u hu] with x hx hu
  rw [hx, hu]

theorem physicalH1Multiplier_norm_le_bounded (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    ‖physicalH1Multiplier u hu‖ ≤ ‖physicalH1Bounded u hu‖ := by
  have hop : ‖(ContinuousLinearMap.mul ℂ ℂ).holderL spatialMeasure ∞ 2 2‖ ≤ 1 :=
    (ContinuousLinearMap.norm_holderL_le (ContinuousLinearMap.mul ℂ ℂ)).trans
      (ContinuousLinearMap.opNorm_mul_le ℂ ℂ)
  calc
    _ ≤ ‖(ContinuousLinearMap.mul ℂ ℂ).holderL spatialMeasure ∞ 2 2‖ *
        ‖physicalH1Bounded u hu‖ :=
      ((ContinuousLinearMap.mul ℂ ℂ).holderL spatialMeasure ∞ 2 2).le_opNorm _
    _ ≤ 1 * ‖physicalH1Bounded u hu‖ := mul_le_mul_of_nonneg_right hop (norm_nonneg _)
    _ = _ := one_mul _

theorem physicalH1Multiplier_norm_le (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    ‖physicalH1Multiplier u hu‖ ≤ ‖physicalSobolevL2 1 u hu‖ * ‖reciprocalBracketL2‖ :=
  (physicalH1Multiplier_norm_le_bounded u hu).trans
    ((physicalH1Bounded_norm_le u hu).trans (physicalH1Continuous_norm_bound u hu))

/-- Fixed positive constant, chosen before the physical field and the source ball radius. -/
def physicalH1MultiplierConstant : ℝ := 1 + ‖reciprocalBracketL2‖

theorem physicalH1MultiplierConstant_pos : 0 < physicalH1MultiplierConstant := by
  unfold physicalH1MultiplierConstant
  positivity

theorem physicalH1Multiplier_uniform_bound (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    ‖physicalH1Multiplier u hu‖ ≤ physicalH1MultiplierConstant * ‖physicalSobolevL2 1 u hu‖ := by
  apply (physicalH1Multiplier_norm_le u hu).trans
  unfold physicalH1MultiplierConstant
  nlinarith [norm_nonneg (physicalSobolevL2 1 u hu)]

theorem physicalH1Multiplier_ball_bound (R : ℝ) (_hR : 1 ≤ R) (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u))
    (hball : ‖physicalSobolevL2 1 u hu‖ ≤ R) :
    ‖physicalH1Multiplier u hu‖ ≤ physicalH1MultiplierConstant * R :=
  (physicalH1Multiplier_uniform_bound u hu).trans
    (mul_le_mul_of_nonneg_left hball physicalH1MultiplierConstant_pos.le)

theorem exists_physicalH1_multiplier_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : PhysicalL2)
      (hu : SobolevSquareSummable 1 (physicalFourier u)),
      ‖physicalH1Multiplier u hu‖ ≤ C * ‖physicalSobolevL2 1 u hu‖ :=
  ⟨physicalH1MultiplierConstant, physicalH1MultiplierConstant_pos,
    physicalH1Multiplier_uniform_bound⟩

end NlsGge.Analysis
