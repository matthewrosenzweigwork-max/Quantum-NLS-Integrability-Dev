import NlsGge.Hierarchy.RiccatiSmoothClassicalDerivativePhysicalL2AgreementRecovery30Fifth
import NlsGge.Sobolev.SmoothFourier
import NlsGge.Sobolev.PeriodicBridge
import NlsGge.Sobolev.SourceEmbeddings
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace NlsGge.HierarchyRiccati.Core

open NlsGge.Pilot
open MeasureTheory
open scoped ContDiff

local instance : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure
  infer_instance

private theorem riccatiBracket_power_le_maxRecovery30 (m : ℕ) (n : ℤ) :
    japaneseBracket n ^ (2 * m) ≤
      (2 : ℝ) ^ (2 * m) * (1 + |(n : ℝ)| ^ (2 * (m + 1))) := by
  let a : ℝ := |(n : ℝ)|
  let b : ℝ := japaneseBracket n
  have ha : 0 ≤ a := abs_nonneg _
  have hb : 0 < b := japaneseBracket_pos n
  have hbSq : b ^ 2 = 1 + a ^ 2 := by
    dsimp [b, a]
    rw [japaneseBracket_sq, sq_abs]
  have hbUpper : b ≤ 1 + a := by
    nlinarith [sq_nonneg (b - (1 + a))]
  have hsumMax : 1 + a ≤ 2 * max 1 a := by
    by_cases h : a ≤ 1
    · rw [max_eq_left h]
      nlinarith
    · rw [max_eq_right (le_of_not_ge h)]
      nlinarith
  have hmaxPower : (max 1 a) ^ (2 * m) ≤ 1 + a ^ (2 * (m + 1)) := by
    by_cases h : a ≤ 1
    · rw [max_eq_left h]
      simp only [one_pow]
      exact le_add_of_nonneg_right (by positivity)
    · have haOne : 1 ≤ a := le_of_not_ge h
      rw [max_eq_right haOne]
      have hexp : 2 * m ≤ 2 * (m + 1) := by omega
      calc
        a ^ (2 * m) ≤ a ^ (2 * (m + 1)) :=
          pow_le_pow_right₀ haOne hexp
        _ ≤ 1 + a ^ (2 * (m + 1)) := by linarith
  calc
    b ^ (2 * m) ≤ (1 + a) ^ (2 * m) :=
      pow_le_pow_left₀ hb.le hbUpper _
    _ ≤ (2 * max 1 a) ^ (2 * m) :=
      pow_le_pow_left₀ (by positivity) hsumMax _
    _ = (2 : ℝ) ^ (2 * m) * (max 1 a) ^ (2 * m) := by rw [mul_pow]
    _ ≤ (2 : ℝ) ^ (2 * m) * (1 + a ^ (2 * (m + 1))) :=
      mul_le_mul_of_nonneg_left hmaxPower (by positivity)

private theorem riccatiSmoothSobolevWeightedCoefficient_leRecovery30
    (m : ℕ) (n : ℤ) (c d : ℂ)
    (hd : d = fourierMultiplier n ^ (m + 1) * c) :
    sobolevModeWeight (m : ℝ) n * ‖c‖ ^ 2 ≤
      (2 : ℝ) ^ (2 * m) * ‖c‖ ^ 2 +
        ((2 : ℝ) ^ (2 * m) / ((2 * Real.pi) ^ (m + 1)) ^ 2) * ‖d‖ ^ 2 := by
  let a : ℝ := |(n : ℝ)|
  let b : ℝ := japaneseBracket n
  let A : ℝ := (2 : ℝ) ^ (2 * m)
  let H : ℝ := (2 * Real.pi) ^ (m + 1)
  have ha : 0 ≤ a := abs_nonneg _
  have hweight : sobolevModeWeight (m : ℝ) n = b ^ (2 * m) := by
    dsimp [sobolevModeWeight, b]
    rw [show 2 * (m : ℝ) = ((2 * m : ℕ) : ℝ) by push_cast; ring]
    exact Real.rpow_natCast _ _
  have hbracket := riccatiBracket_power_le_maxRecovery30 m n
  have hdnorm : ‖d‖ ^ 2 = (H * a ^ (m + 1) * ‖c‖) ^ 2 := by
    calc
      ‖d‖ ^ 2 = (‖fourierMultiplier n‖ ^ (m + 1) * ‖c‖) ^ 2 := by
        rw [hd]
        simp
      _ = (H * a ^ (m + 1) * ‖c‖) ^ 2 := by
        rw [norm_fourierMultiplier]
        dsimp [H, a]
        simp only [mul_pow]
  have hcancel : (A / H ^ 2) * ‖d‖ ^ 2 = A * a ^ (2 * (m + 1)) * ‖c‖ ^ 2 := by
    rw [hdnorm]
    have hpow : (a ^ (m + 1)) ^ 2 = a ^ (2 * (m + 1)) := by
      calc
        (a ^ (m + 1)) ^ 2 = a ^ ((m + 1) * 2) := by rw [pow_mul]
        _ = a ^ (2 * (m + 1)) := by rw [Nat.mul_comm (m + 1) 2]
    have hH : H ≠ 0 := by
      dsimp [H]
      positivity
    dsimp [A]
    simp only [mul_pow, hpow]
    field_simp [hH]
  rw [hweight]
  calc
    b ^ (2 * m) * ‖c‖ ^ 2 ≤
        ((2 : ℝ) ^ (2 * m) * (1 + a ^ (2 * (m + 1)))) * ‖c‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hbracket (sq_nonneg _)
    _ = A * ‖c‖ ^ 2 + A * a ^ (2 * (m + 1)) * ‖c‖ ^ 2 := by
      dsimp [A]
      ring
    _ = A * ‖c‖ ^ 2 + (A / H ^ 2) * ‖d‖ ^ 2 := by
      rw [← hcancel]
    _ = (2 : ℝ) ^ (2 * m) * ‖c‖ ^ 2 +
        ((2 : ℝ) ^ (2 * m) / ((2 * Real.pi) ^ (m + 1)) ^ 2) * ‖d‖ ^ 2 := by
      rfl

/-- Every smooth period-one input has an actual source Sobolev vector at each
natural order. Its coefficients are exactly the physical Fourier coefficients
of the continuous period-one representative. The zero Fourier mode is included
in the Parseval-controlled base term; no division by the derivative multiplier
is used. -/
theorem riccatiSmoothPeriodic_hasSobolevCarrierWithExactFourierCoefficientsRecovery30
    (m : ℕ) (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
    (hper : Function.Periodic u 1) :
    ∃ x : SobolevHilbert (m : ℝ),
      ∀ n : ℤ,
        (show WeightedHilbert (sobolevModeWeight (m : ℝ)) from x) n =
          physicalFourier
            (ContinuousMap.toLp 2 spatialMeasure ℂ
              (riccatiSmoothPeriodicLiftContinuousMapRecovery30First
                u hu.continuous hper)) n := by
  let U : PhysicalL2 :=
    ContinuousMap.toLp 2 spatialMeasure ℂ
      (riccatiSmoothPeriodicLiftContinuousMapRecovery30First u hu.continuous hper)
  let dFun : ℝ → ℂ := iteratedDeriv (m + 1) u
  have hD : ContDiff ℝ ∞ dFun := by
    dsimp [dFun]
    rw [iteratedDeriv_eq_iterate]
    exact ContDiff.iterate_deriv (m + 1) hu
  have hDper : Function.Periodic dFun 1 := by
    dsimp [dFun]
    exact NlsGge.HierarchyRiccati.periodic_iteratedDeriv_of_contDiff
      u hu hper (m + 1)
  let V : PhysicalL2 :=
    ContinuousMap.toLp 2 spatialMeasure ℂ
      (riccatiSmoothPeriodicLiftContinuousMapRecovery30First dFun hD.continuous hDper)
  let c : ℤ → ℂ := fun n => physicalFourier U n
  let d : ℤ → ℂ := fun n => physicalFourier V n
  have hc : Summable (fun n : ℤ => ‖c n‖ ^ 2) := by
    dsimp [c]
    exact NlsGge.Pilot.summable_physicalFourier_sq U
  have hdSummable : Summable (fun n : ℤ => ‖d n‖ ^ 2) := by
    dsimp [d]
    exact NlsGge.Pilot.summable_physicalFourier_sq V
  have hcoeff (n : ℤ) : d n = fourierMultiplier n ^ (m + 1) * c n := by
    change physicalFourier
        (ContinuousMap.toLp 2 spatialMeasure ℂ
          (riccatiSmoothPeriodicLiftContinuousMapRecovery30First
            (iteratedDeriv (m + 1) u) hD.continuous hDper)) n =
      fourierMultiplier n ^ (m + 1) *
        physicalFourier
          (ContinuousMap.toLp 2 spatialMeasure ℂ
            (riccatiSmoothPeriodicLiftContinuousMapRecovery30First
              u hu.continuous hper)) n
    rw [physicalFourier_liftContinuousMap_eq_fourierCoeffOnRecovery30First
        (iteratedDeriv (m + 1) u) hD.continuous hDper n,
      physicalFourier_liftContinuousMap_eq_fourierCoeffOnRecovery30First
        u hu.continuous hper n]
    exact riccatiFourierCoeffOn_iteratedDeriv_periodOneRecovery29
      u hu hper (m + 1) n
  have hmajor : Summable (fun n : ℤ =>
      (2 : ℝ) ^ (2 * m) * ‖c n‖ ^ 2 +
        ((2 : ℝ) ^ (2 * m) / ((2 * Real.pi) ^ (m + 1)) ^ 2) * ‖d n‖ ^ 2) := by
    apply (hc.mul_left ((2 : ℝ) ^ (2 * m))).add
    exact hdSummable.mul_left
      ((2 : ℝ) ^ (2 * m) / ((2 * Real.pi) ^ (m + 1)) ^ 2)
  have hsob : SobolevSquareSummable (m : ℝ) c := by
    change Summable (fun n : ℤ =>
      Real.rpow (japaneseBracket n) (2 * (m : ℝ)) * ‖c n‖ ^ 2)
    apply Summable.of_nonneg_of_le
      (fun n => mul_nonneg (Real.rpow_nonneg (japaneseBracket_pos n).le _) (sq_nonneg _))
      (fun n => riccatiSmoothSobolevWeightedCoefficient_leRecovery30 m n (c n) (d n)
        (hcoeff n))
      hmajor
  have hw : ∀ n : ℤ, 0 ≤ sobolevModeWeight (m : ℝ) n :=
    fun n => (sobolevModeWeightPositive (m : ℝ)).out n |>.le
  let x : SobolevHilbert (m : ℝ) := by
    change WeightedHilbert (sobolevModeWeight (m : ℝ))
    exact ⟨c, (weightedCoordinates_mem_l2_iff
      (sobolevModeWeight (m : ℝ)) hw c).2 hsob⟩
  refine ⟨x, ?_⟩
  intro n
  change c n = _
  rfl

end NlsGge.HierarchyRiccati.Core

end
