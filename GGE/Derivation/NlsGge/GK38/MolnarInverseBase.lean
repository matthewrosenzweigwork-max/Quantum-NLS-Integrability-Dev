import NlsGge.GK38.MolnarCubicTrace
import NlsGge.GK38.MolnarJensen
import NlsGge.GK38.MolnarSourceWeights

set_option autoImplicit false

open MeasureTheory

namespace NlsGge.GK38.MolnarBounds38

open NlsGge.Pilot NlsGge.Schur NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.HierarchyRiccati.Core

theorem sourcePairFourier_le_mass_quad38 (y : SobolevHilbert ((1 : ℕ) : ℝ)) :
    Summable (fun n : ℤ => (1 + |2 * Real.pi * (n : ℝ)|) ^ 2 *
      ‖physicalFourier (sobolevToL2_38 1 y) n‖ ^ 2) ∧
    (2 / 3 : ℝ) * (∑' n : ℤ, (1 + |2 * Real.pi * (n : ℝ)|) ^ 2 *
      ‖physicalFourier (sobolevToL2_38 1 y) n‖ ^ 2) ≤
      ‖sobolevToL2_38 1 y‖ ^ 2 + chargeQuad38 ((1 : ℕ) : ℝ) 1 y := by
  let u := sobolevToL2_38 1 y
  have hu : SobolevSquareSummable 1 (physicalFourier u) := by
    simpa only [Nat.cast_one] using sobolevToL2_38_sobolev 1 y
  have hsF := sourcePairFourier_summable38 u hu
  have hsW := weightedHilbert_hasSum (sobolevModeWeight ((1 : ℕ) : ℝ))
    (show WeightedHilbert (sobolevModeWeight ((1 : ℕ) : ℝ)) from y)
  have hsQ : Summable (fun n : ℤ =>
      (2 * Real.pi * (n : ℝ)) ^ 2 * ‖physicalFourier u n‖ ^ 2) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      (hsW.summable.mul_left (1 + (2 * Real.pi) ^ 2))
    dsimp [u]
    rw [sobolevToL2_38_fourier]
    have hw := chargeQuad_weight_le38 1 1 le_rfl n
    norm_num only [Nat.mul_one] at hw
    have hlow : (2 * Real.pi * (n : ℝ)) ^ 2 ≤
        (1 + (2 * Real.pi) ^ 2) * sobolevModeWeight ((1 : ℕ) : ℝ) n := by
      simp only [Nat.cast_one]
      linarith
    have h := mul_le_mul_of_nonneg_right hlow
      (sq_nonneg ‖(show WeightedHilbert (sobolevModeWeight ((1 : ℕ) : ℝ)) from y) n‖)
    simpa only [mul_assoc] using h
  have hq : (∑' n : ℤ, (2 * Real.pi * (n : ℝ)) ^ 2 * ‖physicalFourier u n‖ ^ 2) =
      chargeQuad38 ((1 : ℕ) : ℝ) 1 y := by
    unfold chargeQuad38
    apply tsum_congr
    intro n
    dsimp [u]
    rw [sobolevToL2_38_fourier]
  have hQ : HasSum (fun n : ℤ => (2 * Real.pi * (n : ℝ)) ^ 2 * ‖physicalFourier u n‖ ^ 2)
      (chargeQuad38 ((1 : ℕ) : ℝ) 1 y) := by rw [← hq]; exact hsQ.hasSum
  have hsum := (hasSum_physicalFourier_sq u).add hQ
  have hpoint : ∀ n : ℤ,
      (2 / 3 : ℝ) * ((1 + |2 * Real.pi * (n : ℝ)|) ^ 2 * ‖physicalFourier u n‖ ^ 2) ≤
        ‖physicalFourier u n‖ ^ 2 +
          (2 * Real.pi * (n : ℝ)) ^ 2 * ‖physicalFourier u n‖ ^ 2 := by
    intro n
    have h := mul_le_mul_of_nonneg_right (sourcePairWeight_le_derivative38 n)
      (sq_nonneg ‖physicalFourier u n‖)
    nlinarith [h]
  have h := Summable.tsum_le_tsum hpoint (hsF.mul_left (2 / 3 : ℝ)) hsum.summable
  rw [tsum_mul_left, hsum.tsum_eq] at h
  exact ⟨hsF, h⟩

theorem mass_plus_quadratic_action_le_weighted38 (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    Summable (fun n : ℤ => (2 * Real.pi * (n : ℝ)) ^ 2 * actualGapActionAllE02_38 u n) ∧
    Summable (fun n : ℤ => (1 + |2 * Real.pi * (n : ℝ)|) ^ 2 * actualGapActionAllE02_38 u n) ∧
    ‖u‖ ^ 2 + (∑' n : ℤ, (2 * Real.pi * (n : ℝ)) ^ 2 * actualGapActionAllE02_38 u n) ≤
      ∑' n : ℤ, (1 + |2 * Real.pi * (n : ℝ)|) ^ 2 * actualGapActionAllE02_38 u n := by
  have hs := molnarActionSummability38 1 le_rfl u (by simpa only [Nat.cast_one] using hu)
  have hweight : ∀ n : ℤ,
      1 + (2 * Real.pi * (n : ℝ)) ^ 2 ≤ (1 + |2 * Real.pi * (n : ℝ)|) ^ 2 := by
    intro n
    nlinarith [abs_nonneg (2 * Real.pi * (n : ℝ)), sq_abs (2 * Real.pi * (n : ℝ))]
  have hsQ : Summable (fun n : ℤ => (2 * Real.pi * (n : ℝ)) ^ 2 * actualGapActionAllE02_38 u n) := by
    refine Summable.of_nonneg_of_le (fun n => by
      exact mul_nonneg (sq_nonneg _) (actualGapAction_nonneg_F04_38 u n)) (fun n => ?_) hs
    have hn : (2 * Real.pi * (n : ℝ)) ^ 2 ≤ (1 + |2 * Real.pi * (n : ℝ)|) ^ 2 := by
      linarith [hweight n]
    exact mul_le_mul_of_nonneg_right hn (actualGapAction_nonneg_F04_38 u n)
  have hsum := (actualGapAction_hasSum_E02_38 u hu).add hsQ.hasSum
  have hpoint : ∀ n : ℤ,
      actualGapActionAllE02_38 u n + (2 * Real.pi * (n : ℝ)) ^ 2 * actualGapActionAllE02_38 u n ≤
        (1 + |2 * Real.pi * (n : ℝ)|) ^ 2 * actualGapActionAllE02_38 u n := by
    intro n
    have h := mul_le_mul_of_nonneg_right (hweight n) (actualGapAction_nonneg_F04_38 u n)
    simpa only [add_mul, one_mul] using h
  have h := Summable.tsum_le_tsum hpoint hsum.summable hs
  rw [hsum.tsum_eq] at h
  exact ⟨hsQ, hs, h⟩

theorem molnar_inverse_base_pair_carrier38 (y : SobolevHilbert ((1 : ℕ) : ℝ)) :
    Summable (fun n : ℤ => (1 + |2 * Real.pi * (n : ℝ)|) ^ 2 *
      ‖physicalFourier (sobolevToL2_38 1 y) n‖ ^ 2) ∧
    Summable (fun n : ℤ => (1 + |2 * Real.pi * (n : ℝ)|) ^ 2 *
      actualGapActionAllE02_38 (sobolevToL2_38 1 y) n) ∧
    (2 / 3 : ℝ) * (∑' n : ℤ, (1 + |2 * Real.pi * (n : ℝ)|) ^ 2 *
      ‖physicalFourier (sobolevToL2_38 1 y) n‖ ^ 2) ≤
      (∑' n : ℤ, (1 + |2 * Real.pi * (n : ℝ)|) ^ 2 *
        actualGapActionAllE02_38 (sobolevToL2_38 1 y) n) + (‖sobolevToL2_38 1 y‖ ^ 2) ^ 2 := by
  have hF := sourcePairFourier_le_mass_quad38 y
  have hA := mass_plus_quadratic_action_le_weighted38 _
    (by simpa only [Nat.cast_one] using sobolevToL2_38_sobolev 1 y)
  have hJ := chargeTwo_ge_quad_add_mass_sq38 y
  rw [massChargeAllSobolev38 1 le_rfl y] at hJ
  have htrace := molnar_cubic_trace38 y
  have hcubenonneg : 0 ≤ ∫ t : ℝ, actualGapHeightE02_38 (sobolevToL2_38 1 y) t ^ 3 :=
    integral_nonneg fun t => pow_nonneg (actualGapHeightE02_38_nonneg _ t) 3
  have hlast : 0 ≤ (8 / (3 * Real.pi)) *
      ∫ t : ℝ, actualGapHeightE02_38 (sobolevToL2_38 1 y) t ^ 3 :=
    mul_nonneg (by positivity) hcubenonneg
  refine ⟨hF.1, hA.2.1, ?_⟩
  linarith [hF.2, hA.2.2, htrace.2.2]

/-- The exact source Lemma 15 pair-norm inverse base for EVERY physical H1 potential. -/
theorem molnar_inverse_base_pair38 (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    Summable (fun n : ℤ => (1 + |2 * Real.pi * (n : ℝ)|) ^ 2 * ‖physicalFourier u n‖ ^ 2) ∧
    Summable (fun n : ℤ => (1 + |2 * Real.pi * (n : ℝ)|) ^ 2 * actualGapActionAllE02_38 u n) ∧
    (2 / 3 : ℝ) * (∑' n : ℤ, (1 + |2 * Real.pi * (n : ℝ)|) ^ 2 * ‖physicalFourier u n‖ ^ 2) ≤
      (∑' n : ℤ, (1 + |2 * Real.pi * (n : ℝ)|) ^ 2 * actualGapActionAllE02_38 u n) +
        (‖u‖ ^ 2) ^ 2 := by
  obtain ⟨y, hy⟩ := exists_actual_H1_carrier38 u hu
  rw [← hy]
  exact molnar_inverse_base_pair_carrier38 y

end NlsGge.GK38.MolnarBounds38
