import NlsGge.Schur.FreeResolventPotentialMatrixEntriesAfterInnerScalar
import NlsGge.Analysis.PhysicalNonresonantSeries

set_option autoImplicit false
noncomputable section
open scoped InnerProduct InnerProductSpace

namespace NlsGge.Schur
open NlsGge.Pilot NlsGge.Analysis

private theorem sectorIndex_ne_resonant_of_ne_zero (n r : ℤ) (hr : r ≠ 0) :
    sectorIndex n r ≠ resonantIndex n := by
  intro h
  have hzero : sectorIndex n 0 = resonantIndex n := by
    apply Subtype.ext
    change n + 2 * 0 = n
    ring
  have heq : sectorIndex n r = sectorIndex n 0 := h.trans hzero.symm
  exact hr (sectorIndex_injective n heq)

private theorem sectorIndex_resolvent_coeff_sq_bound (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralDisk n) (r : ℤ) (hr : r ≠ 0) :
    ‖freeResolventCoeff n z (sectorIndex n r)‖ ^ 2 ≤ inverseSquare r := by
  have hrne : sectorIndex n r ≠ resonantIndex n :=
    sectorIndex_ne_resonant_of_ne_zero n r hr
  have hraw := freeResolventCoeff_bound n z hz (sectorIndex n r) hrne
  have hden :
      |((sectorIndex n r).val : ℝ) - (n : ℝ)| = 2 * |(r : ℝ)| := by
    change |((n + 2 * r : ℤ) : ℝ) - (n : ℝ)| = 2 * |(r : ℝ)|
    push_cast
    rw [show (n : ℝ) + 2 * (r : ℝ) - (n : ℝ) = 2 * (r : ℝ) by ring,
      abs_mul]
    norm_num
  rw [hden] at hraw
  have hrpos : 0 < |(r : ℝ)| := abs_pos.mpr (by exact_mod_cast hr)
  have hdenle : |(r : ℝ)| ≤ 2 * |(r : ℝ)| := by nlinarith
  have hcoeff : ‖freeResolventCoeff n z (sectorIndex n r)‖ ≤
      1 / |(r : ℝ)| :=
    hraw.trans (one_div_le_one_div_of_le hrpos hdenle)
  have hsq : ‖freeResolventCoeff n z (sectorIndex n r)‖ ^ 2 ≤
      (1 / |(r : ℝ)|) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hcoeff
  calc
    ‖freeResolventCoeff n z (sectorIndex n r)‖ ^ 2 ≤
        (1 / |(r : ℝ)|) ^ 2 := hsq
    _ = inverseSquare r := by
      simp [inverseSquare, div_pow, sq_abs]

private theorem sector_index_pair_sum_half (n r s : ℤ) :
    ((sectorIndex n r).val + (sectorIndex n s).val) / 2 = n + r + s := by
  change (n + 2 * r + (n + 2 * s)) / 2 = n + r + s
  omega

private theorem sector_index_pair_neg_sum_half (n r s : ℤ) :
    -((sectorIndex n r).val + (sectorIndex n s).val) / 2 = -(n + r + s) := by
  have hdvd : 2 ∣ (sectorIndex n r).val + (sectorIndex n s).val := by
    change 2 ∣ n + 2 * r + (n + 2 * s)
    omega
  rw [Int.neg_ediv_of_dvd hdvd, sector_index_pair_sum_half]

/-- The actual upper DVD matrix coefficient is dominated by the source
nonresonant double-series summand. -/
theorem freeResolventPotentialFreeResolvent_upper_entry_sq_bound
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n) (r s : ℤ)
    (hr : r ≠ 0) (hs : s ≠ 0) :
    ‖inner ℂ (parityPairVector n (true, sectorIndex n r))
      (freeResolventPotentialFreeResolvent u₁ u₂ hu₁ hu₂ n z hz
        (parityPairVector n (false, sectorIndex n s)))‖ ^ 2 ≤
      ‖physicalFourier u₁ (n + r + s)‖ ^ 2 *
        inverseSquare r * inverseSquare s := by
  rw [freeResolventPotentialFreeResolvent_upper_entry]
  rw [sector_index_pair_sum_half]
  have hleft := sectorIndex_resolvent_coeff_sq_bound n z hz r hr
  have hright := sectorIndex_resolvent_coeff_sq_bound n z hz s hs
  rw [norm_mul, norm_mul]
  calc
    (‖freeResolventCoeff n z (sectorIndex n r)‖ *
        ‖physicalFourier u₁ (n + r + s)‖ *
        ‖freeResolventCoeff n z (sectorIndex n s)‖) ^ 2 =
      ‖freeResolventCoeff n z (sectorIndex n r)‖ ^ 2 *
        ‖physicalFourier u₁ (n + r + s)‖ ^ 2 *
          ‖freeResolventCoeff n z (sectorIndex n s)‖ ^ 2 := by ring
    _ ≤ inverseSquare r * ‖physicalFourier u₁ (n + r + s)‖ ^ 2 *
          inverseSquare s := by
      calc
        _ ≤ inverseSquare r * ‖physicalFourier u₁ (n + r + s)‖ ^ 2 *
              ‖freeResolventCoeff n z (sectorIndex n s)‖ ^ 2 := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hleft (sq_nonneg _)) (sq_nonneg _)
        _ ≤ inverseSquare r * ‖physicalFourier u₁ (n + r + s)‖ ^ 2 *
              inverseSquare s :=
            mul_le_mul_of_nonneg_left hright
              (mul_nonneg (inverseSquare_nonneg _) (sq_nonneg _))
    _ = ‖physicalFourier u₁ (n + r + s)‖ ^ 2 *
          inverseSquare r * inverseSquare s := by ring

/-- The independent lower DVD matrix coefficient has the reflected source
double-series summand, with no conjugacy relation to the upper field. -/
theorem freeResolventPotentialFreeResolvent_lower_entry_sq_bound
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n) (r s : ℤ)
    (hr : r ≠ 0) (hs : s ≠ 0) :
    ‖inner ℂ (parityPairVector n (false, sectorIndex n r))
      (freeResolventPotentialFreeResolvent u₁ u₂ hu₁ hu₂ n z hz
        (parityPairVector n (true, sectorIndex n s)))‖ ^ 2 ≤
      ‖physicalFourier u₂ (-(n + r + s))‖ ^ 2 *
        inverseSquare r * inverseSquare s := by
  rw [freeResolventPotentialFreeResolvent_lower_entry]
  rw [sector_index_pair_neg_sum_half]
  have hleft := sectorIndex_resolvent_coeff_sq_bound n z hz r hr
  have hright := sectorIndex_resolvent_coeff_sq_bound n z hz s hs
  rw [norm_mul, norm_mul]
  calc
    (‖freeResolventCoeff n z (sectorIndex n r)‖ *
        ‖physicalFourier u₂ (-(n + r + s))‖ *
        ‖freeResolventCoeff n z (sectorIndex n s)‖) ^ 2 =
      ‖freeResolventCoeff n z (sectorIndex n r)‖ ^ 2 *
        ‖physicalFourier u₂ (-(n + r + s))‖ ^ 2 *
          ‖freeResolventCoeff n z (sectorIndex n s)‖ ^ 2 := by ring
    _ ≤ inverseSquare r * ‖physicalFourier u₂ (-(n + r + s))‖ ^ 2 *
          inverseSquare s := by
      calc
        _ ≤ inverseSquare r * ‖physicalFourier u₂ (-(n + r + s))‖ ^ 2 *
              ‖freeResolventCoeff n z (sectorIndex n s)‖ ^ 2 := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hleft (sq_nonneg _)) (sq_nonneg _)
        _ ≤ inverseSquare r * ‖physicalFourier u₂ (-(n + r + s))‖ ^ 2 *
              inverseSquare s :=
            mul_le_mul_of_nonneg_left hright
              (mul_nonneg (inverseSquare_nonneg _) (sq_nonneg _))
    _ = ‖physicalFourier u₂ (-(n + r + s))‖ ^ 2 *
          inverseSquare r * inverseSquare s := by ring

end NlsGge.Schur
