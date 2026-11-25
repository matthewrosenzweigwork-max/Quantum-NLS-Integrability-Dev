import NlsGge.GK38.PairAsymptoticsCharacteristic

/-! # S1: quarter-radius lattice geometry for GK Lemma 6.3 -/

set_option autoImplicit false

open Filter Topology Set Metric

namespace NlsGge.GK38

noncomputable section

def countingCenter38 (n : ℤ) : ℂ := (n : ℂ) * (Real.pi : ℂ)

def countingRadius38 (N : ℕ) : ℝ := (N : ℝ) * Real.pi + Real.pi / 4

theorem countingRadius_pos38 (N : ℕ) : 0 < countingRadius38 N := by
  unfold countingRadius38
  positivity

theorem norm_countingCenter38 (n : ℤ) :
    ‖countingCenter38 n‖ = |(n : ℝ)| * Real.pi := by
  simp [countingCenter38, Complex.norm_intCast]

theorem countingCenter_sub38 (n m : ℤ) :
    countingCenter38 n - countingCenter38 m = countingCenter38 (n - m) := by
  simp [countingCenter38, sub_mul]

theorem countingCenter_separated38 {n m : ℤ} (h : n ≠ m) :
    Real.pi ≤ ‖countingCenter38 n - countingCenter38 m‖ := by
  rw [countingCenter_sub38, norm_countingCenter38]
  have hi : (1 : ℤ) ≤ |n - m| := by
    have hp : 0 < |n - m| := abs_pos.mpr (sub_ne_zero.mpr h)
    omega
  have hr : (1 : ℝ) ≤ |((n - m : ℤ) : ℝ)| := by exact_mod_cast hi
  nlinarith [Real.pi_pos]

theorem countingCenter_low_norm38 {N : ℕ} {n : ℤ} (h : |n| ≤ (N : ℤ)) :
    ‖countingCenter38 n‖ ≤ (N : ℝ) * Real.pi := by
  rw [norm_countingCenter38]
  have hr : |(n : ℝ)| ≤ (N : ℝ) := by exact_mod_cast h
  exact mul_le_mul_of_nonneg_right hr Real.pi_pos.le

theorem countingCenter_far_norm38 {N : ℕ} {n : ℤ} (h : (N : ℤ) < |n|) :
    ((N : ℝ) + 1) * Real.pi ≤ ‖countingCenter38 n‖ := by
  rw [norm_countingCenter38]
  have hi : (N : ℤ) + 1 ≤ |n| := by omega
  have hr : (N : ℝ) + 1 ≤ |(n : ℝ)| := by exact_mod_cast hi
  exact mul_le_mul_of_nonneg_right hr Real.pi_pos.le

/-- The central circle avoids every open quarter-radius lattice disc. -/
theorem counting_central_sphere_separated38 (N : ℕ) {z : ℂ}
    (hz : z ∈ sphere (0 : ℂ) (countingRadius38 N)) (n : ℤ) :
    Real.pi / 4 ≤ ‖z - countingCenter38 n‖ := by
  have hz' : ‖z‖ = countingRadius38 N := by
    simpa only [mem_sphere, dist_zero_right] using hz
  by_cases hn : |n| ≤ (N : ℤ)
  · have hc := countingCenter_low_norm38 hn
    have ht := norm_sub_norm_le z (countingCenter38 n)
    rw [hz'] at ht
    unfold countingRadius38 at ht
    linarith
  · have hc := countingCenter_far_norm38 (lt_of_not_ge hn)
    have ht := norm_sub_norm_le (countingCenter38 n) z
    rw [norm_sub_rev, hz'] at ht
    unfold countingRadius38 at ht
    linarith [Real.pi_pos]

/-- Every point of a lattice-disc boundary avoids every other open lattice disc. -/
theorem counting_small_sphere_separated38 (n : ℤ) {z : ℂ}
    (hz : z ∈ sphere (countingCenter38 n) (Real.pi / 4)) (m : ℤ) :
    Real.pi / 4 ≤ ‖z - countingCenter38 m‖ := by
  have hz' : ‖z - countingCenter38 n‖ = Real.pi / 4 := by
    simpa only [mem_sphere, dist_eq_norm] using hz
  by_cases hmn : m = n
  · rw [hmn, hz']
  · have hc := countingCenter_separated38 hmn
    have ht : ‖countingCenter38 m - countingCenter38 n‖ ≤
        ‖z - countingCenter38 m‖ + ‖z - countingCenter38 n‖ := by
      calc
        _ = ‖(countingCenter38 m - z) + (z - countingCenter38 n)‖ := by congr 1; ring
        _ ≤ ‖countingCenter38 m - z‖ + ‖z - countingCenter38 n‖ := norm_add_le _ _
        _ = _ := by rw [norm_sub_rev]
    rw [hz'] at ht
    linarith [Real.pi_pos]

theorem counting_far_sphere_norm38 {N : ℕ} {n : ℤ} (hn : (N : ℤ) < |n|)
    {z : ℂ} (hz : z ∈ sphere (countingCenter38 n) (Real.pi / 4)) :
    countingRadius38 N ≤ ‖z‖ := by
  have hz' : ‖countingCenter38 n - z‖ = Real.pi / 4 := by
    simpa only [mem_sphere, dist_eq_norm, norm_sub_rev] using hz
  have hc := countingCenter_far_norm38 hn
  have ht := norm_sub_norm_le (countingCenter38 n) z
  rw [hz'] at ht
  unfold countingRadius38
  linarith [Real.pi_pos]

/-- Outside the central disc, the low-index lattice discs are automatically avoided. -/
theorem counting_outside_separated38 (N : ℕ) {z : ℂ}
    (hz : countingRadius38 N ≤ ‖z‖)
    (hfar : ∀ n : ℤ, (N : ℤ) < |n| → Real.pi / 4 ≤ ‖z - countingCenter38 n‖)
    (n : ℤ) : Real.pi / 4 ≤ ‖z - countingCenter38 n‖ := by
  by_cases hn : (N : ℤ) < |n|
  · exact hfar n hn
  · have hc := countingCenter_low_norm38 (le_of_not_gt hn)
    have ht := norm_sub_norm_le z (countingCenter38 n)
    unfold countingRadius38 at hz
    linarith

theorem counting_sin_ne_zero38 {z : ℂ}
    (hsep : ∀ n : ℤ, Real.pi / 4 ≤ ‖z - countingCenter38 n‖) :
    Complex.sin z ≠ 0 := by
  intro hz
  obtain ⟨n, hn⟩ := Complex.sin_eq_zero_iff.mp hz
  have h := hsep n
  rw [hn, countingCenter38, sub_self, norm_zero] at h
  linarith [Real.pi_pos]

end
end NlsGge.GK38
