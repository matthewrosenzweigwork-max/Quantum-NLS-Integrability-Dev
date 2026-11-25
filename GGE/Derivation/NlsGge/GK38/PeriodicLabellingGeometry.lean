import NlsGge.GK38.PeriodicLabellingDefs

/-! # S2: real-part separation of the certified spectral blocks -/
set_option autoImplicit false
open Filter Topology Set Metric
namespace NlsGge.GK38
noncomputable section

theorem countingCenter_re38 (n : ℤ) : (countingCenter38 n).re = (n : ℝ) * Real.pi := by
  simp [countingCenter38]

theorem counting_small_re_bounds38 {n : ℤ} {z : ℂ}
    (hz : z ∈ ball (countingCenter38 n) (Real.pi / 4)) :
    (n : ℝ) * Real.pi - Real.pi / 4 < z.re ∧
      z.re < (n : ℝ) * Real.pi + Real.pi / 4 := by
  have h := (Complex.abs_re_le_norm (z - countingCenter38 n)).trans_lt
    (mem_ball_iff_norm.mp hz)
  rw [Complex.sub_re, countingCenter_re38, abs_lt] at h
  constructor <;> linarith

theorem counting_central_re_bounds38 {N : ℕ} {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) (countingRadius38 N)) :
    -countingRadius38 N < z.re ∧ z.re < countingRadius38 N := by
  have h := (Complex.abs_re_le_norm z).trans_lt (by
    simpa only [mem_ball, dist_zero_right] using hz)
  exact abs_lt.mp h

theorem counting_small_blocks_re_lt38 {n m : ℤ} (hnm : n < m) {z w : ℂ}
    (hz : z ∈ ball (countingCenter38 n) (Real.pi / 4))
    (hw : w ∈ ball (countingCenter38 m) (Real.pi / 4)) : z.re < w.re := by
  obtain ⟨_, hz'⟩ := counting_small_re_bounds38 hz
  obtain ⟨hw', _⟩ := counting_small_re_bounds38 hw
  have hn : (n : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast (show n + 1 ≤ m by omega)
  nlinarith [Real.pi_pos]

theorem counting_central_small_re_lt38 {N : ℕ} {n : ℤ} (hn : (N : ℤ) < n) {z w : ℂ}
    (hz : z ∈ ball (0 : ℂ) (countingRadius38 N))
    (hw : w ∈ ball (countingCenter38 n) (Real.pi / 4)) : z.re < w.re := by
  obtain ⟨_, hz'⟩ := counting_central_re_bounds38 hz
  obtain ⟨hw', _⟩ := counting_small_re_bounds38 hw
  have hn' : (N : ℝ) + 1 ≤ (n : ℝ) := by
    exact_mod_cast (show (N : ℤ) + 1 ≤ n by omega)
  unfold countingRadius38 at hz'
  nlinarith [Real.pi_pos]

theorem counting_small_central_re_lt38 {N : ℕ} {n : ℤ} (hn : n < -(N : ℤ)) {z w : ℂ}
    (hz : z ∈ ball (countingCenter38 n) (Real.pi / 4))
    (hw : w ∈ ball (0 : ℂ) (countingRadius38 N)) : z.re < w.re := by
  obtain ⟨_, hz'⟩ := counting_small_re_bounds38 hz
  obtain ⟨hw', _⟩ := counting_central_re_bounds38 hw
  have hn' : (n : ℝ) + 1 ≤ -(N : ℝ) := by
    exact_mod_cast (show n + 1 ≤ -(N : ℤ) by omega)
  unfold countingRadius38 at hw'
  nlinarith [Real.pi_pos]

theorem counting_small_ball_disjoint38 {n m : ℤ} (hnm : n ≠ m) :
    Disjoint (ball (countingCenter38 n) (Real.pi / 4))
      (ball (countingCenter38 m) (Real.pi / 4)) := by
  rw [Set.disjoint_left]
  intro z hzn hzm
  rcases lt_or_gt_of_ne hnm with h | h
  · exact (lt_irrefl z.re) (counting_small_blocks_re_lt38 h hzn hzm)
  · exact (lt_irrefl z.re) (counting_small_blocks_re_lt38 h hzm hzn)

theorem counting_central_small_disjoint38 {N : ℕ} {n : ℤ} (hn : (N : ℤ) < |n|) :
    Disjoint (ball (0 : ℂ) (countingRadius38 N))
      (ball (countingCenter38 n) (Real.pi / 4)) := by
  rw [Set.disjoint_left]
  intro z hz hnz
  rcases lt_abs.mp hn with h | h
  · exact (lt_irrefl z.re) (counting_central_small_re_lt38 h hz hnz)
  · have h' : n < -(N : ℤ) := by linarith
    exact (lt_irrefl z.re) (counting_small_central_re_lt38 h' hnz hz)

end
end NlsGge.GK38
