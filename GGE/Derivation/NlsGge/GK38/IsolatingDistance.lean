import NlsGge.GK38.IsolatingDefs
import Mathlib.Analysis.Normed.Affine.AddTorsor

/-! Actual sInf distance between positive open complex balls.
Nonempty and lower-bound prerequisites precede every sInf estimate. -/
set_option autoImplicit false
open Set Metric
namespace NlsGge.GK38
noncomputable section

def ballDistances38 (c d : ℂ) (r s : ℝ) : Set ℝ :=
  {v | ∃ z ∈ ball c r, ∃ w ∈ ball d s, v = dist z w}

theorem ballDistances38_nonempty (c d : ℂ) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    (ballDistances38 c d r s).Nonempty :=
  ⟨dist c d, c, mem_ball_self hr, d, mem_ball_self hs, rfl⟩

theorem ballDistances38_bddBelow (c d : ℂ) (r s : ℝ) : BddBelow (ballDistances38 c d r s) := by
  refine ⟨0, ?_⟩
  rintro v ⟨z, _, w, _, rfl⟩
  exact dist_nonneg

theorem ballDistance38_lower (c d : ℂ) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    max 0 (dist c d - r - s) ≤ ballDistance38 c d r s := by
  apply le_csInf (ballDistances38_nonempty c d hr hs)
  rintro v ⟨z, hz, w, hw, rfl⟩
  apply max_le
  · exact dist_nonneg
  · have ht := dist_triangle4 c z w d
    have hz' : dist c z < r := by simpa only [dist_comm] using mem_ball.mp hz
    have hw' : dist w d < s := mem_ball.mp hw
    linarith

theorem ballDistance38_le_pair (c d : ℂ) (r s : ℝ) {z w : ℂ}
    (hz : z ∈ ball c r) (hw : w ∈ ball d s) : ballDistance38 c d r s ≤ dist z w :=
  csInf_le (ballDistances38_bddBelow c d r s) ⟨z, hz, w, hw, rfl⟩

theorem ballDistance38_zero_of_overlap (c d : ℂ) {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hD : dist c d < r + s) : ballDistance38 c d r s = 0 := by
  let t := r / (r + s)
  have hsum : 0 < r + s := add_pos hr hs
  have ht : 0 < t := div_pos hr hsum
  have htt : t * (r + s) = r := div_mul_cancel₀ r (ne_of_gt hsum)
  have hut : 0 < 1 - t := by
    have ht1 : t < 1 := (div_lt_one hsum).mpr (by linarith)
    linarith
  have hutt : (1 - t) * (r + s) = s := by nlinarith
  let z : ℂ := AffineMap.lineMap c d t
  have hz : z ∈ ball c r := by
    rw [mem_ball, dist_lineMap_left, Real.norm_eq_abs, abs_of_pos ht]
    nlinarith [mul_lt_mul_of_pos_left hD ht]
  have hw : z ∈ ball d s := by
    rw [mem_ball, dist_lineMap_right, Real.norm_eq_abs, abs_of_pos hut]
    nlinarith [mul_lt_mul_of_pos_left hD hut]
  apply le_antisymm
  · simpa only [dist_self] using ballDistance38_le_pair c d r s hz hw
  · exact (le_max_left _ _).trans (ballDistance38_lower c d hr hs)

theorem ballDistance38_upper_separated (c d : ℂ) {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hD : r + s ≤ dist c d) :
    ballDistance38 c d r s ≤ dist c d - r - s := by
  have hsum : 0 < r + s := add_pos hr hs
  have hposD : 0 < dist c d := hsum.trans_le hD
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ : ℝ := min (1 / 2) (ε / (2 * (r + s)))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (by positivity))
  have hδ1 : δ < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hδb : δ * (r + s) ≤ ε := by
    have hh : δ ≤ ε / (2 * (r + s)) := min_le_right _ _
    have hh' := (le_div_iff₀ (by positivity : 0 < 2 * (r + s))).mp hh
    nlinarith
  let a : ℝ := (1 - δ) * r / dist c d
  let b : ℝ := 1 - (1 - δ) * s / dist c d
  have ha : 0 ≤ a := le_of_lt (div_pos (mul_pos (by linarith) hr) hposD)
  have hb : 0 ≤ 1 - b := by
    dsimp [b]
    have := div_pos (mul_pos (by linarith : 0 < 1 - δ) hs) hposD
    linarith
  have haD : a * dist c d = (1 - δ) * r := div_mul_cancel₀ _ (ne_of_gt hposD)
  have hbD : (1 - b) * dist c d = (1 - δ) * s := by
    dsimp [b]
    rw [sub_sub_cancel, div_mul_cancel₀ _ (ne_of_gt hposD)]
  have hab : a ≤ b := by nlinarith [mul_nonneg hδ.le hsum.le]
  let z : ℂ := AffineMap.lineMap c d a
  let w : ℂ := AffineMap.lineMap c d b
  have hz : z ∈ ball c r := by
    rw [mem_ball, dist_lineMap_left, Real.norm_eq_abs, abs_of_nonneg ha, haD]
    nlinarith
  have hw : w ∈ ball d s := by
    rw [mem_ball, dist_lineMap_right, Real.norm_eq_abs, abs_of_nonneg hb, hbD]
    nlinarith
  have hdist : dist z w = dist c d - r - s + δ * (r + s) := by
    rw [dist_lineMap_lineMap, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hab)]
    nlinarith [haD, hbD]
  calc ballDistance38 c d r s ≤ dist z w := ballDistance38_le_pair c d r s hz hw
    _ = _ := hdist
    _ ≤ dist c d - r - s + ε := by linarith

theorem ballDistance38_eq (c d : ℂ) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    ballDistance38 c d r s = max 0 (dist c d - r - s) := by
  apply le_antisymm _ (ballDistance38_lower c d hr hs)
  by_cases hD : dist c d < r + s
  · rw [ballDistance38_zero_of_overlap c d hr hs hD]
    exact le_max_left _ _
  · exact (ballDistance38_upper_separated c d hr hs (le_of_not_gt hD)).trans (le_max_right _ _)

theorem ballDistance38_wellDefined (c d : ℂ) (r s : ℝ) (hr : 0 < r) (hs : 0 < s) :
    {v : ℝ | ∃ z ∈ ball c r, ∃ w ∈ ball d s, v = dist z w}.Nonempty ∧
      BddBelow {v : ℝ | ∃ z ∈ ball c r, ∃ w ∈ ball d s, v = dist z w} ∧
      ballDistance38 c d r s = max 0 (dist c d - r - s) :=
  ⟨ballDistances38_nonempty c d hr hs, ballDistances38_bddBelow c d r s, ballDistance38_eq c d hr hs⟩

end
end NlsGge.GK38
