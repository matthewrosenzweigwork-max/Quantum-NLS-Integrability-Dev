import NlsGge.GK38.StdRootBranchesDefs

/-! Scalar branch geometry for arbitrary complex unordered and repeated endpoints.
GK I.12(12.4): the linear prefactor fixes the standard branch's sign. -/

set_option autoImplicit false
open Set Metric
namespace NlsGge.GK38
noncomputable section

theorem stdRoot_degenerate38 (a z : ℂ) : stdRoot38 a 0 z = a - z := by
  simp [stdRoot38]

theorem stdRoot_swap38 (a b z : ℂ) :
    stdRoot38 ((a + b) / 2) ((b - a)^2) z =
      stdRoot38 ((b + a) / 2) ((a - b)^2) z := by
  have hm : (a + b) / 2 = (b + a) / 2 := by ring
  have hg : (b - a)^2 = (a - b)^2 := by ring
  rw [hm, hg]

theorem stdRoot_midpoint_mem38 (a b : ℂ) : (a + b) / 2 ∈ segment ℝ a b := by
  refine ⟨(1 / 2 : ℝ), (1 / 2 : ℝ), by norm_num, by norm_num, by norm_num, ?_⟩
  simp only [Complex.real_smul]
  push_cast
  ring

theorem stdRoot_midpoint_ne38 {a b z : ℂ} (hz : z ∉ segment ℝ a b) :
    (a + b) / 2 - z ≠ 0 := by
  intro h
  apply hz
  rw [← sub_eq_zero.mp h]
  exact stdRoot_midpoint_mem38 a b

theorem stdRoot_sq_of_ne38 {τ g2 z : ℂ} (h : τ - z ≠ 0) :
    stdRoot38 τ g2 z ^ 2 = (τ - z)^2 - g2 / 4 := by
  unfold stdRoot38
  rw [mul_pow, Lib.sqrt_sq]
  field_simp [h]

theorem stdRoot_sq38 (a b z : ℂ) (hz : z ∉ segment ℝ a b) :
    stdRoot38 ((a + b) / 2) ((b - a)^2) z ^ 2 = (a - z) * (b - z) := by
  rw [stdRoot_sq_of_ne38 (stdRoot_midpoint_ne38 hz)]
  ring

theorem stdRoot_ne_zero38 (a b z : ℂ) (hz : z ∉ segment ℝ a b) :
    stdRoot38 ((a + b) / 2) ((b - a)^2) z ≠ 0 := by
  have ha : a - z ≠ 0 := sub_ne_zero.mpr
    (ne_of_mem_of_not_mem (left_mem_segment ℝ a b) hz)
  have hb : b - z ≠ 0 := sub_ne_zero.mpr
    (ne_of_mem_of_not_mem (right_mem_segment ℝ a b) hz)
  intro h
  apply mul_ne_zero ha hb
  rw [← stdRoot_sq38 a b z hz, h]
  simp

/-- A segment described by the symmetric mean and squared gap, including collapse. -/
theorem segment_symmetric_iff38 (a b z : ℂ) :
    z ∈ segment ℝ a b ↔ ∃ t : ℝ, t ∈ Icc 0 1 ∧
      (z - (a + b) / 2)^2 = (t : ℂ)^2 * (b - a)^2 / 4 := by
  constructor
  · intro hz
    rw [segment_eq_image ℝ a b] at hz
    obtain ⟨s, hs, rfl⟩ := hz
    refine ⟨|2 * s - 1|, ⟨abs_nonneg _, ?_⟩, ?_⟩
    · rw [abs_le]
      constructor <;> linarith [hs.1, hs.2]
    · have hsq : (|2 * s - 1| : ℝ)^2 = (2 * s - 1)^2 := sq_abs _
      have hc : ((|2 * s - 1| : ℝ) : ℂ)^2 = ((2 * s - 1 : ℝ) : ℂ)^2 := by
        exact_mod_cast hsq
      rw [hc]
      simp only [Complex.real_smul]
      push_cast
      ring
  · rintro ⟨t, ht, he⟩
    have hs : (z - (a + b) / 2)^2 = ((t : ℂ) * (b - a) / 2)^2 := by
      rw [he]; ring
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with hp | hp
    · rw [segment_eq_image ℝ a b]
      refine ⟨(1 + t) / 2, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
      simp only [Complex.real_smul]
      push_cast
      linear_combination -hp
    · rw [segment_eq_image ℝ a b]
      refine ⟨(1 - t) / 2, ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
      simp only [Complex.real_smul]
      push_cast
      linear_combination -hp

end
end NlsGge.GK38
