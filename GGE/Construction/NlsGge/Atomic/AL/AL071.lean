import Mathlib

namespace NlsGge.Atomic.AL071


                                                                                                                                            
set_option autoImplicit false

theorem AL071_sinbounds (y : ℝ) (hy : |y| ≤ Real.pi / 2) :
    2 / Real.pi * |y| ≤ |Real.sin y| ∧ |Real.sin y| ≤ |y| := by
  rcases le_total 0 y with h0 | h0
  · rw [abs_of_nonneg h0] at hy ⊢
    have hs : 0 ≤ Real.sin y := Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [Real.pi_pos])
    rw [abs_of_nonneg hs]
    exact ⟨Real.mul_le_sin h0 hy, Real.sin_le h0⟩
  · have h0' : 0 ≤ -y := by linarith
    rw [abs_of_nonpos h0] at hy ⊢
    have hs : 0 ≤ Real.sin (-y) := Real.sin_nonneg_of_nonneg_of_le_pi h0' (by linarith [Real.pi_pos])
    have hs' : Real.sin y ≤ 0 := by
      have := hs
      rw [Real.sin_neg] at this
      linarith
    rw [abs_of_nonpos hs']
    have e : -Real.sin y = Real.sin (-y) := (Real.sin_neg y).symm
    rw [e]
    exact ⟨Real.mul_le_sin h0' hy, Real.sin_le h0'⟩

theorem AL071_main : ((∀ (h : ℝ) (k : ℤ), 0 < h → |(k : ℝ)| * h ≤ 1 / 2 →
    4 * |(k : ℝ)| ≤ |2 * Real.sin (Real.pi * k * h) / h| ∧
    |2 * Real.sin (Real.pi * k * h) / h| ≤ 2 * Real.pi * |(k : ℝ)|) : Prop) := by
  intro h k hh hk
  have hy : |Real.pi * k * h| = Real.pi * (|(k : ℝ)| * h) := by
    rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hh]; ring
  have hyle : |Real.pi * k * h| ≤ Real.pi / 2 := by
    rw [hy]; nlinarith [Real.pi_pos]
  obtain ⟨hl, hu⟩ := AL071_sinbounds _ hyle
  have hden : |2 * Real.sin (Real.pi * k * h) / h| = 2 * |Real.sin (Real.pi * k * h)| / h := by
    rw [abs_div, abs_mul, abs_of_pos hh]; norm_num
  rw [hden]
  rw [hy] at hl hu
  constructor
  · rw [le_div_iff₀ hh]
    have h1 : 2 / Real.pi * (Real.pi * (|(k : ℝ)| * h)) = 2 * (|(k : ℝ)| * h) := by
      field_simp
    nlinarith [Real.pi_pos, abs_nonneg (k : ℝ)]
  · rw [div_le_iff₀ hh]
    nlinarith [Real.pi_pos]


end NlsGge.Atomic.AL071
