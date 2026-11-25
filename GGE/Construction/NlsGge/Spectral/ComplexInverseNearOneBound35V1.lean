import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Tactic
set_option autoImplicit false
namespace NlsGge.SpectralFoundations

/-- Inversion is quantitatively controlled on the half-unit neighborhood
of one. The denominator is proved nonzero before division is used. -/
theorem complexInverse_near_one_bound35
    (c : ℂ) (η : ℝ) (hη : η ≤ 1/2) (h : ‖c-1‖ ≤ η) :
    ‖c⁻¹-1‖ ≤ 2*η := by
  have htriangle : (1 : ℝ) ≤ ‖c-1‖+‖c‖ := by
    calc
      (1 : ℝ) = ‖(c-1)-c‖ := by simp
      _ ≤ ‖c-1‖+‖c‖ := norm_sub_le _ _
  have hnorm : (0 : ℝ) < ‖c‖ := by linarith
  have hc : c ≠ 0 := norm_pos_iff.mp hnorm
  have he : c⁻¹-1=-(c-1)/c := by field_simp [hc]; ring
  rw [he,norm_div,norm_neg]
  apply (div_le_iff₀ hnorm).2
  have hηnonneg : 0 ≤ η := (norm_nonneg _).trans h
  nlinarith

end NlsGge.SpectralFoundations
