import Mathlib
import NlsGge.Atomic.KST.KST018
import NlsGge.Atomic.KST.KST019
import NlsGge.ThirdConsultation.KST.KST047Host

/- KST-047 PRODUCTION01 (proof development, AUTHOR; not self-reviewed).  Target NlsGge/Atomic/KST/KST047.lean,
   namespace NlsGge.ThirdConsultation.KST.  Head VERBATIM from design STATEMENTS/KST.md "## KST-047"
   (gpt6pro_followup10; identical in followups 1-10; no Pro round 5-12 entry touches KST-047).
   Route = source skeleton (WORK_PACKETS KST-047.md): product and ratio give the two magnitudes, r <= π/48 from the
   π/48 coefficient bounds, triangle inequality for the disc.  Support: KST047Host (Balanced, rootRadius). -/
set_option autoImplicit false
noncomputable section
open NlsGge.Atomic.KST004

namespace NlsGge.ThirdConsultation.KST

theorem kst047 (n : ℤ) (a b c : ℂ → ℂ) (σ : ℂ)
    (h : Balanced n a b c σ) :
  0 < rootRadius b c σ ∧
  rootRadius b c σ / 3 ≤ ‖b σ‖ ∧ ‖b σ‖ ≤ 3 * rootRadius b c σ ∧
  rootRadius b c σ / 3 ≤ ‖c σ‖ ∧ ‖c σ‖ ≤ 3 * rootRadius b c σ ∧
  Metric.closedBall σ (2*rootRadius b c σ) ⊆
    Metric.ball (center n) (Real.pi/3) := by
  obtain ⟨⟨-, -, -, hbd⟩, -, hσ, hbc, hlo, hhi⟩ := h
  have hb0 : b σ ≠ 0 := left_ne_zero_of_mul hbc
  have hc0 : c σ ≠ 0 := right_ne_zero_of_mul hbc
  have hB : 0 < ‖b σ‖ := norm_pos_iff.2 hb0
  have hC : 0 < ‖c σ‖ := norm_pos_iff.2 hc0
  have hstrip : σ ∈ spectralStrip n := by
    apply closedBall_subset_strip n
    rw [Metric.mem_closedBall, dist_eq_norm]
    linarith [Real.pi_pos]
  obtain ⟨-, hbπ, hcπ⟩ := hbd σ hstrip
  have hprod : ‖b σ * c σ‖ = ‖b σ‖ * ‖c σ‖ := norm_mul _ _
  have hratio : ‖c σ / b σ‖ = ‖c σ‖ / ‖b σ‖ := norm_div _ _
  rw [hratio] at hlo hhi
  have h1 : ‖c σ‖ ≤ 9 * ‖b σ‖ := by
    have := (div_le_iff₀ hB).1 hhi
    linarith
  have h2 : ‖b σ‖ ≤ 9 * ‖c σ‖ := by
    have := (le_div_iff₀ hB).1 hlo
    linarith
  set r := rootRadius b c σ with hr
  have hrdef : r = Real.sqrt (‖b σ‖ * ‖c σ‖) := by
    rw [hr, rootRadius, hprod]
  have hrpos : 0 < r := by
    rw [hrdef]
    exact Real.sqrt_pos.2 (mul_pos hB hC)
  have hr2 : r ^ 2 = ‖b σ‖ * ‖c σ‖ := by
    rw [hrdef]
    exact Real.sq_sqrt (mul_pos hB hC).le
  have hbu : ‖b σ‖ ≤ 3 * r := by
    by_contra hcon
    push_neg at hcon
    have h3 : (3 * r) * (3 * r) < ‖b σ‖ * ‖b σ‖ :=
      mul_self_lt_mul_self (by positivity) hcon
    nlinarith [mul_le_mul_of_nonneg_left h2 hB.le]
  have hcu : ‖c σ‖ ≤ 3 * r := by
    by_contra hcon
    push_neg at hcon
    have h3 : (3 * r) * (3 * r) < ‖c σ‖ * ‖c σ‖ :=
      mul_self_lt_mul_self (by positivity) hcon
    nlinarith [mul_le_mul_of_nonneg_left h1 hC.le]
  have hbl : r / 3 ≤ ‖b σ‖ := by
    by_contra hcon
    push_neg at hcon
    have h3 : ‖b σ‖ * ‖b σ‖ < (r / 3) * (r / 3) :=
      mul_self_lt_mul_self hB.le hcon
    nlinarith [mul_le_mul_of_nonneg_left h1 hB.le]
  have hcl : r / 3 ≤ ‖c σ‖ := by
    by_contra hcon
    push_neg at hcon
    have h3 : ‖c σ‖ * ‖c σ‖ < (r / 3) * (r / 3) :=
      mul_self_lt_mul_self hC.le hcon
    nlinarith [mul_le_mul_of_nonneg_left h2 hC.le]
  have hrπ : r ≤ Real.pi / 48 := by
    rw [hrdef]
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    have := mul_le_mul hbπ hcπ hC.le (by positivity)
    nlinarith [this]
  refine ⟨hrpos, hbl, hbu, hcl, hcu, ?_⟩
  intro z hz
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  rw [Metric.mem_ball, dist_eq_norm]
  calc ‖z - center n‖ = ‖(z - σ) + (σ - center n)‖ := by congr 1; ring
    _ ≤ ‖z - σ‖ + ‖σ - center n‖ := norm_add_le _ _
    _ < Real.pi / 3 := by linarith [Real.pi_pos]

end NlsGge.ThirdConsultation.KST
end
