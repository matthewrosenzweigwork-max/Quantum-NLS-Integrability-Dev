import Mathlib
import NlsGge.Atomic.KSPS.KSPS019

/- KSN012 SUP6 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/KSN/KSN012Sup6.lean.
   SUPPORT (no packet increment), part 1 of the ball-uniform constants for KSN012_missingA:
   a localization constant a = a(B), uniform on the sobolevNorm-1 ball of SobolevC 1, valid for ALL labels n:
     ‖mu φ n - n π‖ ≤ a / indexWeight n  and  ‖criticalEigenvalue φ n - n π‖ ≤ a / indexWeight n.
   (KSPS021W.mu_localization_of / KSPS024W.crit_localization_of give such an a only per φ, because they absorb the
   finitely many low labels using φ's own values.)
   Route: high labels |n| ≥ N0 + N1 + 1 from the landed KSPS-019 head rough_boundary_roots (C/|n| ≤ 2C/indexWeight n);
   low labels from the landed uniform counting KSPS019Support.unif_counting on Cset B (toPotPair_mem_Cset): central
   labels |n| ≤ N1 lie in ball 0 (countingRadius38 N1) (GK38 criticalCandidate_central_mem38 with muSeq_eq_candidate38 /
   lamDot_eq_candidate38), the others in the quarter disc at n π (KSPS019Support.small_mem). Nothing assumed. -/
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.KSN012U
noncomputable section
open NlsGge.GK38 NlsGge.ThirdConsultation.KSPS

theorem sup6_one_le_w (n : ℤ) : 1 ≤ indexWeight n := by
  unfold indexWeight
  rw [Real.one_le_sqrt]
  nlinarith [sq_nonneg (n : ℝ)]

theorem sup6_w_pos (n : ℤ) : 0 < indexWeight n := lt_of_lt_of_le one_pos (sup6_one_le_w n)

theorem sup6_natAbs_cast (n : ℤ) : ((n.natAbs : ℕ) : ℝ) = |(n : ℝ)| := by
  rw [Nat.cast_natAbs, Int.cast_abs]

theorem sup6_w_le_two (n : ℤ) (hn : 1 ≤ |(n : ℝ)|) : indexWeight n ≤ 2 * |(n : ℝ)| := by
  unfold indexWeight
  rw [Real.sqrt_le_left (by positivity)]
  have h := sq_abs (n : ℝ)
  nlinarith

theorem sup6_w_le_of_natAbs (n : ℤ) (M : ℕ) (hn : n.natAbs ≤ M) : indexWeight n ≤ 1 + M := by
  unfold indexWeight
  rw [Real.sqrt_le_left (by positivity)]
  have h1 : |(n : ℝ)| ≤ M := by
    rw [← sup6_natAbs_cast]; exact_mod_cast hn
  have h2 := sq_abs (n : ℝ)
  have h3 : |(n : ℝ)| ^ 2 ≤ (M : ℝ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  have h4 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  nlinarith

theorem sup6_norm_npi (n : ℤ) : ‖(n : ℂ) * (Real.pi : ℂ)‖ = |(n : ℝ)| * Real.pi := by
  rw [norm_mul, Complex.norm_intCast, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]

/-- Low labels: every labelled root of a function with uniform root counting at cutoff `N1` lies within
    `2 N1 π + π` of `n π`. -/
theorem sup6_low_label {f : ℂ → ℂ} {N1 : ℕ} (h : RootCountingAt38 f 1 N1) (n : ℤ) :
    ‖criticalCandidate38 f N1 n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ 2 * N1 * Real.pi + Real.pi := by
  have hpi := Real.pi_pos
  by_cases hc : criticalCentralIndex38 N1 n
  · have h1 := criticalCandidate_central_mem38 h hc
    rw [Metric.mem_ball, dist_zero_right] at h1
    have habs : |n| ≤ (N1 : ℤ) := abs_le.mpr hc
    have habsR : |(n : ℝ)| ≤ N1 := by exact_mod_cast habs
    have h2 := norm_sub_le (criticalCandidate38 f N1 n) ((n : ℂ) * (Real.pi : ℂ))
    rw [sup6_norm_npi] at h2
    have h3 : |(n : ℝ)| * Real.pi ≤ N1 * Real.pi := mul_le_mul_of_nonneg_right habsR hpi.le
    unfold countingRadius38 at h1
    linarith
  · have hlt : (N1 : ℤ) < |n| := by
      unfold criticalCentralIndex38 at hc
      by_contra hcon
      push_neg at hcon
      exact hc (abs_le.mp hcon)
    have h1 := NlsGge.ThirdConsultation.KSPS019Support.small_mem h hlt
    rw [Metric.mem_ball, dist_eq_norm] at h1
    have h1' : ‖criticalCandidate38 f N1 n - (n : ℂ) * (Real.pi : ℂ)‖ < Real.pi / 4 := h1
    have h4 : (0 : ℝ) ≤ 2 * N1 * Real.pi := by positivity
    linarith

/-- Ball-uniform localization constant, valid for all labels. -/
theorem sup6_unif_loc (B : ℝ) (hB : 0 < B) :
    ∃ a : ℝ, 0 ≤ a ∧ ∀ φ : SobolevC 1, sobolevNorm 1 φ ≤ B → ∀ n : ℤ,
      ‖mu φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n ∧
      ‖criticalEigenvalue φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n := by
  obtain ⟨C, N0, hC, h19⟩ := rough_boundary_roots B hB
  obtain ⟨N1, -, hcount⟩ := NlsGge.ThirdConsultation.KSPS019Support.unif_counting hB.le
  have hpi := Real.pi_pos
  set M : ℕ := N0 + N1 + 1 with hM
  set K : ℝ := 2 * N1 * Real.pi + Real.pi with hK
  have hK0 : 0 ≤ K := by positivity
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  refine ⟨2 * C + K * (1 + M), by positivity, fun φ hφ n => ?_⟩
  have hw1 := sup6_one_le_w n
  have hw0 := sup6_w_pos n
  have hKM0 : 0 ≤ K * (1 + M) := by positivity
  by_cases hn : M ≤ n.natAbs
  · have hb := h19 φ hφ n (by omega)
    rw [sup6_natAbs_cast] at hb
    have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      rw [← sup6_natAbs_cast]; exact_mod_cast (show 1 ≤ n.natAbs by omega)
    have hpos : 0 < |(n : ℝ)| := by linarith
    have hw2 := sup6_w_le_two n hn1
    have hCn : C / |(n : ℝ)| ≤ (2 * C + K * (1 + M)) / indexWeight n := by
      rw [div_le_div_iff₀ hpos hw0]
      nlinarith [mul_le_mul_of_nonneg_left hw2 hC, mul_nonneg hKM0 hpos.le]
    have hm0 := norm_nonneg (mu φ n - (n : ℂ) * (Real.pi : ℂ))
    have hc0 := norm_nonneg (criticalEigenvalue φ n - (n : ℂ) * (Real.pi : ℂ))
    exact ⟨by linarith, by linarith⟩
  · have hwM : indexWeight n ≤ 1 + M := sup6_w_le_of_natAbs n M (by omega)
    have hKw : K ≤ (2 * C + K * (1 + M)) / indexWeight n := by
      rw [le_div_iff₀ hw0]
      have := mul_le_mul_of_nonneg_left hwM hK0
      linarith
    obtain ⟨hD, hCr⟩ := hcount (toPotPair φ)
      (NlsGge.ThirdConsultation.KSPS019Support.toPotPair_mem_Cset φ hφ)
    have h1 := sup6_low_label hD n
    have h2 := sup6_low_label hCr n
    rw [← muSeq_eq_candidate38 (toPotPair φ) hD] at h1
    rw [← lamDot_eq_candidate38 (toPotPair φ) hCr] at h2
    exact ⟨(show ‖muSeq (toPotPair φ) n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ _ from h1.trans hKw),
      (show ‖lamDot (toPotPair φ) n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ _ from h2.trans hKw)⟩

end
end NlsGge.ThirdConsultation.KSN012U
