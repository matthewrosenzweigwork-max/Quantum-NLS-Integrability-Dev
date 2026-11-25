import NlsGge.GK38.TauGammaCriticalFactor

/-! Finite scalar denominator algebra never divides by the squared gap. -/
set_option autoImplicit false
open Set Metric
namespace NlsGge.GK38
noncomputable section

theorem critical_denominator_algebra38 (d g q qp : ℂ) (hq : q ≠ 0)
    (hc : 2 * d * q + (d ^ 2 - g / 4) * qp = 0) (hcollapsed : g = 0 → d = 0) :
    2 * q + d * qp ≠ 0 ∧ d = g * (qp / (4 * (2 * q + d * qp))) := by
  have he : d * (2 * q + d * qp) = (g / 4) * qp := by linear_combination hc
  have hB : 2 * q + d * qp ≠ 0 := by
    intro hzero
    have hz : g * qp = 0 := by
      rw [hzero, mul_zero] at he
      linear_combination -4 * he
    rcases mul_eq_zero.mp hz with hg | hp
    · have hd := hcollapsed hg
      rw [hd, zero_mul, add_zero] at hzero
      exact hq ((mul_eq_zero.mp hzero).resolve_left (by norm_num))
    · rw [hp, mul_zero, add_zero] at hzero
      exact hq ((mul_eq_zero.mp hzero).resolve_left (by norm_num))
  refine ⟨hB, ?_⟩
  field_simp
  linear_combination 4 * he

theorem critical_denominator_nonzero38 (C : PotPair → ℤ → ℂ) (R : PotPair → ℤ → ℝ)
    (hsel : AdmissibleSelectors38 C R) (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) :
    criticalDenominator38 C R φ n ≠ 0 := by
  have hf := hsel φ hφ
  obtain ⟨c, N, hg, hs⟩ := hf
  have hq := exterior_nonzero_in_disc38 φ (C φ) (R φ) ⟨c, N, hg, hs⟩ n (lamDot φ n)
    (hs.1 n).2.2.2.1
  exact (critical_denominator_algebra38 _ _ _ _ hq (critical_factor_equation38 C R hsel φ hφ n)
    (fun hg0 => sub_eq_zero.mpr (gamma2_zero_critical_eq_tau38 C R hsel φ hφ n hg0))).1

theorem critical_coefficient_identity38 (C : PotPair → ℤ → ℂ) (R : PotPair → ℤ → ℝ)
    (hsel : AdmissibleSelectors38 C R) (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) :
    lamDot φ n - tauN38 C R φ n = gamma2N38 C R φ n * criticalCoefficient38 C R φ n := by
  have hf := hsel φ hφ
  obtain ⟨c, N, hg, hs⟩ := hf
  have hq := exterior_nonzero_in_disc38 φ (C φ) (R φ) ⟨c, N, hg, hs⟩ n (lamDot φ n)
    (hs.1 n).2.2.2.1
  exact (critical_denominator_algebra38 _ _ _ _ hq (critical_factor_equation38 C R hsel φ hφ n)
    (fun hg0 => sub_eq_zero.mpr (gamma2_zero_critical_eq_tau38 C R hsel φ hφ n hg0))).2

end
end NlsGge.GK38
