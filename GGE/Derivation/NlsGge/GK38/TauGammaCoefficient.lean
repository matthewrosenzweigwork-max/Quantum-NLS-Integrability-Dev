import NlsGge.GK38.TauGammaDenominatorBounds

/-! A nonzero common denominator transfers the proved numerator L2 bound to the actual coefficient. -/
set_option autoImplicit false
open Filter Topology Set Metric
namespace NlsGge.GK38
noncomputable section

theorem critical_coefficient_common_l2_bound38 (C : PotPair → ℤ → ℂ) (R : PotPair → ℤ → ℝ)
    (hsel : AdmissibleSelectors38 C R) (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW) :
    ∃ V : Set PotPair, V ∈ 𝓝 φ₀ ∧ V ⊆ gkW ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ φ ∈ V,
      (∀ n : ℤ, lamDot φ n - tauN38 C R φ n = gamma2N38 C R φ n * criticalCoefficient38 C R φ n) ∧
      Summable (fun n : ℤ => ‖criticalCoefficient38 C R φ n‖ ^ 2) ∧
      (∑' n : ℤ, ‖criticalCoefficient38 C R φ n‖ ^ 2) ≤ B := by
  obtain ⟨Ub, hUb, hUbW, b, hb, hB⟩ := critical_denominator_common_bound38 C R hsel φ₀ hφ₀
  obtain ⟨Uq, hUq, _, Bq, hBq, hQ⟩ := exterior_critical_common_l2_bound38 φ₀ hφ₀
  let K := (4 * b)⁻¹ ^ 2
  have hK : 0 ≤ K := sq_nonneg _
  refine ⟨Ub ∩ Uq, inter_mem hUb hUq, fun φ hφ => hUbW hφ.1,
    K * Bq, mul_nonneg hK hBq, fun φ hφ => ?_⟩
  have hpoint (n : ℤ) : ‖criticalCoefficient38 C R φ n‖ ^ 2 ≤
      K * ‖deriv (exteriorFactor38 φ n) (lamDot φ n)‖ ^ 2 := by
    have hdiv : ‖criticalCoefficient38 C R φ n‖ ≤
        ‖deriv (exteriorFactor38 φ n) (lamDot φ n)‖ / (4 * b) := by
      rw [criticalCoefficient38, norm_div, norm_mul, Complex.norm_ofNat]
      exact div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
        (mul_le_mul_of_nonneg_left (hB φ hφ.1 n) (by norm_num))
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hdiv 2
    simpa only [K, div_eq_mul_inv, mul_pow, mul_comm] using hsq
  have hdom := (hQ φ hφ.2).2.1.mul_left K
  have hs := hdom.of_nonneg_of_le (fun n => sq_nonneg _) hpoint
  refine ⟨fun n => critical_coefficient_identity38 C R hsel φ (hUbW hφ.1) n, hs, ?_⟩
  apply (hs.tsum_le_tsum hpoint hdom).trans
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left (hQ φ hφ.2).2.2.2 hK

theorem lamDot_sub_tau38 (C : PotPair → ℤ → ℂ) (R : PotPair → ℤ → ℝ)
    (hsel : AdmissibleSelectors38 C R) (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW) :
    ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ U ⊆ gkW ∧ ∃ a : PotPair → ℤ → ℂ,
      (∀ φ ∈ U, ∀ n : ℤ, lamDot φ n - tauN38 C R φ n = gamma2N38 C R φ n * a φ n) ∧
      IsLocUnifL2Seq a φ₀ := by
  obtain ⟨U, hU, hUW, B, _, h⟩ := critical_coefficient_common_l2_bound38 C R hsel φ₀ hφ₀
  exact ⟨U, hU, hUW, criticalCoefficient38 C R, fun φ hφ => (h φ hφ).1,
    U, hU, B, fun φ hφ => (h φ hφ).2⟩

theorem lamDot_sub_tau (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW) :
    ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ U ⊆ gkW ∧ ∃ a : PotPair → ℤ → ℂ,
      (∀ φ ∈ U, ∀ n : ℤ, lamDot φ n - tauN φ n = gamma2 φ n * a φ n) ∧
      IsLocUnifL2Seq a φ₀ :=
  lamDot_sub_tau38 discC discR isolating_selectors_admissible38 φ₀ hφ₀

end
end NlsGge.GK38
