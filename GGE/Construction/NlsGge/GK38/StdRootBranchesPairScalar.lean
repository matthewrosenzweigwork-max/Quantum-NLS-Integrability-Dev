import NlsGge.GK38.StdRootBranchesFactors

/-! Scalar estimates for the paired standard-root mechanism. -/
set_option autoImplicit false
open Set Metric
namespace NlsGge.GK38
noncomputable section

theorem stdRoot_norm_le38 {τ g z : ℂ} (hne : τ - z ≠ 0) :
    ‖stdRoot38 τ g z‖ ≤ ‖τ - z‖^2 + ‖g‖ / 4 + 1 := by
  have he : ‖stdRoot38 τ g z‖^2 = ‖(τ - z)^2 - g / 4‖ := by
    rw [← norm_pow, stdRoot_sq_of_ne38 hne]
  have hb : ‖(τ - z)^2 - g / 4‖ ≤ ‖τ - z‖^2 + ‖g‖ / 4 := by
    have h := norm_sub_le ((τ-z)^2) (g/4)
    rw [norm_pow, norm_div, Complex.norm_ofNat] at h
    exact h
  nlinarith [norm_nonneg (stdRoot38 τ g z), sq_nonneg (‖stdRoot38 τ g z‖ - 1)]

theorem root_sqrt_pair_error38 {s₁ s₂ : ℂ} {e : ℝ} (he : 0 ≤ e)
    (h₁ : ‖s₁ - 1‖ ≤ e) (h₂ : ‖s₂ - 1‖ ≤ e) :
    ‖s₁ * s₂ - 1‖ ≤ 2 * e + e^2 := by
  have hs₂ : ‖s₂‖ ≤ 1 + e := by
    have h := norm_le_norm_sub_add s₂ (1 : ℂ)
    norm_num at h
    linarith
  have hid : s₁ * s₂ - 1 = (s₁ - 1) * s₂ + (s₂ - 1) := by ring
  rw [hid]
  calc
    _ ≤ ‖(s₁ - 1) * s₂‖ + ‖s₂ - 1‖ := norm_add_le _ _
    _ = ‖s₁ - 1‖ * ‖s₂‖ + ‖s₂ - 1‖ := by rw [norm_mul]
    _ ≤ e * (1 + e) + e := by gcongr
    _ = 2 * e + e^2 := by ring

theorem root_pair_expand_bound38 (L₁ L₂ s₁ s₂ : ℂ) {e : ℝ} (he : 0 ≤ e)
    (h₁ : ‖s₁ - 1‖ ≤ e) (h₂ : ‖s₂ - 1‖ ≤ e) :
    ‖(L₁ * s₁) * (L₂ * s₂) - 1‖ ≤
      ‖L₁ * L₂ - 1‖ + ‖L₁‖ * ‖L₂‖ * (2 * e + e^2) := by
  have hid : (L₁ * s₁) * (L₂ * s₂) - 1 =
      (L₁ * L₂ - 1) + (L₁ * L₂) * (s₁ * s₂ - 1) := by ring
  rw [hid]
  calc
    _ ≤ ‖L₁ * L₂ - 1‖ + ‖(L₁ * L₂) * (s₁ * s₂ - 1)‖ := norm_add_le _ _
    _ = ‖L₁ * L₂ - 1‖ + ‖L₁‖ * ‖L₂‖ * ‖s₁ * s₂ - 1‖ := by simp only [norm_mul]
    _ ≤ _ := by gcongr; exact root_sqrt_pair_error38 he h₁ h₂

theorem root_pair_linear_norm38 {a z c : ℂ} {D R T : ℝ}
    (hD : ‖a - c‖ ≤ D) (hz : ‖z‖ ≤ R) (hc : ‖c‖ = T)
    (hT : 0 < T) (hsep : 2 * (D + R) ≤ T) :
    T / 2 ≤ ‖a - z‖ ∧ ‖(a - z) / c‖ ≤ 3 / 2 := by
  have hd : ‖(a - z) - c‖ ≤ D + R := by
    have he : (a - z) - c = (a - c) - z := by ring
    rw [he]
    exact (norm_sub_le _ _).trans (add_le_add hD hz)
  have hlo := norm_le_norm_sub_add c (a - z)
  rw [norm_sub_rev, hc] at hlo
  have hhi := norm_le_norm_sub_add (a - z) c
  rw [hc] at hhi
  refine ⟨by linarith, ?_⟩
  rw [norm_div, hc, div_le_iff₀ hT]
  linarith

end
end NlsGge.GK38
