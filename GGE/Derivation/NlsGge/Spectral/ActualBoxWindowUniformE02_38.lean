import NlsGge.Spectral.ActualQuasimomentumWindowUniformE02_38
import NlsGge.Spectral.ActualCouplingSobolevUniformBox38
set_option autoImplicit false
noncomputable section
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-! # Uniform Box and Window on H¹ balls (campaign 38): `|n| ≥ K R²` -/

theorem ratio_le_of_le_mul_E02_38 (A B R n : ℝ) (hA : 0 < A) (hR : 1 ≤ R) (hB : 0 ≤ B)
    (hn : A * B * R^2 ≤ |n|) : B * R^2 / |n| ≤ 1 / A := by
  have hR2 : 0 < R^2 := by positivity
  rcases eq_or_lt_of_le hB with h0 | hBpos
  · rw [← h0]; simp; positivity
  have hnpos : 0 < |n| := lt_of_lt_of_le (by positivity) hn
  rw [div_le_div_iff₀ hnpos hA]
  nlinarith

/-- Uniform Box and Window: there are absolute constants `K, C` such that for `R ≥ 1`,
`‖u‖_{H¹} ≤ R` and `|n| ≥ K R²`, the Box hypothesis holds with `δ = C R²/|n| ≤ 1/1000` and the
Window hypothesis holds. -/
theorem actualBoxWindow_uniform_E02_38 :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧ ∀ R : ℝ, 1 ≤ R →
      ∀ (u : PhysicalL2) (hu : SobolevSquareSummable 1 (physicalFourier u)),
        ‖physicalSobolevL2 1 u hu‖ ≤ R → ∀ n : ℤ, K * R ^ 2 ≤ |(n : ℝ)| →
          ActualHalfTraceBoxE02_38 u n (C * R ^ 2 / |(n : ℝ)|) ∧
          C * R ^ 2 / |(n : ℝ)| ≤ 1/1000 ∧
          ActualQuasimomentumWindowE02_38 u n := by
  obtain ⟨K₁, C₁, hK₁, hC₁, hbox⟩ := actualHalfTraceBox_uniform38
  obtain ⟨K₂, C₂, hK₂, hC₂, hstrip⟩ := actualHalfTrace_uniformHalfStrip_coupling38
  refine ⟨max (max K₁ K₂) (max (1000 * C₁) (20000 * C₂)), C₁,
    lt_of_lt_of_le hK₁ (le_trans (le_max_left _ _) (le_max_left _ _)), hC₁, ?_⟩
  intro R hR u hu huR n hn
  have hR2 : 0 ≤ R^2 := by positivity
  have h1 : K₁ * R^2 ≤ |(n:ℝ)| :=
    le_trans (mul_le_mul_of_nonneg_right (le_trans (le_max_left _ _) (le_max_left _ _)) hR2) hn
  have h2 : K₂ * R^2 ≤ |(n:ℝ)| :=
    le_trans (mul_le_mul_of_nonneg_right (le_trans (le_max_right _ _) (le_max_left _ _)) hR2) hn
  have h3 : 1000 * C₁ * R^2 ≤ |(n:ℝ)| :=
    le_trans (mul_le_mul_of_nonneg_right (le_trans (le_max_left _ _) (le_max_right _ _)) hR2) hn
  have h4 : 20000 * C₂ * R^2 ≤ |(n:ℝ)| :=
    le_trans (mul_le_mul_of_nonneg_right (le_trans (le_max_right _ _) (le_max_right _ _)) hR2) hn
  refine ⟨hbox R hR u hu huR n h1, ratio_le_of_le_mul_E02_38 1000 C₁ R n (by norm_num) hR hC₁.le h3, ?_⟩
  apply actualQuasimomentumWindow_of_normalizedStrip_E02_38 u n (C₂ * R ^ 2 / |(n : ℝ)|)
    (by positivity) (ratio_le_of_le_mul_E02_38 20000 C₂ R n (by norm_num) hR hC₂.le h4)
  intro τ hτ z hz hz0
  exact hstrip R hR u hu huR τ hτ n h2 z hz hz0

end NlsGge.SpectralFoundations
end
