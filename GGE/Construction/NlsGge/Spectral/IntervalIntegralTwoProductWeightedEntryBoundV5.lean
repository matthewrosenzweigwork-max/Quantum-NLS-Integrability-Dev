import NlsGge.Spectral.IntervalIntegralRealPowerFactorialV5
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace NlsGge.SpectralFoundations

/-- Weighted two-product estimate: a source entry bounded by M times a Dyson
entry bounded by D*s^n integrates to the next power with the expected 1/(n+1).
This is the scalar step that creates factorial decay. -/
theorem norm_intervalIntegral_two_products_weighted_le
    (f₀ f₁ g₀ g₁ : ℝ → ℂ) (n : ℕ) (t M D : ℝ)
    (ht : 0 ≤ t) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hf₀ : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖f₀ s‖ ≤ M)
    (hf₁ : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖f₁ s‖ ≤ M)
    (hg₀ : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖g₀ s‖ ≤ D * s ^ n)
    (hg₁ : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖g₁ s‖ ≤ D * s ^ n) :
    ‖∫ s in (0 : ℝ)..t, f₀ s * g₀ s + f₁ s * g₁ s‖ ≤
      2 * M * D * t ^ (n + 1) / (n + 1 : ℝ) := by
  have hbound (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) t) :
      ‖f₀ s * g₀ s + f₁ s * g₁ s‖ ≤ 2 * M * D * s ^ n := by
    have hs' : s ∈ Set.Icc (0 : ℝ) t := ⟨le_of_lt hs.1, hs.2⟩
    calc
      ‖f₀ s * g₀ s + f₁ s * g₁ s‖ ≤
          ‖f₀ s * g₀ s‖ + ‖f₁ s * g₁ s‖ := norm_add_le _ _
      _ = ‖f₀ s‖ * ‖g₀ s‖ + ‖f₁ s‖ * ‖g₁ s‖ := by simp only [norm_mul]
      _ ≤ M * (D * s ^ n) + M * (D * s ^ n) := by
        apply add_le_add
        · exact mul_le_mul (hf₀ s hs') (hg₀ s hs') (norm_nonneg _) hM
        · exact mul_le_mul (hf₁ s hs') (hg₁ s hs') (norm_nonneg _) hM
      _ = 2 * M * D * s ^ n := by ring
  have hmajorantCont : ContinuousOn
      (fun s : ℝ => (2 * M * D) * s ^ n) (Set.uIcc (0 : ℝ) t) := by
    fun_prop
  have hmajorantInt : IntervalIntegrable (fun s : ℝ => (2 * M * D) * s ^ n)
      MeasureTheory.volume 0 t := hmajorantCont.intervalIntegrable (μ := MeasureTheory.volume)
  calc
    ‖∫ s in (0 : ℝ)..t, f₀ s * g₀ s + f₁ s * g₁ s‖ ≤
        ∫ s in (0 : ℝ)..t, (2 * M * D) * s ^ n :=
      intervalIntegral.norm_integral_le_of_norm_le ht
        (Filter.Eventually.of_forall hbound) hmajorantInt
    _ = 2 * M * D * t ^ (n + 1) / (n + 1 : ℝ) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral_zero_to_t_real_pow]
      ring

end NlsGge.SpectralFoundations
