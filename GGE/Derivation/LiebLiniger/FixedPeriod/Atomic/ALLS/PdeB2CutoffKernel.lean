import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB2CutoffMode

/-! # Track B, step B2: the cutoff gain for a dilated Schwartz kernel

For a Schwartz function `g` (in the application `g = 𝓕⁻η` for the time cutoff `η`, so that
`δ g(δ·) = 𝓕⁻(η(·/δ))`), the profile `R₁(u) = |g(u)| (1 + |2πu|)^α` (`cutoffProfile`) is
measurable, bounded by Schwartz seminorms and integrable (`0 ≤ α ≤ 1`), and the dilated kernel
`κ_δ(r) = δ g(δr)` satisfies the kernel hypothesis of `cutoff_gain_mode` with equality.
`cutoff_gain_dilated`: for `0 ≤ α ≤ β`, `0 < β < 1/2`, ONE constant `C < ∞` (depending on `g, α, β`
only) gives, for every `δ > 0`, every measurable `θ` and every mode `k`,
`∫ ⟨-2πξ+(2πk)²⟩^{-2β} (∫ |κ_δ(ξ-ζ)| |θ(ζ)| dζ)² dξ ≤ C δ^{2β-2α} ∫ ⟨-2πζ+(2πk)²⟩^{-2α} |θ(ζ)|² dζ`.
The identification `δ g(δ·) = 𝓕⁻(η(·/δ))` (change of variables) is a separate step.
-/

set_option autoImplicit false
noncomputable section

namespace LiebLiniger.FixedPeriod.ALLS.PdeB

open MeasureTheory
open scoped ENNReal SchwartzMap

/-- The kernel profile `R₁(u) = |g(u)| (1 + |2πu|)^α`. -/
def cutoffProfile (g : 𝓢(ℝ, ℂ)) (α : ℝ) (u : ℝ) : ℝ≥0∞ :=
  ‖g u‖ₑ * ENNReal.ofReal ((1 + |2 * Real.pi * u|) ^ α)

theorem one_add_rpow_le_self {α x : ℝ} (hα1 : α ≤ 1) (hx : 0 ≤ x) :
    (1 + x) ^ α ≤ 1 + x := by
  calc (1 + x) ^ α ≤ (1 + x) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hα1
    _ = 1 + x := Real.rpow_one _

theorem cutoffProfile_le (g : 𝓢(ℝ, ℂ)) {α : ℝ} (hα1 : α ≤ 1) (u : ℝ) :
    cutoffProfile g α u ≤ ENNReal.ofReal (‖g u‖ + 2 * Real.pi * (‖u‖ ^ 1 * ‖g u‖)) := by
  unfold cutoffProfile
  rw [← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  have h1 := one_add_rpow_le_self hα1 (abs_nonneg (2 * Real.pi * u))
  have h2 : |2 * Real.pi * u| = 2 * Real.pi * ‖u‖ := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi), Real.norm_eq_abs]
  calc ‖g u‖ * (1 + |2 * Real.pi * u|) ^ α ≤ ‖g u‖ * (1 + |2 * Real.pi * u|) :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = ‖g u‖ + 2 * Real.pi * (‖u‖ ^ 1 * ‖g u‖) := by rw [h2, pow_one]; ring

theorem measurable_cutoffProfile (g : 𝓢(ℝ, ℂ)) (α : ℝ) : Measurable (cutoffProfile g α) := by
  unfold cutoffProfile
  have h1 : Measurable fun u => ‖g u‖ₑ := g.continuous.measurable.enorm
  have h2 : Measurable fun u : ℝ => ENNReal.ofReal ((1 + |2 * Real.pi * u|) ^ α) :=
    ENNReal.measurable_ofReal.comp
      ((by fun_prop : Continuous fun u : ℝ => 1 + |2 * Real.pi * u|).measurable.pow_const α)
  exact h1.mul h2

theorem cutoffProfile_le_const (g : 𝓢(ℝ, ℂ)) {α : ℝ} (hα1 : α ≤ 1) (u : ℝ) :
    cutoffProfile g α u ≤ ENNReal.ofReal
      (SchwartzMap.seminorm ℝ 0 0 g + 2 * Real.pi * SchwartzMap.seminorm ℝ 1 0 g) := by
  refine (cutoffProfile_le g hα1 u).trans (ENNReal.ofReal_le_ofReal ?_)
  have a := SchwartzMap.norm_le_seminorm ℝ g u
  have b := SchwartzMap.norm_pow_mul_le_seminorm ℝ g 1 u
  nlinarith [Real.pi_pos]

theorem lintegral_cutoffProfile_lt_top (g : 𝓢(ℝ, ℂ)) {α : ℝ} (hα1 : α ≤ 1) :
    ∫⁻ u, cutoffProfile g α u < ⊤ := by
  have hi : Integrable (fun u : ℝ => ‖g u‖ + 2 * Real.pi * (‖u‖ ^ 1 * ‖g u‖)) :=
    ((g.integrable (μ := volume)).norm).add
      ((g.integrable_pow_mul (μ := volume) 1).const_mul (2 * Real.pi))
  calc ∫⁻ u, cutoffProfile g α u
      ≤ ∫⁻ u, ENNReal.ofReal (‖g u‖ + 2 * Real.pi * (‖u‖ ^ 1 * ‖g u‖)) :=
        lintegral_mono (cutoffProfile_le g hα1)
    _ < ⊤ := by
      rw [← ofReal_integral_eq_lintegral_ofReal hi
        (ae_of_all _ fun u => by simp only [Pi.zero_apply]; positivity)]
      exact ENNReal.ofReal_lt_top

/-- The dilated kernel `δ g(δ·)` satisfies the kernel hypothesis of `cutoff_gain_mode`. -/
theorem dilated_kernel_bound (g : 𝓢(ℝ, ℂ)) (α : ℝ) {δ : ℝ} (hδ : 0 < δ) (r : ℝ) :
    ‖(δ : ℂ) * g (δ * r)‖ₑ * ENNReal.ofReal ((1 + δ * |2 * Real.pi * r|) ^ α) ≤
      ENNReal.ofReal δ * cutoffProfile g α (δ * r) := by
  apply le_of_eq
  unfold cutoffProfile
  rw [enorm_mul, ← ofReal_norm (δ : ℂ), Complex.norm_real, Real.norm_of_nonneg hδ.le]
  have e : δ * |2 * Real.pi * r| = |2 * Real.pi * (δ * r)| := by
    rw [show 2 * Real.pi * (δ * r) = δ * (2 * Real.pi * r) by ring, abs_mul δ (2 * Real.pi * r), abs_of_pos hδ]
  rw [e, mul_assoc]

/-- Cutoff gain `H^{-α} → H^{-β}` for the dilated Schwartz kernel, uniform in `δ > 0` and `k`. -/
theorem cutoff_gain_dilated {α β : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ0 : 0 < β) (hβ : β < 1 / 2)
    (g : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ δ : ℝ, 0 < δ → ∀ θ : ℝ → ℂ, Measurable θ → ∀ k : ℤ,
      ∫⁻ ξ, modWt (-(2 * β)) k (-(2 * Real.pi) * ξ) *
          (∫⁻ ζ, ‖(δ : ℂ) * g (δ * (ξ - ζ))‖ₑ * ‖θ ζ‖ₑ) ^ 2 ≤
        C * ENNReal.ofReal (δ ^ (2 * β - 2 * α)) *
          ∫⁻ ζ, modWt (-(2 * α)) k (-(2 * Real.pi) * ζ) * ‖θ ζ‖ₑ ^ 2 := by
  have hα1 : α ≤ 1 := by linarith
  set A0 : ℝ≥0∞ := ENNReal.ofReal
    (SchwartzMap.seminorm ℝ 0 0 g + 2 * Real.pi * SchwartzMap.seminorm ℝ 1 0 g) with hA0
  have hI := (lintegral_cutoffProfile_lt_top g hα1).ne
  refine ⟨ENNReal.ofReal ((2 : ℝ) ^ (2 * α)) * (∫⁻ u, cutoffProfile g α u) *
      (A0 * ENNReal.ofReal (|(-(2 * Real.pi))⁻¹| * (2 / (1 - 2 * β))) +
        ∫⁻ u, cutoffProfile g α u), ?_, ?_⟩
  · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI)
      (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top, hI⟩)
  · intro δ hδ θ hθ k
    exact cutoff_gain_mode hα hαβ hβ0 hβ hδ (cutoffProfile g α) (measurable_cutoffProfile g α) A0
      ENNReal.ofReal_ne_top (cutoffProfile_le_const g hα1) (fun r => (δ : ℂ) * g (δ * r)) θ hθ
      (dilated_kernel_bound g α hδ) k

end LiebLiniger.FixedPeriod.ALLS.PdeB
