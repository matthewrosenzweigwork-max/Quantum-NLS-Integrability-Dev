import Mathlib
import QuantumNLS.RootDensityFormula
import QuantumNLS.RootDiscriminantEntire

/-!
# R-7E0532E7 `thm:root-spectral-density`: assembly of the prerequisite-free parts (continuous-representative class)

Combines `RootDiscriminant*` (the realized DEF-013 discriminant `Δ_u = tr M(L,·)` for continuous `u`: real on `ℝ`, entire,
continuous, `|Δ_u(t)| ≤ 2cosh(√κ ∫₀ᴸ|u|)`) with `RootDensityFormula` (the arcosh density).

`root_density_structure`: for `L, κ > 0`, continuous `u` and the ONE remaining analytic input, the asymptotics
`eq:root-trace-asymptotic` (`Δ_u(t) - 2cos(tL/2) → 0`, a Riemann-Lebesgue statement about the Dyson series that uses no
DEF-013-L²/EXT-025/R-09E1EAE9 input but is NOT proved here), the function `ρ = (πκ)⁻¹ arcosh(|Δ|/2)·1_{|Δ|>2}` is continuous,
`0 ≤ ρ ≤ ‖u‖_{L¹(0,L)}/(π√κ)`, each component of `{|Δ|>2}` is a bounded open interval with `|Δ| = 2` at the endpoints, the endpoint
set is finite on compact intervals, and the measure `ρ dt` is supported on `closure {|Δ|>2}`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal
open QuantumNLS.SpatialTransfer QuantumNLS.RootDiscriminant QuantumNLS.RootDensity
  QuantumNLS.RootDiscriminantBound QuantumNLS.RootDiscriminantContinuity QuantumNLS.RootDiscriminantEntire

namespace QuantumNLS.RootSpectralDensity

/-- `Δ` at the zeros `±(2j+1)π/L` of the free trace tends to `0`. -/
theorem tendsto_small (L κ : ℝ) {u : ℝ → ℂ} (hL : 0 < L)
    (hasym : Tendsto (fun t => discReal L κ u t - 2 * Real.cos (t * L / 2)) (cocompact ℝ) (𝓝 0)) :
    Tendsto (fun j : ℕ => discReal L κ u ((2 * (j : ℝ) + 1) * Real.pi / L)) atTop (𝓝 0) ∧
    Tendsto (fun j : ℕ => discReal L κ u (-((2 * (j : ℝ) + 1) * Real.pi / L))) atTop (𝓝 0) := by
  have h0 : Tendsto (fun j : ℕ => (2 * (j : ℝ) + 1) * Real.pi / L) atTop atTop := by
    refine Tendsto.atTop_div_const hL (Tendsto.atTop_mul_const Real.pi_pos ?_)
    exact tendsto_atTop_add_const_right _ 1 (Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop)
  have hcos : ∀ j : ℕ, Real.cos ((2 * (j : ℝ) + 1) * Real.pi / L * L / 2) = 0 := by
    intro j
    have : (2 * (j : ℝ) + 1) * Real.pi / L * L / 2 = (j : ℝ) * Real.pi + Real.pi / 2 := by
      field_simp
    rw [this, Real.cos_add_pi_div_two, Real.sin_nat_mul_pi]; simp
  constructor
  · have h1 : Tendsto (fun j : ℕ => (2 * (j : ℝ) + 1) * Real.pi / L) atTop (cocompact ℝ) := by
      rw [cocompact_eq_atBot_atTop]; exact h0.mono_right le_sup_right
    have := hasym.comp h1
    refine this.congr (fun j => ?_)
    simp [Function.comp, hcos j]
  · have h1 : Tendsto (fun j : ℕ => -((2 * (j : ℝ) + 1) * Real.pi / L)) atTop (cocompact ℝ) := by
      rw [cocompact_eq_atBot_atTop]; exact (tendsto_neg_atTop_atBot.comp h0).mono_right le_sup_left
    have := hasym.comp h1
    refine this.congr (fun j => ?_)
    have e : Real.cos (-((2 * (j : ℝ) + 1) * Real.pi / L) * L / 2) = 0 := by
      rw [neg_mul, neg_div, Real.cos_neg]
      exact hcos j
    simp only [Function.comp, e]
    ring

theorem exists_small_pos (L κ : ℝ) {u : ℝ → ℂ} (hL : 0 < L)
    (hasym : Tendsto (fun t => discReal L κ u t - 2 * Real.cos (t * L / 2)) (cocompact ℝ) (𝓝 0)) (R : ℝ) :
    ∃ p : ℝ, R ≤ p ∧ |discReal L κ u p| < 2 := by
  obtain ⟨h1, -⟩ := tendsto_small L κ hL hasym
  have h0 : Tendsto (fun j : ℕ => (2 * (j : ℝ) + 1) * Real.pi / L) atTop atTop := by
    refine Tendsto.atTop_div_const hL (Tendsto.atTop_mul_const Real.pi_pos ?_)
    exact tendsto_atTop_add_const_right _ 1 (Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop)
  have h2 : ∀ᶠ j : ℕ in atTop, |discReal L κ u ((2 * (j : ℝ) + 1) * Real.pi / L)| < 2 :=
    ((tendsto_order.1 (by simpa using h1.abs)).2 2 (by norm_num))
  obtain ⟨j, hj1, hj2⟩ := ((h0.eventually_ge_atTop R).and h2).exists
  exact ⟨_, hj1, hj2⟩

theorem exists_small_neg (L κ : ℝ) {u : ℝ → ℂ} (hL : 0 < L)
    (hasym : Tendsto (fun t => discReal L κ u t - 2 * Real.cos (t * L / 2)) (cocompact ℝ) (𝓝 0)) (R : ℝ) :
    ∃ p : ℝ, p ≤ R ∧ |discReal L κ u p| < 2 := by
  obtain ⟨-, h1⟩ := tendsto_small L κ hL hasym
  have h0 : Tendsto (fun j : ℕ => (2 * (j : ℝ) + 1) * Real.pi / L) atTop atTop := by
    refine Tendsto.atTop_div_const hL (Tendsto.atTop_mul_const Real.pi_pos ?_)
    exact tendsto_atTop_add_const_right _ 1 (Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop)
  have h2 : ∀ᶠ j : ℕ in atTop, |discReal L κ u (-((2 * (j : ℝ) + 1) * Real.pi / L))| < 2 :=
    ((tendsto_order.1 (by simpa using h1.abs)).2 2 (by norm_num))
  obtain ⟨j, hj1, hj2⟩ := ((h0.eventually_ge_atTop (-R)).and h2).exists
  exact ⟨_, by linarith, hj2⟩

/-- **Structure of the density (continuous `u`)**, assuming the real-axis asymptotics `eq:root-trace-asymptotic`. -/
theorem root_density_structure (L κ : ℝ) (hL : 0 < L) (hκ : 0 < κ) {u : ℝ → ℂ} (hu : Continuous u)
    (hasym : Tendsto (fun t => discReal L κ u t - 2 * Real.cos (t * L / 2)) (cocompact ℝ) (𝓝 0)) :
    Continuous (rootDensity κ (discReal L κ u)) ∧
    (∀ t, 0 ≤ rootDensity κ (discReal L κ u) t) ∧
    (∀ t, rootDensity κ (discReal L κ u) t ≤
      (∫ x in (0 : ℝ)..L, ‖u x‖) / (Real.pi * Real.sqrt κ)) ∧
    (∀ t, rootDensity κ (discReal L κ u) t = 0 ↔ |discReal L κ u t| ≤ 2) ∧
    (∀ x, 2 < |discReal L κ u x| → ∃ a b : ℝ, a < x ∧ x < b ∧
      connectedComponentIn {t | 2 < |discReal L κ u t|} x = Ioo a b ∧
      |discReal L κ u a| = 2 ∧ |discReal L κ u b| = 2) ∧
    (∀ a b : ℝ, {t : ℝ | t ∈ Icc a b ∧ |discReal L κ u t| = 2}.Finite) ∧
    (volume.withDensity (fun t => ENNReal.ofReal (rootDensity κ (discReal L κ u) t))).support =
      closure {t | 2 < |discReal L κ u t|} := by
  have hc := continuous_discReal κ L hu hL.le
  have hρc := continuous_rootDensity (κ := κ) hc
  have hρ0 := rootDensity_nonneg hκ (discReal L κ u)
  have hI : 0 ≤ ∫ x in (0 : ℝ)..L, ‖u x‖ := intervalIntegral.integral_nonneg hL.le (fun x _ => norm_nonneg _)
  refine ⟨hρc, hρ0, rootDensity_le hκ hI (fun t => abs_discReal_le L hκ hu hL.le t), rootDensity_eq_zero_iff hκ _,
    fun x hx => connectedComponentIn_eq_Ioo hc (fun R => let ⟨p, h1, h2⟩ := exists_small_pos L κ hL hasym R; ⟨p, h1, h2.le⟩)
      (fun R => let ⟨p, h1, h2⟩ := exists_small_neg L κ hL hasym R; ⟨p, h1, h2.le⟩) hx, ?_, ?_⟩
  · refine finite_endpoints (D := discriminant L κ u) (differentiable_discriminant L hu hL.le)
      (fun t => discriminant_eq_discReal L κ hu t) ?_
    obtain ⟨p, -, hp⟩ := exists_small_pos L κ hL hasym 0
    exact ⟨p, ne_of_lt hp⟩
  · have : {t | 0 < rootDensity κ (discReal L κ u) t} = {t | 2 < |discReal L κ u t|} := by
      ext t; exact rootDensity_pos_iff hκ _ t
    rw [support_withDensity hρc hρ0, this]

#print axioms root_density_structure

end QuantumNLS.RootSpectralDensity
