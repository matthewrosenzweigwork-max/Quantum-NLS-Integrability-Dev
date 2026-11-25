import NlsGge.Hierarchy.ALExteriorBranch38
import NlsGge.Analysis.EvenLogDisk38
import Mathlib.Tactic

/-! Batch 38, E07-3 assembly (`D:eq:pAL`, paper/v2.tex l.1881-1885).
With `ζ = 1/z`, `f(ζ) = alExteriorG38 α ζ = w₊(1/ζ)/(1/ζ)^L` is analytic,
nonvanishing and even on the unit disk with `f(0) = e^{M_d/2}`. Its even
logarithm `ℓ` with `ℓ(0) = M_d/2` gives
`p(z) - log z = (1/L) ℓ(1/z) = M_d/(2L) + (1/L) Σ_{k≥1} C_k z^{-2k}` on
`|z| > 1`, with all winding coefficients `C_k` (no truncation at the period). -/

set_option autoImplicit false
noncomputable section

namespace NlsGge.AblowitzLadik

open Metric NlsGge.Analysis
open scoped Nat

theorem alExteriorG38_exp_mass {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) :
    Complex.exp (((alMass38 L α / 2 : ℝ)) : ℂ) = alExteriorG38 α 0 := by
  rw [alExteriorG38_zero hα, Complex.ofReal_exp]

theorem exists_alLog38 {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) :
    ∃ ℓ : ℂ → ℂ, AnalyticOnNhd ℂ ℓ (ball (0:ℂ) 1) ∧
      (∀ ζ ∈ ball (0:ℂ) 1, Complex.exp (ℓ ζ) = alExteriorG38 α ζ) ∧
      ℓ 0 = ((alMass38 L α / 2 : ℝ) : ℂ) ∧ ∀ ζ ∈ ball (0:ℂ) 1, ℓ (-ζ) = ℓ ζ :=
  exists_even_analytic_log_ball38 (alExteriorG38_analytic hα).differentiableOn
    (fun ζ hζ => alExteriorG38_ne_zero hα hζ) (fun ζ hζ => alExteriorG38_neg hα hζ)
    (alExteriorG38_exp_mass hα)

/-- The normalized logarithm `ℓ = log f` on the unit `ζ`-disk (zero for non-admissible `α`). -/
def alLog38 {L : ℕ} [NeZero L] (α : ZMod L → ℂ) : ℂ → ℂ := by
  classical
  exact if h : IsALField38 α then Classical.choose (exists_alLog38 h) else fun _ => 0

theorem alLog38_spec {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) :
    AnalyticOnNhd ℂ (alLog38 α) (ball (0:ℂ) 1) ∧
      (∀ ζ ∈ ball (0:ℂ) 1, Complex.exp (alLog38 α ζ) = alExteriorG38 α ζ) ∧
      alLog38 α 0 = ((alMass38 L α / 2 : ℝ) : ℂ) ∧
      ∀ ζ ∈ ball (0:ℂ) 1, alLog38 α (-ζ) = alLog38 α ζ := by
  classical
  have h := Classical.choose_spec (exists_alLog38 hα)
  simpa [alLog38, hα] using h

/-- The AL Laurent coefficients `C_k` of `D:eq:pAL` (`k ≥ 1`). -/
def alC38 {L : ℕ} [NeZero L] (α : ZMod L → ℂ) (k : ℕ) : ℂ :=
  iteratedDeriv (2 * k) (alLog38 α) 0 / ((2 * k)! : ℂ)

theorem alC38_succ {L : ℕ} [NeZero L] (α : ZMod L → ℂ) (k : ℕ) :
    alC38 α (k + 1) = evenLogCoeff38 (alLog38 α) k := rfl

/-- `p(z) - log z := (1/L) ℓ(1/z)` on `|z| > 1`. -/
def alPMinusLog38 {L : ℕ} [NeZero L] (α : ZMod L → ℂ) (z : ℂ) : ℂ :=
  (1 / (L : ℂ)) * alLog38 α z⁻¹

theorem inv_mem_ball38 {z : ℂ} (hz : 1 < ‖z‖) : z⁻¹ ∈ ball (0:ℂ) 1 := by
  have h0 : z ≠ 0 := by intro h; simp [h] at hz; linarith
  rw [mem_ball_zero_iff, norm_inv]
  exact inv_lt_one_of_one_lt₀ hz

/-- `exp(L (p - log z)) = w₊(z)/z^L`, i.e. `p - log z = (1/L) log(w₊/z^L)` with the
branch fixed at infinity (`= M_d/(2L)` there). -/
theorem alPMinusLog38_exp {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α)
    {z : ℂ} (hz : 1 < ‖z‖) :
    Complex.exp ((L : ℂ) * alPMinusLog38 α z) = alExtW38 α z⁻¹ / z ^ L := by
  have h0 : z ≠ 0 := by intro h; simp [h] at hz; linarith
  have hL : (L : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne L)
  unfold alPMinusLog38 alExtW38
  rw [← mul_assoc, mul_one_div_cancel hL, one_mul, (alLog38_spec hα).2.1 _ (inv_mem_ball38 hz)]
  rw [inv_pow, inv_inv]
  field_simp

/-- `D:eq:pAL`: on `|z| > 1`,
`p(z) - log z = M_d/(2L) + (1/L) Σ_{k≥1} C_k z^{-2k}`, the series converging. -/
theorem alPMinusLog38_laurent {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α)
    {z : ℂ} (hz : 1 < ‖z‖) :
    Summable (fun k : ℕ => alC38 α (k + 1) * z⁻¹ ^ (2 * (k + 1))) ∧
      alPMinusLog38 α z = ((alMass38 L α / (2 * L) : ℝ) : ℂ) +
        (1 / (L : ℂ)) * ∑' k : ℕ, alC38 α (k + 1) * z⁻¹ ^ (2 * (k + 1)) := by
  have hs := alLog38_spec hα
  obtain ⟨hsum, heq⟩ := even_taylor_tsum38 hs.1.differentiableOn hs.2.2.2 (inv_mem_ball38 hz)
  refine ⟨hsum, ?_⟩
  have hL : (L : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne L)
  unfold alPMinusLog38
  simp only [alC38_succ]
  rw [heq, hs.2.2.1]
  push_cast
  field_simp

/-- Cauchy bound for the Laurent coefficients (used for normal convergence, L02). -/
theorem norm_alC38_le {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) (k : ℕ) :
    ‖alC38 α (k + 1)‖ ≤ circleSup38 (alLog38 α) ρ * (ρ ^ (2 * (k + 1)))⁻¹ :=
  norm_evenLogCoeff_le_circleSup38 (alLog38_spec hα).1.differentiableOn hρ hρ1 k

end NlsGge.AblowitzLadik

end
