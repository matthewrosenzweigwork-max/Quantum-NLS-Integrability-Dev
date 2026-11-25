import Mathlib
import QuantumNLS.HolomorphicStageD1
import QuantumNLS.HolomorphicStageD3

/-!
# DEF-017 C2, stage D4: uniform geometric majorants for the Taylor coefficients (GP-05 consumers)

For `f` complex-differentiable on an open `U` (E, F complex normed spaces in one universe, F complete), with
`ball x R ⊆ U` and `‖f‖ ≤ M` on `ball x R`:

* `coeff_uniform_majorant`: for every `y ∈ ball x (R/2)` and every `n`,
  `‖(n!)⁻¹ • iteratedFDeriv ℂ n f y‖ ≤ M * e * (8 e / R)^n`.
  This is a UNIFORM geometric majorant on the half-radius neighbourhood, obtained from stage D1 at the centres `y`
  with radius `R/2` (the ball `ball y (R/2)` lies in `ball x R`).

* `analyticOnNhd_bridge`: the bridge in the form the EXT-025 Ext025A5 modules consume
  (`AnalyticAt ℂ f a` as hypothesis): complex differentiability on an open set gives analyticity at each point and
  on the set, together with the uniform majorant above.

Standard axioms only.
-/

set_option autoImplicit false
noncomputable section
open Filter Topology Metric Complex Set

namespace QuantumNLS.HolomorphicStageD4

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem coeff_uniform_majorant {U : Set E} (hU : IsOpen U) {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℂ F] [CompleteSpace F] {f : E → F} (hf : DifferentiableOn ℂ f U) {x : E} {R M : ℝ}
    (hR : 0 < R) (hM0 : 0 ≤ M) (hxU : ball x R ⊆ U) (hM : ∀ z ∈ ball x R, ‖f z‖ ≤ M) (n : ℕ) :
    ∀ y ∈ ball x (R / 2), ‖((n.factorial : ℂ))⁻¹ • iteratedFDeriv ℂ n f y‖
      ≤ M * Real.exp 1 * (8 * Real.exp 1 / R) ^ n := by
  intro y hy
  have hR2 : 0 < R / 2 := half_pos hR
  have hsub : ball y (R / 2) ⊆ ball x R := by
    intro z hz
    rw [mem_ball] at hz hy ⊢
    have h1 := dist_triangle z y x
    linarith
  have hyU : ball y (R / 2) ⊆ U := hsub.trans hxU
  have hMy : ∀ z ∈ ball y (R / 2), ‖f z‖ ≤ M := fun z hz => hM z (hsub hz)
  have h := QuantumNLS.HolomorphicStageD1.coeff_radius_bound hU hf hR2 hM0 hyU hMy n
  -- h : ‖(n!)⁻¹ • iteratedFDeriv ℂ n f y‖ * ((R/2)/(4 e))^n ≤ M e
  have hpos : (0 : ℝ) < ((R / 2) / (4 * Real.exp 1)) ^ n := by
    apply pow_pos
    exact div_pos hR2 (by positivity)
  have hle := (le_div_iff₀ hpos).2 h
  refine hle.trans (le_of_eq ?_)
  have hprod : (8 * Real.exp 1 / R) * ((R / 2) / (4 * Real.exp 1)) = 1 := by
    field_simp
    norm_num
  have hone : (8 * Real.exp 1 / R) ^ n * ((R / 2) / (4 * Real.exp 1)) ^ n = 1 := by
    rw [← mul_pow, hprod, one_pow]
  rw [div_eq_iff hpos.ne']
  linear_combination (-(M * Real.exp 1)) * hone

/-- The packaged bridge: complex differentiability on an open `U` gives analyticity on `U` and, at each
`x ∈ U`, a positive-radius power series whose `n`-th coefficient is `(n!)⁻¹ • iteratedFDeriv ℂ n f x`. -/
theorem analyticOnNhd_bridge {U : Set E} (hU : IsOpen U) {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℂ F] [CompleteSpace F] {f : E → F} (hf : DifferentiableOn ℂ f U) :
    AnalyticOnNhd ℂ f U ∧ ∀ x ∈ U, ∃ r : NNReal, 0 < r ∧
      HasFPowerSeriesOnBall f (fun n : ℕ => ((n.factorial : ℂ))⁻¹ • iteratedFDeriv ℂ n f x) x r :=
  ⟨QuantumNLS.HolomorphicStageD3.analyticOnNhd_of_differentiableOn hU hf,
    fun _ hx => QuantumNLS.HolomorphicStageD3.hasFPowerSeriesOnBall_of_differentiableOn hU hf hx⟩

end QuantumNLS.HolomorphicStageD4

#print axioms QuantumNLS.HolomorphicStageD4.coeff_uniform_majorant
#print axioms QuantumNLS.HolomorphicStageD4.analyticOnNhd_bridge
