import Mathlib
import QuantumNLS.HolomorphicStageD1
import QuantumNLS.HolomorphicStageD2
import QuantumNLS.HolomorphicCauchyC1

/-!
# DEF-017 C2, stage D3: complex-differentiable maps on complex Banach spaces are analytic (power series)

Main results (E, F complex normed spaces in one universe `Type u`, F complete, `U ⊆ E` open,
`f : E → F` complex-differentiable on `U`, `x ∈ U`):

* `hasFPowerSeriesOnBall_of_differentiableOn`: there are `r > 0` with
  `HasFPowerSeriesOnBall f (fun n => (n!)⁻¹ • iteratedFDeriv ℂ n f x) x r`.
* `analyticAt_of_differentiableOn`: `AnalyticAt ℂ f x`.
* `analyticOnNhd_of_differentiableOn`: `AnalyticOnNhd ℂ f U`.

Proof. Pick a ball `ball x R ⊆ U` on which `‖f‖ ≤ M` (stage A, `exists_local_bound`). Set `r = R/(4e)`.
* Radius: stage D1 gives `(n!)⁻¹ ‖iteratedFDeriv ℂ n f x‖ r^n ≤ M e` for all `n`, hence `r ≤ radius`.
* Convergence: for `‖y‖ < r`, the slice `s ↦ f (x + s • y)` is complex-differentiable on `ball 0 2`
  (`‖s • y‖ < R` there), so the one-variable Taylor theorem `Complex.hasSum_taylorSeries_on_ball` at `c = 0`, `z = 1`
  gives `HasSum (n ↦ (n!)⁻¹ (1-0)^n iteratedDeriv n g 0) (f (x+y))`. Stage D2 identifies
  `iteratedDeriv n g 0 = iteratedFDeriv ℂ n f x (fun _ => y)`, so the diagonal series of `p` converges to `f (x+y)`.

`HasFPowerSeriesOnBall` only tests the diagonal `p n (fun _ => y)`, so no symmetry of iterated derivatives and no
polarization identity are needed. Standard axioms only.
-/

set_option autoImplicit false
noncomputable section
open Filter Topology Metric Complex Set

namespace QuantumNLS.HolomorphicStageD3

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Radius and convergence of the coefficient series `(n!)⁻¹ • iteratedFDeriv ℂ n f x` near `x`. -/
theorem hasFPowerSeriesOnBall_of_differentiableOn {U : Set E} (hU : IsOpen U) {F : Type u}
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] {f : E → F}
    (hf : DifferentiableOn ℂ f U) {x : E} (hx : x ∈ U) :
    ∃ r : NNReal, 0 < r ∧
      HasFPowerSeriesOnBall f (fun n : ℕ => ((n.factorial : ℂ))⁻¹ • iteratedFDeriv ℂ n f x) x r := by
  obtain ⟨R, hR, hxU, K, hK⟩ := QuantumNLS.HolomorphicCauchyC1.exists_local_bound hU hf hx
  have hM0 : 0 ≤ max K 0 := le_max_right _ _
  have hM : ∀ z ∈ ball x R, ‖f z‖ ≤ max K 0 := fun z hz => (hK z hz).trans (le_max_left _ _)
  have hexp : (2 : ℝ) < Real.exp 1 := by
    have := Real.add_one_lt_exp (one_ne_zero : (1 : ℝ) ≠ 0)
    linarith
  set r0 : ℝ := R / (4 * Real.exp 1) with hr0_def
  have hr0 : 0 < r0 := div_pos hR (by positivity)
  have hr0_lt : r0 < R / 2 := by
    rw [hr0_def, div_lt_iff₀ (by positivity)]
    nlinarith
  obtain ⟨r, hrr⟩ : ∃ r : NNReal, (r : ℝ) = r0 := ⟨Real.toNNReal r0, Real.coe_toNNReal r0 hr0.le⟩
  have hr : (0 : NNReal) < r := by
    rw [← NNReal.coe_pos, hrr]
    exact hr0
  refine ⟨r, hr, ?_, ?_, ?_⟩
  · -- radius bound from stage D1
    exact FormalMultilinearSeries.le_radius_of_bound
      (p := fun n : ℕ => ((n.factorial : ℂ))⁻¹ • iteratedFDeriv ℂ n f x) (max K 0 * Real.exp 1)
      (r := r)
      (fun n => by
        rw [hrr]
        exact QuantumNLS.HolomorphicStageD1.coeff_radius_bound hU hf hR hM0 hxU hM n)
  · exact ENNReal.coe_pos.2 hr
  · intro y hy
    -- the slice is complex-differentiable on ball 0 2 and stays in U
    have hyn : ‖y‖ < r0 := by
      have h1 : ‖y‖₊ < r := by
        rw [Metric.mem_eball, edist_zero_right] at hy
        exact ENNReal.coe_lt_coe.1 hy
      have h2 : (‖y‖₊ : ℝ) < (r : ℝ) := NNReal.coe_lt_coe.2 h1
      rw [coe_nnnorm, hrr] at h2
      exact h2
    have hsmul : ∀ t : ℂ, ‖t‖ < 2 → x + t • y ∈ U := by
      intro t ht
      apply hxU
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
      have hy2 : ‖y‖ < R / 2 := by linarith
      nlinarith [norm_nonneg t, norm_nonneg y]
    have hlin : DifferentiableOn ℂ (fun s : ℂ => x + s • y) (ball (0 : ℂ) 2) :=
      (by fun_prop : Differentiable ℂ (fun s : ℂ => x + s • y)).differentiableOn
    have hmaps : MapsTo (fun s : ℂ => x + s • y) (ball (0 : ℂ) 2) U := by
      intro s hs
      exact hsmul s (by simpa [mem_ball_zero_iff] using hs)
    have hgd : DifferentiableOn ℂ (fun s : ℂ => f (x + s • y)) (ball (0 : ℂ) 2) :=
      DifferentiableOn.comp hf hlin hmaps
    have h1mem : (1 : ℂ) ∈ ball (0 : ℂ) 2 := by
      simp [mem_ball_zero_iff]
    have hT := Complex.hasSum_taylorSeries_on_ball hgd h1mem
    have hT2 : HasSum (fun n : ℕ => (n.factorial : ℂ)⁻¹ • (1 - 0 : ℂ) ^ n •
        iteratedDeriv n (fun s : ℂ => f (x + s • y)) 0) (f (x + y)) := by
      have h := hT
      rwa [one_smul] at h
    have hdiag : ∀ n : ℕ, iteratedDeriv n (fun s : ℂ => f (x + s • y)) 0
        = iteratedFDeriv ℂ n f x (fun _ => y) := by
      intro n
      have h := QuantumNLS.HolomorphicStageD2.iteratedDeriv_slice hU hf x y n 0 (by simpa using hx)
      rw [zero_smul, add_zero] at h
      exact h
    convert hT2 using 1
    funext n
    simp only [smul_apply]
    rw [hdiag n]
    simp

/-- A complex-differentiable map on an open subset of a complex Banach space is analytic at each point. -/
theorem analyticAt_of_differentiableOn {U : Set E} (hU : IsOpen U) {F : Type u}
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] {f : E → F}
    (hf : DifferentiableOn ℂ f U) {x : E} (hx : x ∈ U) : AnalyticAt ℂ f x := by
  obtain ⟨r, _, h⟩ := hasFPowerSeriesOnBall_of_differentiableOn hU hf hx
  exact h.analyticAt

/-- Bridge: complex-differentiable on an open set implies analytic on that set (Banach domains). -/
theorem analyticOnNhd_of_differentiableOn {U : Set E} (hU : IsOpen U) {F : Type u}
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] {f : E → F}
    (hf : DifferentiableOn ℂ f U) : AnalyticOnNhd ℂ f U :=
  fun _ hx => analyticAt_of_differentiableOn hU hf hx

end QuantumNLS.HolomorphicStageD3

#print axioms QuantumNLS.HolomorphicStageD3.hasFPowerSeriesOnBall_of_differentiableOn
#print axioms QuantumNLS.HolomorphicStageD3.analyticAt_of_differentiableOn
#print axioms QuantumNLS.HolomorphicStageD3.analyticOnNhd_of_differentiableOn
