import Mathlib
import QuantumNLS.HolomorphicStageC
import QuantumNLS.HolomorphicCauchyC1

/-!
# DEF-017 C2, stage D1: iterated Cauchy bounds for complex-differentiable maps on Banach spaces

For `f : E → F` complex-differentiable on an open `U` (E, F complex normed spaces in one universe, F complete),
with `ball x R ⊆ U` and `‖f‖ ≤ M` on `ball x R`, this file proves the FULL operator-norm bound
  `‖iteratedFDeriv ℂ n f x‖ ≤ M * (4 (n+1) / R)^n`
by iterating the one-variable Cauchy estimate (stage A, `norm_fderiv_apply_le`) on the map
`iteratedFDeriv ℂ k f : E → (E [×k]→L F)`, which is complex-differentiable by stage C. Each step loses a
radius `d = R / (2 (n+1))`, and the derivative of order `k+1` has the same operator norm as the
derivative of order `k` (curry-left isometry).

Consequence (`coeff_radius_bound`): with `r = R / (4 e)`, the coefficients `(n!)⁻¹ • iteratedFDeriv ℂ n f x`
satisfy `‖·‖ * r^n ≤ M e` for all `n`, so the formal series has radius at least `r`.

No symmetry of iterated derivatives and no polarization identity is used: the crude full-norm bound
suffices for the radius, and the diagonal Taylor identity is handled in stage D3.
Standard axioms only.
-/

set_option autoImplicit false
noncomputable section
open Filter Topology Metric Complex Set
open scoped ContDiff

namespace QuantumNLS.HolomorphicStageD1

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The curry-left map is a linear isometry, so `‖iteratedFDeriv (k+1) f y‖ = ‖fderiv (iteratedFDeriv k f) y‖`. -/
theorem norm_iteratedFDeriv_succ_eq_norm_fderiv {F : Type u} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (f : E → F) (k : ℕ) (y : E) :
    ‖iteratedFDeriv ℂ (k + 1) f y‖ = ‖fderiv ℂ (iteratedFDeriv ℂ k f) y‖ := by
  rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, LinearIsometryEquiv.norm_map]

/-- Stage C gives smoothness; hence every iterated derivative is complex-differentiable on the open `U`. -/
theorem differentiableOn_iteratedFDeriv_of_differentiableOn {U : Set E} (hU : IsOpen U) {F : Type u}
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] {f : E → F} (hf : DifferentiableOn ℂ f U)
    (k : ℕ) : DifferentiableOn ℂ (iteratedFDeriv ℂ k f) U := by
  have h := QuantumNLS.HolomorphicStageC.contDiffOn_nat_of_differentiableOn hU (k + 1) F f hf
  have h2 := h.differentiableOn_iteratedFDerivWithin (m := k) (by exact_mod_cast Nat.lt_succ_self k)
    hU.uniqueDiffOn
  refine h2.congr ?_
  intro z hz
  exact ((iteratedFDerivWithin_of_isOpen k hU) hz).symm

/-- Induction step bound: with `‖f‖ ≤ M` on `ball x R`, the `k`-th derivative is bounded by `M (2/d)^k`
on the smaller ball `ball x (R - k d)`. -/
theorem norm_iteratedFDeriv_le_on_ball {U : Set E} (hU : IsOpen U) {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℂ F] [CompleteSpace F] {f : E → F} (hf : DifferentiableOn ℂ f U) {x : E} {R M d : ℝ}
    (hd : 0 < d) (hM0 : 0 ≤ M) (hxU : ball x R ⊆ U) (hM : ∀ z ∈ ball x R, ‖f z‖ ≤ M) (k : ℕ) :
    ∀ y ∈ ball x (R - k * d), ‖iteratedFDeriv ℂ k f y‖ ≤ M * (2 / d) ^ k := by
  induction k with
  | zero =>
    intro y hy
    have hy' : y ∈ ball x R := by simpa using hy
    simpa using hM y hy'
  | succ k ih =>
    intro y hy
    have hkd : (0 : ℝ) ≤ (k : ℝ) * d := mul_nonneg (Nat.cast_nonneg k) hd.le
    have hcast : ((k + 1 : ℕ) : ℝ) * d = (k : ℝ) * d + d := by push_cast; ring
    rw [hcast] at hy
    rw [mem_ball] at hy
    have hsub : ball y d ⊆ ball x (R - (k : ℝ) * d) := by
      intro z hz
      rw [mem_ball] at hz ⊢
      have h1 := dist_triangle z y x
      linarith
    have hsubR : ball x (R - (k : ℝ) * d) ⊆ ball x R :=
      ball_subset_ball (by linarith)
    have hsubU : ball y d ⊆ U := hsub.trans (hsubR.trans hxU)
    have hK : ∀ z ∈ ball y d, ‖iteratedFDeriv ℂ k f z‖ ≤ M * (2 / d) ^ k :=
      fun z hz => ih z (hsub hz)
    have hdiff : DifferentiableOn ℂ (iteratedFDeriv ℂ k f) U :=
      differentiableOn_iteratedFDeriv_of_differentiableOn hU hf k
    have hbnd : (0 : ℝ) ≤ 2 * (M * (2 / d) ^ k) / d :=
      div_nonneg (mul_nonneg (by norm_num) (mul_nonneg hM0 (pow_nonneg (div_nonneg (by norm_num) hd.le) k)))
        hd.le
    have hop : ‖fderiv ℂ (iteratedFDeriv ℂ k f) y‖ ≤ 2 * (M * (2 / d) ^ k) / d := by
      refine ContinuousLinearMap.opNorm_le_bound _ hbnd (fun v => ?_)
      exact QuantumNLS.HolomorphicCauchyC1.norm_fderiv_apply_le hdiff hd hsubU hK v
    rw [norm_iteratedFDeriv_succ_eq_norm_fderiv]
    refine hop.trans (le_of_eq ?_)
    rw [pow_succ]
    ring

/-- The full operator-norm bound for the `n`-th derivative at the centre of the ball. -/
theorem norm_iteratedFDeriv_le {U : Set E} (hU : IsOpen U) {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℂ F] [CompleteSpace F] {f : E → F} (hf : DifferentiableOn ℂ f U) {x : E} {R M : ℝ}
    (hR : 0 < R) (hM0 : 0 ≤ M) (hxU : ball x R ⊆ U) (hM : ∀ z ∈ ball x R, ‖f z‖ ≤ M) (n : ℕ) :
    ‖iteratedFDeriv ℂ n f x‖ ≤ M * (4 * ((n : ℝ) + 1) / R) ^ n := by
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  set d : ℝ := R / (2 * ((n : ℝ) + 1)) with hd_def
  have hd : 0 < d := div_pos hR (by positivity)
  have hnd : (n : ℝ) * d + d = R / 2 := by
    rw [hd_def]; field_simp
  have hx : x ∈ ball x (R - (n : ℝ) * d) := by
    rw [mem_ball, dist_self]
    linarith
  have h := norm_iteratedFDeriv_le_on_ball hU hf hd hM0 hxU hM n x hx
  have hfac : (2 / d) = 4 * ((n : ℝ) + 1) / R := by
    rw [hd_def]; field_simp; norm_num
  rw [hfac] at h
  exact h

/-- Factorial-exponential bound: `(n+1)^n / n! ≤ e · e^n`. -/
theorem factorial_pow_le (n : ℕ) :
    ((n : ℝ) + 1) ^ n / (n.factorial : ℝ) ≤ Real.exp 1 * Real.exp 1 ^ n := by
  have hfac : ((n : ℝ) + 1) ^ n / (n.factorial : ℝ) = ((n : ℝ) + 1) ^ (n + 1) / ((n + 1).factorial : ℝ) := by
    have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
    rw [Nat.factorial_succ, pow_succ]
    push_cast
    rw [mul_comm ((n : ℝ) + 1) (n.factorial : ℝ), mul_div_mul_right _ _ hn1]
  have h1 := Real.pow_div_factorial_le_exp (x := (n : ℝ) + 1) (by positivity) (n + 1)
  have h2 : Real.exp ((n : ℝ) + 1) = Real.exp 1 * Real.exp 1 ^ n := by
    rw [Real.exp_add, ← Real.exp_nat_mul, mul_one, mul_comm]
  rw [hfac]
  calc ((n : ℝ) + 1) ^ (n + 1) / ((n + 1).factorial : ℝ) ≤ Real.exp ((n : ℝ) + 1) := h1
    _ = Real.exp 1 * Real.exp 1 ^ n := h2

/-- The coefficient bound: with `r = R / (4 e)`, `‖(n!)⁻¹ • iteratedFDeriv ℂ n f x‖ * r^n ≤ M e`. -/
theorem coeff_radius_bound {U : Set E} (hU : IsOpen U) {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℂ F] [CompleteSpace F] {f : E → F} (hf : DifferentiableOn ℂ f U) {x : E} {R M : ℝ}
    (hR : 0 < R) (hM0 : 0 ≤ M) (hxU : ball x R ⊆ U) (hM : ∀ z ∈ ball x R, ‖f z‖ ≤ M) (n : ℕ) :
    ‖((n.factorial : ℂ))⁻¹ • iteratedFDeriv ℂ n f x‖ * (R / (4 * Real.exp 1)) ^ n ≤ M * Real.exp 1 := by
  have hb := norm_iteratedFDeriv_le hU hf hR hM0 hxU hM n
  have hpos : (0 : ℝ) < (n.factorial : ℝ) := by positivity
  have hnorm : ‖((n.factorial : ℂ))⁻¹ • iteratedFDeriv ℂ n f x‖
      = (n.factorial : ℝ)⁻¹ * ‖iteratedFDeriv ℂ n f x‖ := by
    rw [norm_smul, norm_inv, Complex.norm_natCast]
  rw [hnorm]
  have hexp : Real.exp 1 > 0 := Real.exp_pos 1
  have hRne : R ≠ 0 := hR.ne'
  have hexpne : Real.exp 1 ≠ 0 := hexp.ne'
  have hen : Real.exp 1 ^ n ≠ 0 := pow_ne_zero n hexpne
  have hkey : (4 * ((n : ℝ) + 1) / R) * (R / (4 * Real.exp 1)) = ((n : ℝ) + 1) / Real.exp 1 := by
    field_simp
  have hfac := factorial_pow_le n
  have e1 : (4 * ((n : ℝ) + 1) / R) ^ n * (R / (4 * Real.exp 1)) ^ n
      = ((n : ℝ) + 1) ^ n / Real.exp 1 ^ n := by
    rw [← mul_pow, hkey, div_pow]
  calc (n.factorial : ℝ)⁻¹ * ‖iteratedFDeriv ℂ n f x‖ * (R / (4 * Real.exp 1)) ^ n
      ≤ (n.factorial : ℝ)⁻¹ * (M * (4 * ((n : ℝ) + 1) / R) ^ n) * (R / (4 * Real.exp 1)) ^ n := by
        gcongr
    _ = (n.factorial : ℝ)⁻¹ * M * (((n : ℝ) + 1) ^ n / Real.exp 1 ^ n) := by
        rw [← e1]; ring
    _ = M * (((n : ℝ) + 1) ^ n / (n.factorial : ℝ)) / Real.exp 1 ^ n := by
        ring
    _ ≤ M * (Real.exp 1 * Real.exp 1 ^ n) / Real.exp 1 ^ n := by
        gcongr
    _ = M * Real.exp 1 := by
        field_simp

end QuantumNLS.HolomorphicStageD1

#print axioms QuantumNLS.HolomorphicStageD1.norm_iteratedFDeriv_le
#print axioms QuantumNLS.HolomorphicStageD1.coeff_radius_bound
