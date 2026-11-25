import Mathlib

/-!
# R-3FEAD88B step C (stage C1): Fourier series calculus for the pointwise Riccati solution

Series-level input for the Ell² → pointwise bridge. Only Mathlib is imported.

Notation: `ex L k y = exp(2πi k y / L)` and, for a coefficient sequence `c : ℤ → ℂ`,
`series L c y = Σ_k c_k ex L k y`.

Proved here (no Sobolev input yet):
* `ex_hasDerivAt`: `d/dy ex L k y = (2πik/L) ex L k y`; `norm_ex`: `|ex L k y| = 1`;
  `ex_add_period`: `ex L k` is `L`-periodic.
* `series_hasDerivAt`: if `Σ|c_k| < ∞`, `Σ|d_k| < ∞` and the coefficient Riccati identity
  `(2πik/L) c_k = i z c_k + d_k` holds for all `k`, then `series L c` has derivative
  `i z · series L c y + series L d y` at every `y` (termwise differentiation, dominated by
  `|(2πik/L) c_k|`, which is summable by the identity).
* `norm_series_le`: `|series L c y| ≤ Σ|c_k|` (the sup bound with constant `Σ|c_k|`).
* `series_add_period`: `series L c` is `L`-periodic.

Scope: this is calculus on coefficient sequences. The link from the Ell² fixed point
(`RiccatiPicardBall`, weighted `ℓ²` with `a > 1/2`) to summable `c`, `d` with the coefficient
identity is NOT in this module (stage C2). No sorry, admit, native_decide or custom axioms.
-/

namespace QuantumNLS.RiccatiPointwise

open Complex Real

/-- The Fourier exponential `ex L k y = exp(2πi k y / L)`. -/
noncomputable def ex (L : ℝ) (k : ℤ) (y : ℝ) : ℂ :=
  Complex.exp ((2 * (π : ℂ) * Complex.I * (k : ℂ) / (L : ℂ)) * (y : ℂ))

/-- The Fourier series `Σ_k c_k exp(2πi k y / L)`. -/
noncomputable def series (L : ℝ) (c : ℤ → ℂ) (y : ℝ) : ℂ :=
  ∑' k : ℤ, c k * ex L k y

theorem norm_ex (L : ℝ) (k : ℤ) (y : ℝ) : ‖ex L k y‖ = 1 := by
  have h : ex L k y = Complex.exp (((2 * π * k * y / L : ℝ) : ℂ) * Complex.I) := by
    unfold ex
    congr 1
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

theorem ex_hasDerivAt (L : ℝ) (k : ℤ) (y : ℝ) :
    HasDerivAt (ex L k) ((2 * (π : ℂ) * Complex.I * (k : ℂ) / (L : ℂ)) * ex L k y) y := by
  have hb : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 y := by
    first
    | exact (hasDerivAt_id y).ofReal_comp
    | exact Complex.ofRealCLM.hasDerivAt
    | exact (Complex.ofRealCLM.hasDerivAt (x := y))
  have h1 := (hb.const_mul (2 * (π : ℂ) * Complex.I * (k : ℂ) / (L : ℂ))).cexp
  have h2 : HasDerivAt (ex L k)
      (Complex.exp ((2 * (π : ℂ) * Complex.I * (k : ℂ) / (L : ℂ)) * (y : ℂ))
        * ((2 * (π : ℂ) * Complex.I * (k : ℂ) / (L : ℂ)) * 1)) y := h1
  refine h2.congr_deriv ?_
  unfold ex
  ring

theorem summable_mul_ex {L : ℝ} {f : ℤ → ℂ} (hf : Summable (fun k => ‖f k‖)) (y : ℝ) :
    Summable (fun k => f k * ex L k y) :=
  Summable.of_norm_bounded (g := fun k => ‖f k‖) hf
    (fun k => le_of_eq (by rw [norm_mul, norm_ex, mul_one]))

/-- Sup bound: `|series L c y| ≤ Σ_k |c_k|`. -/
theorem norm_series_le {L : ℝ} {c : ℤ → ℂ} (hc : Summable (fun k => ‖c k‖)) (y : ℝ) :
    ‖series L c y‖ ≤ ∑' k : ℤ, ‖c k‖ := by
  have hn : ∀ k : ℤ, ‖c k * ex L k y‖ = ‖c k‖ := fun k => by
    rw [norm_mul, norm_ex, mul_one]
  have hs : Summable (fun k : ℤ => ‖c k * ex L k y‖) := by
    simpa only [hn] using hc
  calc ‖series L c y‖ = ‖∑' k : ℤ, c k * ex L k y‖ := rfl
    _ ≤ ∑' k : ℤ, ‖c k * ex L k y‖ := norm_tsum_le_tsum_norm hs
    _ = ∑' k : ℤ, ‖c k‖ := tsum_congr hn

theorem ex_add_period {L : ℝ} (hL : L ≠ 0) (k : ℤ) (y : ℝ) :
    ex L k (y + L) = ex L k y := by
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL
  have key : (2 * (π : ℂ) * Complex.I * (k : ℂ) / (L : ℂ)) * ((y + L : ℝ) : ℂ)
      = (2 * (π : ℂ) * Complex.I * (k : ℂ) / (L : ℂ)) * (y : ℂ)
        + (k : ℂ) * (2 * (π : ℂ) * Complex.I) := by
    push_cast
    first
    | (field_simp; ring)
    | field_simp
    | ring
  unfold ex
  rw [key, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem series_add_period {L : ℝ} (hL : L ≠ 0) (c : ℤ → ℂ) (y : ℝ) :
    series L c (y + L) = series L c y := by
  unfold series
  exact tsum_congr fun k => by rw [ex_add_period hL k y]

/-- **Termwise differentiation of the Fourier series under the coefficient Riccati identity.**
If `Σ|c_k| < ∞`, `Σ|d_k| < ∞` and `(2πik/L) c_k = i z c_k + d_k` for all `k`, then
`series L c` is differentiable at every `y` with derivative `i z series L c y + series L d y`. -/
theorem series_hasDerivAt {L : ℝ} {c d : ℤ → ℂ} {z : ℂ} (hc : Summable (fun k => ‖c k‖))
    (hd : Summable (fun k => ‖d k‖))
    (hrec : ∀ k : ℤ, (2 * (π : ℂ) * Complex.I * (k : ℂ) / (L : ℂ)) * c k
      = Complex.I * z * c k + d k) (y : ℝ) :
    HasDerivAt (series L c) (Complex.I * z * series L c y + series L d y) y := by
  have hu : Summable (fun k : ℤ => ‖(2 * (π : ℂ) * Complex.I * (k : ℂ) / (L : ℂ)) * c k‖) := by
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
      ((hc.mul_left ‖z‖).add hd)
    rw [hrec k]
    calc ‖Complex.I * z * c k + d k‖ ≤ ‖Complex.I * z * c k‖ + ‖d k‖ := norm_add_le _ _
      _ = ‖z‖ * ‖c k‖ + ‖d k‖ := by
        rw [norm_mul, norm_mul, Complex.norm_I, one_mul]
  have hb : ∀ (k : ℤ) (t : ℝ),
      ‖c k * ((2 * (π : ℂ) * Complex.I * (k : ℂ) / (L : ℂ)) * ex L k t)‖
        ≤ ‖(2 * (π : ℂ) * Complex.I * (k : ℂ) / (L : ℂ)) * c k‖ := by
    intro k t
    have e : c k * ((2 * (π : ℂ) * Complex.I * (k : ℂ) / (L : ℂ)) * ex L k t)
        = ((2 * (π : ℂ) * Complex.I * (k : ℂ) / (L : ℂ)) * c k) * ex L k t := by ring
    exact le_of_eq (by rw [e, norm_mul, norm_ex, mul_one])
  have hD := hasDerivAt_tsum (g := fun k t => c k * ex L k t)
    (g' := fun k t => c k * ((2 * (π : ℂ) * Complex.I * (k : ℂ) / (L : ℂ)) * ex L k t))
    hu (fun k t => (ex_hasDerivAt L k t).const_mul (c k)) (fun k t => hb k t)
    (summable_mul_ex hc y) y
  have e1 : ∀ k : ℤ, c k * ((2 * (π : ℂ) * Complex.I * (k : ℂ) / (L : ℂ)) * ex L k y)
      = (Complex.I * z) * (c k * ex L k y) + d k * ex L k y := by
    intro k
    have e : c k * ((2 * (π : ℂ) * Complex.I * (k : ℂ) / (L : ℂ)) * ex L k y)
        = ((2 * (π : ℂ) * Complex.I * (k : ℂ) / (L : ℂ)) * c k) * ex L k y := by ring
    rw [e, hrec k]
    ring
  have hsum : ∑' k : ℤ, c k * ((2 * (π : ℂ) * Complex.I * (k : ℂ) / (L : ℂ)) * ex L k y)
      = Complex.I * z * series L c y + series L d y := by
    rw [tsum_congr e1, Summable.tsum_add ((summable_mul_ex hc y).mul_left (Complex.I * z))
      (summable_mul_ex hd y), tsum_mul_left]
    rfl
  rw [hsum] at hD
  exact hD

end QuantumNLS.RiccatiPointwise

#print axioms QuantumNLS.RiccatiPointwise.norm_ex
#print axioms QuantumNLS.RiccatiPointwise.ex_hasDerivAt
#print axioms QuantumNLS.RiccatiPointwise.norm_series_le
#print axioms QuantumNLS.RiccatiPointwise.ex_add_period
#print axioms QuantumNLS.RiccatiPointwise.series_add_period
#print axioms QuantumNLS.RiccatiPointwise.series_hasDerivAt
