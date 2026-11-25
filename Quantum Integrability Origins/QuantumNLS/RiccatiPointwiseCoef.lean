import Mathlib
import QuantumNLS.RiccatiPicardBall

/-!
# R-3FEAD88B step C2, stage RiccatiPointwiseCoef: Fourier coefficients of a Picard fixed point

For a fixed point `r : Ell2` of the Banach Riccati map `riccatiT` (RiccatiPicardBall), with
`a > 1/2`, put `c := toField r` and `d := toField u - κ convC(toField v, convC(c, c))`
(definition `rhsD`). Proved here:

* `coef_relation`: `c_k · (i (freq_k - z)) = d_k` for every `k ∈ ℤ`, where `freq_k = 2πk/L`;
* `hrec_of_fixed`: `(2πik/L) c_k = i z c_k + d_k`, the hypothesis of
  `RiccatiPointwise.series_hasDerivAt`;
* `summable_norm_toField`, `summable_norm_rhsD`: `Σ_k ‖c_k‖ < ∞` and `Σ_k ‖d_k‖ < ∞`
  (`ℓ¹` summability from the `H^a` bound, `a > 1/2`);
* `pointwise_coef_exists`: the same data for the fixed point produced by
  `riccatiT_fixed_exists_unique`, with the norm bound `‖r‖ ≤ 2β/Im z`.

Scope: pure coefficient algebra on `Ell2`. No Fourier series, no continuity, no physical κ
(the model κ enters `riccatiT` as is). Standard axioms only; no sorry, admit, native_decide.
-/

set_option autoImplicit false

noncomputable section

namespace QuantumNLS.RiccatiPointwiseCoef

open Complex QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiSobolevE1
  QuantumNLS.RiccatiSobolevE2b QuantumNLS.RiccatiPicardBall

/-- Nonvanishing of the resolvent denominator `i (freq_k - z)` when `Im z > 0`. -/
theorem ne_zero_I_mul (L : ℝ) (z : ℂ) (hz : 0 < z.im) (k : ℤ) :
    Complex.I * (((freq L k : ℝ) : ℂ) - z) ≠ 0 := by
  refine mul_ne_zero Complex.I_ne_zero (fun h => ?_)
  have h2 : z = ((freq L k : ℝ) : ℂ) := (sub_eq_zero.1 h).symm
  have h3 := congrArg Complex.im h2
  simp at h3
  linarith

/-- Coordinates of the resolvent: `(ropCLM z x)_k = x_k / (i (freq_k - z))`. -/
theorem ropCLM_coord (L : ℝ) (z : ℂ) (hz : 0 < z.im) (x : Ell2) (k : ℤ) :
    ropCLM L z hz x k = x k / (Complex.I * (((freq L k : ℝ) : ℂ) - z)) := rfl

/-- The resolvent in the `toField` coordinates. -/
theorem toField_ropCLM_mul (L a : ℝ) (z : ℂ) (hz : 0 < z.im) (x : Ell2) (k : ℤ) :
    toField L a (ropCLM L z hz x) k * (Complex.I * (((freq L k : ℝ) : ℂ) - z))
      = toField L a x k := by
  have hD := ne_zero_I_mul L z hz k
  have hD' : ((freq L k : ℝ) : ℂ) - z ≠ 0 := right_ne_zero_of_mul hD
  have hP := pw_ne_zero L a k
  unfold toField
  rw [ropCLM_coord]
  field_simp

/-- Fixed-point identity in the `Ell2` coordinates: `r_k · i(freq_k - z) = u_k - κ (v (r r))_k`. -/
theorem fixed_coord {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) {z : ℂ} (hz : 0 < z.im) (κ : ℝ)
    {u v r : Ell2} (hr : riccatiT hL ha hz κ u v r = r) (k : ℤ) :
    r k * (Complex.I * (((freq L k : ℝ) : ℂ) - z))
      = u k - (κ : ℂ) * mulBil hL ha v (mulBil hL ha r r) k := by
  have hD := ne_zero_I_mul L z hz k
  have hD' : ((freq L k : ℝ) : ℂ) - z ≠ 0 := right_ne_zero_of_mul hD
  have h := congrArg (fun x : Ell2 => x k) hr
  simp only [riccatiT, lp.coeFn_sub, lp.coeFn_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    ropCLM_coord] at h
  rw [← h]
  field_simp

/-- The right-hand side `d = toField u - κ convC(toField v, convC(c, c))` with `c = toField r`. -/
def rhsD (L a κ : ℝ) (u v r : Ell2) : ℤ → ℂ :=
  fun k => toField L a u k
    - (κ : ℂ) * convC (toField L a v) (convC (toField L a r) (toField L a r)) k

/-- The algebra product in coefficients: `toField (v · (r · r)) = convC(toField v, convC(c, c))`. -/
theorem toField_mulBil_eq {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) (v r : Ell2) :
    toField L a (mulBil hL ha v (mulBil hL ha r r))
      = convC (toField L a v) (convC (toField L a r) (toField L a r)) := by
  simp only [mulBil_apply, toField_mulEll]

/-- Coefficient relation `c_k · i(freq_k - z) = d_k` for a fixed point, every `k`. -/
theorem coef_relation {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) {z : ℂ} (hz : 0 < z.im) (κ : ℝ)
    {u v r : Ell2} (hr : riccatiT hL ha hz κ u v r = r) (k : ℤ) :
    toField L a r k * (Complex.I * (((freq L k : ℝ) : ℂ) - z)) = rhsD L a κ u v r k := by
  have hD := ne_zero_I_mul L z hz k
  have hP := pw_ne_zero L a k
  have h := fixed_coord hL ha hz κ hr k
  have hW := congrFun (toField_mulBil_eq hL ha v r) k
  unfold rhsD
  rw [← hW]
  unfold toField
  rw [div_mul_eq_mul_div, h]
  ring

/-- The ODE-coefficient form `(2πik/L) c_k = i z c_k + d_k`, the hypothesis of
`RiccatiPointwise.series_hasDerivAt`. -/
theorem hrec_of_fixed {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) {z : ℂ} (hz : 0 < z.im) (κ : ℝ)
    {u v r : Ell2} (hr : riccatiT hL ha hz κ u v r = r) (k : ℤ) :
    (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) / (L : ℂ)) * toField L a r k
      = Complex.I * z * toField L a r k + rhsD L a κ u v r k := by
  have h := coef_relation hL ha hz κ hr k
  have hf : ((freq L k : ℝ) : ℂ) = 2 * (Real.pi : ℂ) * (k : ℂ) / (L : ℂ) := by
    unfold freq
    push_cast
    ring
  rw [hf] at h
  linear_combination h

/-- `ℓ¹` summability of the Fourier coefficients of a point of the `H^a` model, `a > 1/2`. -/
theorem summable_norm_toField {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) (x : Ell2) :
    Summable (fun k => ‖toField L a x k‖) :=
  l1_summable hL ha (hsq_summable_eq (hsq_toField_ne_top L a x)).1

/-- `ℓ¹` summability of `d = toField u - κ convC(toField v, convC(c, c))`, `a > 1/2`. -/
theorem summable_norm_rhsD {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) (κ : ℝ) (u v r : Ell2) :
    Summable (fun k => ‖rhsD L a κ u v r k‖) := by
  have hW := summable_norm_toField hL ha (mulBil hL ha v (mulBil hL ha r r))
  have hU := summable_norm_toField hL ha u
  have hb : Summable (fun k => ‖toField L a u k‖
      + ‖(κ : ℂ)‖ * ‖toField L a (mulBil hL ha v (mulBil hL ha r r)) k‖) :=
    hU.add (hW.mul_left _)
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) hb
  have e : rhsD L a κ u v r k
      = toField L a u k - (κ : ℂ) * toField L a (mulBil hL ha v (mulBil hL ha r r)) k := by
    unfold rhsD
    rw [toField_mulBil_eq hL ha v r]
  rw [e]
  exact (norm_sub_le _ _).trans (le_of_eq (by rw [norm_mul]))

/-- **C2 statement for a fixed point.** For `r` with `riccatiT u v r = r` and `a > 1/2`:
the coefficients `c = toField r` and `d = rhsD` are `ℓ¹`, satisfy the coefficient relation, and
satisfy the ODE-coefficient relation `(2πik/L) c_k = i z c_k + d_k`. -/
theorem pointwise_coef {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) {z : ℂ} (hz : 0 < z.im) (κ : ℝ)
    {u v r : Ell2} (hr : riccatiT hL ha hz κ u v r = r) :
    Summable (fun k => ‖toField L a r k‖) ∧
    Summable (fun k => ‖rhsD L a κ u v r k‖) ∧
    (∀ k : ℤ, toField L a r k * (Complex.I * (((freq L k : ℝ) : ℂ) - z))
      = rhsD L a κ u v r k) ∧
    (∀ k : ℤ, (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) / (L : ℂ)) * toField L a r k
      = Complex.I * z * toField L a r k + rhsD L a κ u v r k) :=
  ⟨summable_norm_toField hL ha r, summable_norm_rhsD hL ha κ u v r,
    fun k => coef_relation hL ha hz κ hr k, fun k => hrec_of_fixed hL ha hz κ hr k⟩

/-- **C2 from the Picard ball.** Under the smallness hypotheses of `riccatiT_fixed_exists_unique`,
there is a fixed point `r` with `‖r‖ ≤ 2β/Im z` whose coefficient data satisfy `pointwise_coef`. -/
theorem pointwise_coef_exists {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) {z : ℂ} (hz : 0 < z.im)
    (κ β : ℝ) (hβ : 0 < β) (hκ : 16 * |κ| * Cmul L a ^ 2 * β ^ 2 ≤ z.im ^ 2) (u v : Ell2)
    (hu : ‖u‖ ≤ β) (hv : ‖v‖ ≤ β) :
    ∃ r : Ell2, ‖r‖ ≤ 2 * β / z.im ∧
      Summable (fun k => ‖toField L a r k‖) ∧
      Summable (fun k => ‖rhsD L a κ u v r k‖) ∧
      (∀ k : ℤ, toField L a r k * (Complex.I * (((freq L k : ℝ) : ℂ) - z))
        = rhsD L a κ u v r k) ∧
      (∀ k : ℤ, (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) / (L : ℂ)) * toField L a r k
        = Complex.I * z * toField L a r k + rhsD L a κ u v r k) := by
  obtain ⟨r, hrn, hfix, -⟩ := riccatiT_fixed_exists_unique hL ha hz κ β hβ hκ u v hu hv
  obtain ⟨h1, h2, h3, h4⟩ := pointwise_coef hL ha hz κ hfix
  exact ⟨r, hrn, h1, h2, h3, h4⟩

end QuantumNLS.RiccatiPointwiseCoef

#print axioms QuantumNLS.RiccatiPointwiseCoef.toField_ropCLM_mul
#print axioms QuantumNLS.RiccatiPointwiseCoef.fixed_coord
#print axioms QuantumNLS.RiccatiPointwiseCoef.coef_relation
#print axioms QuantumNLS.RiccatiPointwiseCoef.hrec_of_fixed
#print axioms QuantumNLS.RiccatiPointwiseCoef.summable_norm_toField
#print axioms QuantumNLS.RiccatiPointwiseCoef.summable_norm_rhsD
#print axioms QuantumNLS.RiccatiPointwiseCoef.pointwise_coef
#print axioms QuantumNLS.RiccatiPointwiseCoef.pointwise_coef_exists
