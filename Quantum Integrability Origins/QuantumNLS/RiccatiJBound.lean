import Mathlib
import QuantumNLS.RiccatiFloquet

/-!
# R-3FEAD88B item (c): bounds on the Floquet integral `J = ∫₀ᴸ conj(f) r` and the sector threshold

Pure bound layer, classical (continuous, pointwise) level:
1. `norm_J_le`: `|J| ≤ L · F · R` when `|f| ≤ F` and `|r| ≤ R` on `[0, L]`
   (the `B` of `RiccatiFloquet.tail_exp_bound`).
2. `tail_log_bound_J`: `|log(1 + exp(izL - 2κJ))| ≤ (3/2) exp(2|κ|B) exp(-Im z · L)` under
   the smallness `exp(2|κ|B) exp(-Im z · L) ≤ 1/2`.
3. `uniform_kappa_bound`: for `κ` in a compact `K ⊆ (0, ∞)` with `|κ| ≤ Kb`, the same tail bound
   holds with `Kb` in place of `|κ|`, uniformly in `κ ∈ K`.
4. `sector_smallness`: on the sector `|z| ≥ R ≥ R₀` and `Im z ≥ δ|z|`, with the explicit
   `R₀ = (2 Kb B + log 2) / (δ L)`, the smallness hypothesis of (2)-(3) holds.

What is NOT here: the link between the Ell2 / H^S remainder of `RiccatiRemainder.remainder_bound`
and the pointwise integral `J`. The `B` used here is an input supplied by the caller. No sorry,
admit, native_decide or custom axioms.
-/

namespace QuantumNLS.RiccatiJBound

open Complex Set

/-- Sup bound for the Floquet integral `J = ∫₀ᴸ conj(f) r` on `[0, L]`. -/
theorem norm_J_le {L : ℝ} (hL : 0 ≤ L) {f r : ℝ → ℂ} {F R : ℝ} (hF0 : 0 ≤ F)
    (hf : ∀ x ∈ Icc 0 L, ‖f x‖ ≤ F) (hr : ∀ x ∈ Icc 0 L, ‖r x‖ ≤ R) :
    ‖∫ s in (0 : ℝ)..L, (starRingEnd ℂ) (f s) * r s‖ ≤ L * (F * R) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := L) (f := fun s => (starRingEnd ℂ) (f s) * r s) (C := F * R)
    (by
      intro x hx
      rw [Set.uIoc_of_le hL] at hx
      have hx' : x ∈ Icc 0 L := ⟨hx.1.le, hx.2⟩
      rw [norm_mul, Complex.norm_conj]
      exact mul_le_mul (hf x hx') (hr x hx') (norm_nonneg _) hF0)
  rw [sub_zero, abs_of_nonneg hL] at h
  exact h.trans (le_of_eq (by ring))

/-- Tail bound: `|log(1 + exp(izL - 2κJ))| ≤ (3/2) exp(2|κ|B) exp(-Im z · L)` for `|J| ≤ B`. -/
theorem tail_log_bound_J {L κ : ℝ} {z J : ℂ} {B : ℝ} (hJ : ‖J‖ ≤ B)
    (hsmall : Real.exp (2 * |κ| * B) * Real.exp (-(z.im * L)) ≤ 1 / 2) :
    ‖Complex.log (1 + Complex.exp (Complex.I * z * (L : ℂ) - 2 * (κ : ℂ) * J))‖
      ≤ (3 / 2) * (Real.exp (2 * |κ| * B) * Real.exp (-(z.im * L))) :=
  QuantumNLS.RiccatiFloquet.tail_log_bound L κ z J B hJ hsmall

/-- Uniform in `κ`: for `|κ| ≤ Kb` (with `Kb` a bound on a compact `K ⊆ (0,∞)`), the tail bound holds
with the common constant `Kb`. -/
theorem uniform_kappa_bound {L κ Kb : ℝ} {z J : ℂ} {B : ℝ} (hJ : ‖J‖ ≤ B)
    (hκ : |κ| ≤ Kb) (hB : 0 ≤ B)
    (hsmall : Real.exp (2 * Kb * B) * Real.exp (-(z.im * L)) ≤ 1 / 2) :
    ‖Complex.log (1 + Complex.exp (Complex.I * z * (L : ℂ) - 2 * (κ : ℂ) * J))‖
      ≤ (3 / 2) * (Real.exp (2 * Kb * B) * Real.exp (-(z.im * L))) := by
  have hmono : Real.exp (2 * |κ| * B) ≤ Real.exp (2 * Kb * B) :=
    Real.exp_le_exp.2 (by nlinarith [hκ, hB])
  have hsmall' : Real.exp (2 * |κ| * B) * Real.exp (-(z.im * L)) ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_right hmono (Real.exp_pos _).le).trans hsmall
  refine (tail_log_bound_J hJ hsmall').trans ?_
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hmono (Real.exp_pos _).le) (by norm_num)

/-- Sector smallness: if `|z| ≥ R ≥ R₀ = (2 Kb B + log 2)/(δ L)` and `Im z ≥ δ |z|`, then
`exp(2 Kb B) exp(-Im z · L) ≤ 1/2`. -/
theorem sector_smallness {L δ Kb B R : ℝ} {z : ℂ} (hL : 0 < L) (hδ : 0 < δ)
    (hR : (2 * Kb * B + Real.log 2) / (δ * L) ≤ R) (hzR : R ≤ ‖z‖)
    (hsec : δ * ‖z‖ ≤ z.im) :
    Real.exp (2 * Kb * B) * Real.exp (-(z.im * L)) ≤ 1 / 2 := by
  have hRpos : 0 < δ * L := mul_pos hδ hL
  have h1 : 2 * Kb * B + Real.log 2 ≤ δ * R * L := by
    have : (2 * Kb * B + Real.log 2) / (δ * L) * (δ * L) ≤ R * (δ * L) :=
      mul_le_mul_of_nonneg_right hR hRpos.le
    rw [div_mul_cancel₀ _ hRpos.ne'] at this
    nlinarith [this]
  have h2 : δ * R ≤ z.im := le_trans (mul_le_mul_of_nonneg_left hzR hδ.le) hsec
  have h3 : 2 * Kb * B + Real.log 2 ≤ z.im * L := by
    have : δ * R * L ≤ z.im * L := mul_le_mul_of_nonneg_right h2 hL.le
    linarith
  rw [← Real.exp_add]
  have h4 : 2 * Kb * B + -(z.im * L) ≤ -Real.log 2 := by linarith
  calc Real.exp (2 * Kb * B + -(z.im * L)) ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.2 h4
    _ = 1 / 2 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      norm_num

end QuantumNLS.RiccatiJBound

#print axioms QuantumNLS.RiccatiJBound.norm_J_le
#print axioms QuantumNLS.RiccatiJBound.tail_log_bound_J
#print axioms QuantumNLS.RiccatiJBound.uniform_kappa_bound
#print axioms QuantumNLS.RiccatiJBound.sector_smallness
