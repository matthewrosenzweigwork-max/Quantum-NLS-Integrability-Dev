import Mathlib
import QuantumNLS.RiccatiSobolevBanach

/-!
# R-3FEAD88B stage E4-2: the absorption step `‖r − r_M‖ ≤ 2 η⁻¹ ‖E_M‖` and the sector form

Source (`riccati_expansion.tex`, proof lines 39-45): with `r_M = i ∑ w_n z^{-n}` and the residual `E_M`,
subtracting the two Riccati equations gives, for `d = r − r_M`,
`d = −R_z (E_M + κ v (r + r_M) d)`, `R_z = (∂x − i z)⁻¹`, `η = Im z`.
Absorption of the quadratic term with `‖R_z‖ ≤ η⁻¹` yields `‖d‖ ≤ C η⁻¹ ‖E_M‖`.

This module proves the abstract Banach-level step on the model `Ell2` (E3-pre), with the coupling `κ` a
real scalar. The coupling is the MODEL coupling: for the physical coupling `κ_phys` the source Fourier
convention (E3 addendum 1) gives `κ_model = κ_phys / L`. Everything here is for an arbitrary real `κ`.

Hypotheses are the source ones, made explicit:
* `‖v‖ ≤ β`, `‖r‖ ≤ ρ`, `‖r_M‖ ≤ ρ` (bounded parameter and solutions),
* `4 |κ| C² β ρ ≤ Im z` with `C = Cmul L a` (the smallness that replaces "η large"),
* `‖E‖ ≤ e` (the residual bound; its proof is the E4-3 charge recursion, NOT in this module).

Proved: `absorb_norm_le` (`‖d‖ ≤ 2 η⁻¹ e`), and `absorb_sector` (sector form: `η ≥ δ|z|` gives
`‖d‖ ≤ 2 (δ|z|)⁻¹ e`, the `|z|^{-1}` gain that the source turns into `|z|^{-M-1}` once `e ~ C|z|^{-M}`).
Standard axioms only. No sorry, admit, native_decide, or new axioms.
-/

set_option autoImplicit false
noncomputable section
open Complex

namespace QuantumNLS.RiccatiAbsorb

open QuantumNLS.RiccatiSobolevBanach

/-- Absorption step: if `d = −R_z (E + κ v (r + r_M) d)` with bounded data, then `‖d‖ ≤ 2 η⁻¹ e`. -/
theorem absorb_norm_le {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) {z : ℂ} (hz : 0 < z.im) (κ : ℝ)
    {v r rM E d : Ell2} {β ρ e : ℝ}
    (hv : ‖v‖ ≤ β) (hr : ‖r‖ ≤ ρ) (hrM : ‖rM‖ ≤ ρ) (hE : ‖E‖ ≤ e)
    (hκ : 4 * |κ| * Cmul L a ^ 2 * β * ρ ≤ z.im)
    (hd : d = -(ropCLM L z hz) (E + (κ : ℂ) • mulBil hL ha v (mulBil hL ha (r + rM) d))) :
    ‖d‖ ≤ 2 * z.im⁻¹ * e := by
  have hC : 0 ≤ Cmul L a := Real.sqrt_nonneg _
  have hβ : 0 ≤ β := le_trans (norm_nonneg v) hv
  have hρ : 0 ≤ ρ := le_trans (norm_nonneg r) hr
  have hη : 0 < z.im := hz
  have he0 : 0 ≤ e := le_trans (norm_nonneg E) hE
  have hs2 : ‖r + rM‖ ≤ 2 * ρ := by
    have := norm_add_le r rM
    linarith
  -- ‖(r + rM) d‖ ≤ C (2ρ) ‖d‖
  have hX : ‖mulBil hL ha (r + rM) d‖ ≤ Cmul L a * (2 * ρ) * ‖d‖ :=
    le_trans (norm_mulBil_le hL ha (r + rM) d)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs2 hC) (norm_nonneg _))
  -- ‖v ((r + rM) d)‖ ≤ C β (C (2ρ) ‖d‖)
  have hP : ‖mulBil hL ha v (mulBil hL ha (r + rM) d)‖
      ≤ Cmul L a * β * (Cmul L a * (2 * ρ) * ‖d‖) :=
    le_trans (norm_mulBil_le hL ha v (mulBil hL ha (r + rM) d))
      (mul_le_mul (mul_le_mul_of_nonneg_left hv hC) hX (norm_nonneg _) (mul_nonneg hC hβ))
  -- ‖d‖ = ‖R_z Y‖ with Y the absorbed right-hand side
  have h1 : ‖d‖ = ‖(ropCLM L z hz) (E + (κ : ℂ) • mulBil hL ha v (mulBil hL ha (r + rM) d))‖ := by
    calc ‖d‖ = ‖-(ropCLM L z hz) (E + (κ : ℂ) • mulBil hL ha v (mulBil hL ha (r + rM) d))‖ :=
          congrArg norm hd
      _ = _ := norm_neg _
  have h3 : ‖E + (κ : ℂ) • mulBil hL ha v (mulBil hL ha (r + rM) d)‖
      ≤ e + |κ| * (Cmul L a * β * (Cmul L a * (2 * ρ) * ‖d‖)) := by
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact add_le_add hE (mul_le_mul_of_nonneg_left hP (abs_nonneg κ))
  have h4 : ‖d‖ ≤ z.im⁻¹ * (e + |κ| * (Cmul L a * β * (Cmul L a * (2 * ρ) * ‖d‖))) :=
    h1.trans_le (le_trans (norm_ropCLM_le L z hz _) (mul_le_mul_of_nonneg_left h3 (inv_nonneg.2 hη.le)))
  -- the absorbed coefficient: η⁻¹ · 2|κ| C² β ρ ≤ 1/2
  have hA : z.im⁻¹ * (|κ| * (Cmul L a * β * (Cmul L a * (2 * ρ)))) ≤ 1 / 2 := by
    have e1 : z.im⁻¹ * (|κ| * (Cmul L a * β * (Cmul L a * (2 * ρ))))
        = z.im⁻¹ * (2 * (|κ| * Cmul L a ^ 2 * β * ρ)) := by ring
    have e2 : 2 * (|κ| * Cmul L a ^ 2 * β * ρ) ≤ z.im / 2 := by linarith
    have e3 : z.im⁻¹ * (2 * (|κ| * Cmul L a ^ 2 * β * ρ)) ≤ z.im⁻¹ * (z.im / 2) :=
      mul_le_mul_of_nonneg_left e2 (inv_nonneg.2 hη.le)
    have e4 : z.im⁻¹ * (z.im / 2) = 1 / 2 := by
      field_simp
    rw [e1]
    linarith
  have hsplit : z.im⁻¹ * (e + |κ| * (Cmul L a * β * (Cmul L a * (2 * ρ) * ‖d‖)))
      = z.im⁻¹ * e + (z.im⁻¹ * (|κ| * (Cmul L a * β * (Cmul L a * (2 * ρ))))) * ‖d‖ := by
    ring
  have hB : (z.im⁻¹ * (|κ| * (Cmul L a * β * (Cmul L a * (2 * ρ))))) * ‖d‖ ≤ 1 / 2 * ‖d‖ :=
    mul_le_mul_of_nonneg_right hA (norm_nonneg _)
  rw [hsplit] at h4
  linarith

/-- Sector form. With `η = Im z ≥ δ |z|` and `4|κ| C² β ρ ≤ δ |z|`, the same absorption gives
`‖d‖ ≤ 2 (δ|z|)⁻¹ e`. -/
theorem absorb_sector {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) {z : ℂ} (hz : 0 < z.im) (κ : ℝ)
    {v r rM E d : Ell2} {β ρ e δ : ℝ} (hδ : 0 < δ) (hsec : δ * ‖z‖ ≤ z.im)
    (hv : ‖v‖ ≤ β) (hr : ‖r‖ ≤ ρ) (hrM : ‖rM‖ ≤ ρ) (hE : ‖E‖ ≤ e)
    (hκ : 4 * |κ| * Cmul L a ^ 2 * β * ρ ≤ δ * ‖z‖)
    (hd : d = -(ropCLM L z hz) (E + (κ : ℂ) • mulBil hL ha v (mulBil hL ha (r + rM) d))) :
    ‖d‖ ≤ 2 * (δ * ‖z‖)⁻¹ * e := by
  have hzn : 0 < ‖z‖ := by
    have h := Complex.abs_im_le_norm z
    rw [abs_of_pos hz] at h
    exact lt_of_lt_of_le hz h
  have hpos : 0 < δ * ‖z‖ := mul_pos hδ hzn
  have hκ' : 4 * |κ| * Cmul L a ^ 2 * β * ρ ≤ z.im := le_trans hκ hsec
  have hE' : ‖d‖ ≤ 2 * z.im⁻¹ * e := absorb_norm_le hL ha hz κ hv hr hrM hE hκ' hd
  have hinv : z.im⁻¹ ≤ (δ * ‖z‖)⁻¹ := inv_anti₀ hpos hsec
  have he0 : 0 ≤ e := le_trans (norm_nonneg E) hE
  calc ‖d‖ ≤ 2 * z.im⁻¹ * e := hE'
    _ ≤ 2 * (δ * ‖z‖)⁻¹ * e :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hinv (by norm_num)) he0

end QuantumNLS.RiccatiAbsorb

#print axioms QuantumNLS.RiccatiAbsorb.absorb_norm_le
#print axioms QuantumNLS.RiccatiAbsorb.absorb_sector
