import Mathlib
import QuantumNLS.RiccatiUniformK

/-!
# R-3FEAD88B assembly, arithmetic layer: the sector radius `R`

Given the uniform constant `k` (with `|κ| ≤ k` on a compact `K`), an expansion radius `B`, `βu`,
`δ > 0` and `L > 0`, the module:

* `exists_R`: chooses `R > 0` with `1 ≤ Rδ`, `9 ≤ R(Lδ)`, `16 k L pK² B² ≤ Rδ`,
  `16 (k/L) Cmul² βu² ≤ Rδ`, `remR (k/L) B δ ≤ R` and `logR k B δ ≤ R`;
* `sector_facts`: for `R ≤ ‖z‖` and `δ‖z‖ ≤ Im z`, the hypotheses of the frozen
  `trace_near_one_bound`, `value_remainder` and `log_value` hold for every `κ` with `0 < κ`, `|κ| ≤ k`.

Standard axioms only. No sorry, admit, native_decide, or new axioms.
-/

set_option autoImplicit false
noncomputable section
open Set

namespace QuantumNLS.RiccatiSectorBounds

open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiExpansions QuantumNLS.RiccatiUniformK

/-- From `|x / c| ≤ R` with `c > 0` get `x ≤ R c`. -/
theorem aux_div (x c R : ℝ) (hc : 0 < c) (h : |x / c| ≤ R) : x ≤ R * c :=
  (div_le_iff₀ hc).mp ((le_abs_self _).trans h)

/-- Existence of the uniform sector radius `R`. -/
theorem exists_R (L a S δ k B βu : ℝ) (M : ℕ) (hL : 0 < L) (hδ : 0 < δ) :
    ∃ R : ℝ, 0 < R ∧ 1 ≤ R * δ ∧ 9 ≤ R * (L * δ)
      ∧ 16 * k * L * (physK L a) ^ 2 * B ^ 2 ≤ R * δ
      ∧ 16 * (k / L) * Cmul L a ^ 2 * βu ^ 2 ≤ R * δ
      ∧ remR L a S M (k / L) B δ ≤ R ∧ logR L a S M k B δ ≤ R := by
  refine ⟨1 + |remR L a S M (k / L) B δ| + |logR L a S M k B δ| + |9 / (L * δ)|
      + |16 * k * L * (physK L a) ^ 2 * B ^ 2 / δ|
      + |16 * (k / L) * Cmul L a ^ 2 * βu ^ 2 / δ| + |1 / δ|, ?_⟩
  have h1 := abs_nonneg (remR L a S M (k / L) B δ)
  have h2 := abs_nonneg (logR L a S M k B δ)
  have h3 := abs_nonneg (9 / (L * δ))
  have h4 := abs_nonneg (16 * k * L * (physK L a) ^ 2 * B ^ 2 / δ)
  have h5 := abs_nonneg (16 * (k / L) * Cmul L a ^ 2 * βu ^ 2 / δ)
  have h6 := abs_nonneg (1 / δ)
  refine ⟨by linarith, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact aux_div 1 δ _ hδ (by linarith [le_abs_self (1 / δ)])
  · exact aux_div 9 (L * δ) _ (mul_pos hL hδ) (by linarith [le_abs_self (9 / (L * δ))])
  · exact aux_div _ δ _ hδ (by linarith [le_abs_self (16 * k * L * (physK L a) ^ 2 * B ^ 2 / δ)])
  · exact aux_div _ δ _ hδ (by linarith [le_abs_self (16 * (k / L) * Cmul L a ^ 2 * βu ^ 2 / δ)])
  · linarith [le_abs_self (remR L a S M (k / L) B δ)]
  · linarith [le_abs_self (logR L a S M k B δ)]

/-- The sector facts for one `κ ∈ (0, k]` and one `z` in the sector of radius `R`. -/
theorem sector_facts (L a S δ k B βu R κ : ℝ) (M : ℕ) (z : ℂ) (hL : 0 < L) (ha : 1 / 2 < a)
    (hδ : 0 < δ) (hk : 0 < k) (hκ0 : 0 < κ) (hκk : |κ| ≤ k) (hB : 0 < B)
    (h1 : 1 ≤ R * δ) (h9 : 9 ≤ R * (L * δ))
    (hJ' : 16 * k * L * (physK L a) ^ 2 * B ^ 2 ≤ R * δ)
    (hX : 16 * (k / L) * Cmul L a ^ 2 * βu ^ 2 ≤ R * δ)
    (hrem : remR L a S M (k / L) B δ ≤ R) (hlog : logR L a S M k B δ ≤ R)
    (hRz : R ≤ ‖z‖) (hsec : δ * ‖z‖ ≤ z.im) :
    0 < z.im ∧ 8 + 1 / 4 ≤ L * z.im
      ∧ 16 * |κ / L| * Cmul L a ^ 2 * βu ^ 2 ≤ z.im ^ 2
      ∧ κ * (L * ((physK L a * B) * (physK L a * (2 * B / z.im)))) ≤ 1 / 8
      ∧ remR L a S M (κ / L) B δ ≤ ‖z‖ ∧ logR L a S M κ B δ ≤ ‖z‖ := by
  have hL0 : 0 ≤ L := hL.le
  have hδR : δ * R ≤ z.im := ((mul_le_mul_of_nonneg_left hRz hδ.le)).trans hsec
  have hcomm : δ * R = R * δ := mul_comm _ _
  have him1 : 1 ≤ z.im := by linarith
  have him : 0 < z.im := by linarith
  have hκk' : κ ≤ k := le_trans (le_abs_self κ) hκk
  have hab : |κ / L| ≤ k / L := by
    rw [abs_div, abs_of_pos hL]
    exact div_le_div_of_nonneg_right hκk hL0
  have hab' : |κ / L| ≤ |k / L| := by
    rw [abs_of_pos (div_pos hk hL)]
    exact hab
  refine ⟨him, ?_, ?_, ?_, ?_, ?_⟩
  · have e1 := mul_le_mul_of_nonneg_left hδR hL0
    have e2 : L * (δ * R) = R * (L * δ) := by ring
    linarith
  · have hc : 0 ≤ Cmul L a ^ 2 * βu ^ 2 := by positivity
    have hA : 16 * |κ / L| * Cmul L a ^ 2 * βu ^ 2 ≤ 16 * (k / L) * Cmul L a ^ 2 * βu ^ 2 := by
      gcongr
    have hB2 : z.im ≤ z.im ^ 2 := by nlinarith
    linarith
  · have hY1 : 16 * κ * L * (physK L a) ^ 2 * B ^ 2 ≤ 16 * k * L * (physK L a) ^ 2 * B ^ 2 := by
      gcongr
    have hY : 16 * κ * L * (physK L a) ^ 2 * B ^ 2 ≤ z.im := by linarith
    have e : κ * (L * ((physK L a * B) * (physK L a * (2 * B / z.im))))
        = (2 * κ * L * (physK L a) ^ 2 * B ^ 2) * (z.im)⁻¹ := by ring
    rw [e, ← div_eq_mul_inv, div_le_iff₀ him]
    linarith
  · exact (remR_mono L a S M (κ / L) (k / L) B δ hB.le hδ hab').trans (hrem.trans hRz)
  · have ha0 : 0 ≤ a := by linarith
    have habs : |κ| ≤ |k| := by rw [abs_of_pos hk]; exact hκk
    exact (logR_mono L a S M κ k B δ ha0 hL hB.le hδ habs).trans (hlog.trans hRz)

end QuantumNLS.RiccatiSectorBounds
