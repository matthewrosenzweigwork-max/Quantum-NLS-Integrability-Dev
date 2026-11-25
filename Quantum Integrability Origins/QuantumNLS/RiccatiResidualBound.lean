import Mathlib
import QuantumNLS.RiccatiCharges

/-!
# R-3FEAD88B stage E4-3b: the residual bound `‖E_M‖ ≤ C |z|^{-M}` from uniform charge bounds

Source (`riccati_expansion.tex`, lines 38): `‖E_M‖_{H^a} ≤ C|z|^{-M}` follows from the residual identity and bounds on
the differential polynomials `w_n`. Stage E4-3a (`RiccatiCharges`) proves the identity
`E_M = (i ζ^M) • D w_M − κ • m v (T_M)`, `ζ = z⁻¹`, `T_M = ∑_{b,d≤M} [M ≤ b+d] ζ^{b+d} • m (w b) (w d)`.

The charges `w_n` do not depend on `z`. So the constants `K ≥ ‖w_n‖` (`1 ≤ n ≤ M`) and `KD ≥ ‖D w_M‖` are uniform in `z`,
and the power of `ζ` in each term is the only `z`-dependence. This module proves, for `‖ζ‖ ≤ 1` (i.e. `|z| ≥ 1`):

  `‖E_M‖ ≤ ‖ζ‖^M · (KD + ‖κ‖ · C‖v‖ · M² · C K²)`,

with `C` the bilinear product bound `‖m x y‖ ≤ C‖x‖‖y‖`.

HYPOTHESES (explicit, NOT proved here):
* `hm`: the product is bounded (in the model: `Cmul L a`, from E3-pre);
* `hK`: `‖w_n‖ ≤ K` for `1 ≤ n ≤ M` (uniform in `z`; this is the E4-3c charge bound, which in the model needs the
  `H^S` induction with one derivative lost per step and `S ≥ a + M + 1`; NOT yet proved);
* `hKD`: `‖D w_M‖ ≤ KD` (model: `‖∂w_M‖_{H^a} ≤ ‖w_M‖_{H^{a+1}}` by E4-1, so `KD` is the `H^{a+1}` bound on `w_M`).

Standard axioms only. No sorry, admit, native_decide, or new axioms.
-/

set_option autoImplicit false
noncomputable section
open Complex Finset

namespace QuantumNLS.RiccatiResidualBound

open QuantumNLS.RiccatiCharges

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem norm_IZ_smul (ζ : ℂ) (M : ℕ) (x : X) :
    ‖(Complex.I * ζ ^ M) • x‖ = ‖ζ‖ ^ M * ‖x‖ := by
  rw [norm_smul, norm_mul, Complex.norm_I, one_mul, norm_pow]

/-- Uniform bound on the tail `T_M`: each term has modulus at most `‖ζ‖^M C K²` (when `‖ζ‖ ≤ 1`). -/
theorem norm_tailT_le (m : X →ₗ[ℂ] X →ₗ[ℂ] X) (ζ : ℂ) (w : ℕ → X) (M : ℕ) (C K : ℝ)
    (hζ : ‖ζ‖ ≤ 1) (hC : 0 ≤ C) (hK0 : 0 ≤ K)
    (hm : ∀ x y : X, ‖m x y‖ ≤ C * ‖x‖ * ‖y‖)
    (hK : ∀ n : ℕ, 1 ≤ n → n ≤ M → ‖w n‖ ≤ K) :
    ‖tailT m ζ w M‖ ≤ (M : ℝ) * ((M : ℝ) * (‖ζ‖ ^ M * (C * K ^ 2))) := by
  have hterm : ∀ b ∈ Icc 1 M, ∀ d ∈ Icc 1 M,
      ‖(if M ≤ b + d then (ζ ^ (b + d)) • m (w b) (w d) else 0)‖
        ≤ ‖ζ‖ ^ M * (C * K ^ 2) := by
    intro b hb d hd
    rw [Finset.mem_Icc] at hb hd
    split_ifs with h
    · rw [norm_smul, norm_pow]
      have h1 : ‖ζ‖ ^ (b + d) ≤ ‖ζ‖ ^ M := pow_le_pow_of_le_one (norm_nonneg _) hζ h
      have hwb : ‖w b‖ ≤ K := hK b hb.1 hb.2
      have hwd : ‖w d‖ ≤ K := hK d hd.1 hd.2
      have h2 : ‖m (w b) (w d)‖ ≤ C * (K * K) := by
        refine (hm (w b) (w d)).trans ?_
        have := mul_le_mul hwb hwd (norm_nonneg _) hK0
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left this hC
      have h3 : ‖ζ‖ ^ (b + d) * ‖m (w b) (w d)‖ ≤ ‖ζ‖ ^ M * (C * K ^ 2) := by
        have h4 : ‖ζ‖ ^ (b + d) * ‖m (w b) (w d)‖ ≤ ‖ζ‖ ^ M * (C * (K * K)) :=
          mul_le_mul h1 h2 (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)
        have h5 : ‖ζ‖ ^ M * (C * (K * K)) = ‖ζ‖ ^ M * (C * K ^ 2) := by ring
        linarith
      exact h3
    · simp only [norm_zero]
      exact mul_nonneg (pow_nonneg (norm_nonneg _) _) (mul_nonneg hC (pow_nonneg hK0 _))
  have hsplit : ‖tailT m ζ w M‖
      ≤ ∑ b ∈ Icc 1 M, ∑ d ∈ Icc 1 M, ‖ζ‖ ^ M * (C * K ^ 2) := by
    unfold tailT
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b hb => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d hd => ?_)
    exact hterm b hb d hd
  refine hsplit.trans (le_of_eq ?_)
  simp [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul] <;> ring

/-- Residual bound. For `‖ζ‖ ≤ 1` (`|z| ≥ 1`), `E_M` is `O(‖ζ‖^M)` with a constant independent of `z`. -/
theorem resid_norm_le (m : X →ₗ[ℂ] X →ₗ[ℂ] X) (D : X →ₗ[ℂ] X) (v u : X) (κ z ζ : ℂ) (w : ℕ → X)
    (C K KD : ℝ) (hzζ : z * ζ = 1) (hζ : ‖ζ‖ ≤ 1) (hC : 0 ≤ C)
    (hw1 : w 1 = u)
    (hrec : ∀ n : ℕ, 1 ≤ n → w (n + 1)
      = -(Complex.I • D (w n)) + κ • m v (∑ a ∈ Ico 1 n, m (w a) (w (n - a))))
    (hm : ∀ x y : X, ‖m x y‖ ≤ C * ‖x‖ * ‖y‖)
    (M : ℕ) (hM : 1 ≤ M)
    (hK : ∀ n : ℕ, 1 ≤ n → n ≤ M → ‖w n‖ ≤ K) (hKD : ‖D (w M)‖ ≤ KD) :
    ‖resid m D v u κ z ζ w M‖
      ≤ ‖ζ‖ ^ M * (KD + ‖κ‖ * (C * ‖v‖) * ((M : ℝ) * ((M : ℝ) * (C * K ^ 2)))) := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 1 le_rfl hM)
  have hres := resid_formula m D v u κ z ζ w hzζ hw1 hrec M hM
  rw [hres]
  have hT := norm_tailT_le m ζ w M C K hζ hC hK0 hm hK
  have hA : ‖(Complex.I * ζ ^ M) • D (w M)‖ ≤ ‖ζ‖ ^ M * KD := by
    rw [norm_IZ_smul]
    exact mul_le_mul_of_nonneg_left hKD (pow_nonneg (norm_nonneg _) _)
  have hB : ‖κ • m v (tailT m ζ w M)‖
      ≤ ‖κ‖ * (C * ‖v‖) * ((M : ℝ) * ((M : ℝ) * (‖ζ‖ ^ M * (C * K ^ 2)))) := by
    rw [norm_smul]
    have h1 : ‖m v (tailT m ζ w M)‖
        ≤ C * ‖v‖ * ‖tailT m ζ w M‖ := hm v _
    have h2 : ‖κ‖ * ‖m v (tailT m ζ w M)‖
        ≤ ‖κ‖ * (C * ‖v‖ * ‖tailT m ζ w M‖) :=
      mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    have h3 : C * ‖v‖ * ‖tailT m ζ w M‖
        ≤ C * ‖v‖ * ((M : ℝ) * ((M : ℝ) * (‖ζ‖ ^ M * (C * K ^ 2)))) :=
      mul_le_mul_of_nonneg_left hT (mul_nonneg hC (norm_nonneg _))
    calc ‖κ‖ * ‖m v (tailT m ζ w M)‖
        ≤ ‖κ‖ * (C * ‖v‖ * ((M : ℝ) * ((M : ℝ) * (‖ζ‖ ^ M * (C * K ^ 2))))) :=
          h2.trans (mul_le_mul_of_nonneg_left h3 (norm_nonneg _))
      _ = ‖κ‖ * (C * ‖v‖) * ((M : ℝ) * ((M : ℝ) * (‖ζ‖ ^ M * (C * K ^ 2)))) := by ring
  calc ‖(Complex.I * ζ ^ M) • D (w M) - κ • m v (tailT m ζ w M)‖
      ≤ ‖(Complex.I * ζ ^ M) • D (w M)‖
          + ‖κ • m v (tailT m ζ w M)‖ := norm_sub_le _ _
    _ ≤ ‖ζ‖ ^ M * KD + ‖κ‖ * (C * ‖v‖) * ((M : ℝ) * ((M : ℝ) * (‖ζ‖ ^ M * (C * K ^ 2)))) :=
          add_le_add hA hB
    _ = ‖ζ‖ ^ M * (KD + ‖κ‖ * (C * ‖v‖) * ((M : ℝ) * ((M : ℝ) * (C * K ^ 2)))) := by ring

end QuantumNLS.RiccatiResidualBound

#print axioms QuantumNLS.RiccatiResidualBound.norm_tailT_le
#print axioms QuantumNLS.RiccatiResidualBound.resid_norm_le
