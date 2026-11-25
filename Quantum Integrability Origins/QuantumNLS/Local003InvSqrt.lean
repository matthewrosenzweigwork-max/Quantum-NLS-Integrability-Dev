import Mathlib
import QuantumNLS.LocalSpectralReduced

/-! LOCAL-003 `thm:reset-uniform-reduction` (spectral_reduction.tex:87-110), stage M1:
the inverse square root series satisfies `C^{-1/2} C C^{-1/2} = 1`.

Source (definition before the theorem): "The inverse square root is defined by its power series about the identity.
... Thus `U_n^* U_n = 1`".  The identity `(∑ binom(-1/2,k) x^k)^2 (1+x) = 1` is proved first as an identity of
formal power series over `ℝ` (derivative argument: `(1+X) F' = -F/2`, hence `d((1+X)F^2) = 0`), and then transported
to the Banach algebra `ℂ² →L ℂ²` by the Cauchy product of absolutely summable series (`‖T - 1‖ < 1`). -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open Finset
namespace QuantumNLS.Local003InvSqrt
open QuantumNLS.LocalSpectral PowerSeries

/-- The formal series with coefficients `binom(-1/2,k)`. -/
def Fs : PowerSeries ℝ := PowerSeries.mk invSqrtCoeff

lemma deriv_rel : (1 + X) * d⁄dX Fs = C (-(1 / 2 : ℝ)) * Fs := by
  ext k
  rw [add_mul, one_mul, map_add, coeff_derivative, coeff_C_mul]
  simp only [Fs, coeff_mk]
  rcases k with _ | k
  · have := invSqrtCoeff_succ 0
    simp only [invSqrtCoeff] at this ⊢
    simp
  · rw [coeff_succ_X_mul, coeff_derivative]
    simp only [Fs, coeff_mk]
    rw [invSqrtCoeff_succ (k + 1), invSqrtCoeff_succ k]
    push_cast
    have h1 : ((k : ℝ) + 1) ≠ 0 := by positivity
    have h2 : ((k : ℝ) + 1 + 1) ≠ 0 := by positivity
    field_simp
    ring

lemma sq_rel : (1 + X) * (Fs * Fs) = 1 := by
  apply derivative.ext
  · have h := deriv_rel
    have hX : d⁄dX (1 + X : PowerSeries ℝ) = 1 := by
      rw [map_add, derivative_one, derivative_X, zero_add]
    have hC : (2 : PowerSeries ℝ) * C (-(1 / 2 : ℝ)) = -1 := by
      have h2 : (2 : PowerSeries ℝ) = C (2 : ℝ) := (map_ofNat C 2).symm
      rw [h2, ← map_mul, show (2 : ℝ) * -(1 / 2) = -1 by norm_num, map_neg, map_one]
    rw [Derivation.leibniz, Derivation.leibniz, hX, derivative_one]
    simp only [smul_eq_mul]
    linear_combination (2 * Fs) * h + (Fs * Fs) * hC
  · have h0 : constantCoeff Fs = 1 := by
      rw [← coeff_zero_eq_constantCoeff_apply]; simp [Fs, invSqrtCoeff]
    simp [h0]

lemma sq_coeff (k : ℕ) : coeff k (Fs * Fs) = (-1 : ℝ) ^ k := by
  have h := sq_rel
  induction k with
  | zero =>
    have := congrArg (coeff 0) h
    simpa using this
  | succ k ih =>
    have := congrArg (coeff (k + 1)) h
    rw [add_mul, one_mul, map_add, coeff_succ_X_mul] at this
    simp only [coeff_one, Nat.succ_ne_zero, ite_false] at this
    rw [pow_succ]
    linarith

lemma sq_coeff_sum (k : ℕ) :
    ∑ ij ∈ antidiagonal k, invSqrtCoeff ij.1 * invSqrtCoeff ij.2 = (-1 : ℝ) ^ k := by
  have := sq_coeff k
  rw [coeff_mul] at this
  simpa [Fs] using this

variable {T : E2 →L[ℂ] E2}

lemma summable_norm_invSqrtM (h : ‖T - 1‖ < 1) :
    Summable fun k : ℕ => ‖(invSqrtCoeff k : ℂ) • (T - 1) ^ k‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
    (summable_geometric_of_lt_one (norm_nonneg _) h)
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  calc |invSqrtCoeff k| * ‖(T - 1) ^ k‖ ≤ 1 * ‖T - 1‖ ^ k :=
        mul_le_mul (abs_invSqrtCoeff_le k) (norm_pow_le _ _) (norm_nonneg _) zero_le_one
    _ = ‖T - 1‖ ^ k := one_mul _

/-- `(C^{-1/2})² = ∑ (1 - C)^k = C⁻¹`, as the series `∑ (-(C-1))^k`. -/
lemma invSqrtM_sq (h : ‖T - 1‖ < 1) :
    invSqrtM T * invSqrtM T = ∑' k : ℕ, (-(T - 1)) ^ k := by
  have hn := summable_norm_invSqrtM h
  unfold invSqrtM
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hn hn]
  congr 1
  ext1 n
  have e : ∀ ij ∈ antidiagonal n, ((invSqrtCoeff ij.1 : ℂ) • (T - 1) ^ ij.1) *
      ((invSqrtCoeff ij.2 : ℂ) • (T - 1) ^ ij.2) =
        ((invSqrtCoeff ij.1 * invSqrtCoeff ij.2 : ℝ) : ℂ) • (T - 1) ^ n := by
    intro ij hij
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
    rw [smul_mul_smul_comm, ← pow_add, hij]
    push_cast; rfl
  rw [Finset.sum_congr rfl e, ← Finset.sum_smul, ← Complex.ofReal_sum, sq_coeff_sum]
  have hneg : -(T - 1) = (-1 : ℂ) • (T - 1) := (neg_one_smul ℂ _).symm
  rw [hneg, smul_pow]
  push_cast
  rfl

lemma invSqrtM_sq_mul (h : ‖T - 1‖ < 1) : (invSqrtM T * invSqrtM T) * T = 1 := by
  rw [invSqrtM_sq h]
  have hn : ‖-(T - 1)‖ < 1 := by rwa [norm_neg]
  have := geom_series_mul_neg (-(T - 1)) hn
  rw [show (1 : E2 →L[ℂ] E2) - -(T - 1) = T by abel] at this
  exact this

lemma invSqrtM_commute (h : ‖T - 1‖ < 1) : Commute (invSqrtM T) T := by
  unfold invSqrtM
  refine Commute.tsum_left _ fun i => ?_
  refine Commute.smul_left ?_ _
  have : T = (T - 1) + 1 := by abel
  conv_rhs => rw [this]
  exact ((Commute.refl (T - 1)).pow_left i).add_right (Commute.one_right _)

/-- **`C^{-1/2} C C^{-1/2} = 1`.** -/
theorem invSqrtM_mul_mul (h : ‖T - 1‖ < 1) : invSqrtM T * T * invSqrtM T = 1 := by
  have hc := invSqrtM_commute h
  calc invSqrtM T * T * invSqrtM T = invSqrtM T * (T * invSqrtM T) := mul_assoc _ _ _
    _ = invSqrtM T * (invSqrtM T * T) := by rw [← hc.eq]
    _ = (invSqrtM T * invSqrtM T) * T := (mul_assoc _ _ _).symm
    _ = 1 := invSqrtM_sq_mul h

end QuantumNLS.Local003InvSqrt
#print axioms QuantumNLS.Local003InvSqrt.invSqrtM_sq_mul
#print axioms QuantumNLS.Local003InvSqrt.invSqrtM_mul_mul
