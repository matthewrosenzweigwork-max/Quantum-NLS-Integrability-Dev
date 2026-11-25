import QuantumNLS.Local005MajorantB

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators ENNReal
namespace QuantumNLS.Local005
open QuantumNLS.ResetFreeResolventLOCAL001
open QuantumNLS.ResolventWordEstimateStage2LOCAL005

def baseConstant (L r κ : ℝ) : ℝ := 2 * Real.sqrt (κ / L) * (1 + gapSum L r)

theorem baseConstant_nonneg (L r κ : ℝ) : 0 ≤ baseConstant L r κ :=
  mul_nonneg (by positivity) (by linarith [gapSum_nonneg L r])

theorem envelope_even_bound {L r : ℝ} (hL : 0 < L) (hr : 0 < r)
    (hsmall : r < spacing L / 2) (κ : ℝ) {k : ℕ} (hk : 1 ≤ k)
    (u : Fin k → ℤ → ℂ) (hu : ∀ j, Summable fun m => ‖u j m‖ ^ 2) (n : ℤ) :
    envelope L r κ k u n ≤ baseConstant L r κ ^ k * ∏ j, inputL2Norm u j := by
  have hrow := (envelope_row hL hr hsmall κ u hu n).2
  have hurow := (row_input_data u hu n).2
  have hdc := degree_constant L r κ k hk
  have hprod : 0 ≤ ∏ j, inputL2Norm u j :=
    Finset.prod_nonneg fun j _ => Real.sqrt_nonneg _
  have hD : 0 ≤ ((2 * Real.sqrt (κ / L)) ^ k) ^ 2 * gapSum L r ^ (k - 1) :=
    mul_nonneg (sq_nonneg _) (pow_nonneg (gapSum_nonneg L r) _)
  have hb : envelope L r κ k u n ^ 2 ≤
      (baseConstant L r κ ^ k * ∏ j, inputL2Norm u j) ^ 2 := by
    calc
      _ ≤ _ := hrow
      _ ≤ ((2 * Real.sqrt (κ / L)) ^ k) ^ 2 * gapSum L r ^ (k - 1) *
          (∏ j, inputL2Norm u j) ^ 2 := mul_le_mul_of_nonneg_left hurow hD
      _ ≤ (baseConstant L r κ ^ k) ^ 2 * (∏ j, inputL2Norm u j) ^ 2 :=
        mul_le_mul_of_nonneg_right hdc (sq_nonneg _)
      _ = _ := (mul_pow _ _ _).symm
  exact (sq_le_sq₀ (envelope_nonneg L r κ k u n)
    (mul_nonneg (pow_nonneg (baseConstant_nonneg L r κ) _) hprod)).1 hb

theorem envelope_odd_bound {L r : ℝ} (hL : 0 < L) (hr : 0 < r)
    (hsmall : r < spacing L / 2) (κ : ℝ) {k : ℕ} (hk : 1 ≤ k) (hodd : Odd k)
    (u : Fin k → ℤ → ℂ) (hu : ∀ j, Summable fun m => ‖u j m‖ ^ 2) :
    Summable (fun n : ℤ => envelope L r κ k u n ^ 2) ∧
      ∑' n : ℤ, envelope L r κ k u n ^ 2 ≤
        (baseConstant L r κ ^ k * ∏ j, inputL2Norm u j) ^ 2 := by
  let D := ((2 * Real.sqrt (κ / L)) ^ k) ^ 2 * gapSum L r ^ (k - 1)
  have hD : 0 ≤ D := mul_nonneg (sq_nonneg _) (pow_nonneg (gapSum_nonneg L r) _)
  obtain ⟨hi, hile⟩ := odd_input_data hodd u hu
  have hrow : ∀ n : ℤ, envelope L r κ k u n ^ 2 ≤
      D * ∑' q : Fin (k - 1) → ℤ, amplitude u n q ^ 2 :=
    fun n => (envelope_row hL hr hsmall κ u hu n).2
  have hs : Summable (fun n : ℤ => envelope L r κ k u n ^ 2) :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hrow (hi.mul_left D)
  refine ⟨hs, ?_⟩
  calc
    _ ≤ ∑' n : ℤ, D * ∑' q : Fin (k - 1) → ℤ, amplitude u n q ^ 2 :=
      hs.tsum_le_tsum hrow (hi.mul_left D)
    _ = D * ∑' n : ℤ, ∑' q : Fin (k - 1) → ℤ, amplitude u n q ^ 2 := tsum_mul_left
    _ ≤ D * (∏ j, inputL2Norm u j) ^ 2 := mul_le_mul_of_nonneg_left hile hD
    _ ≤ (baseConstant L r κ ^ k) ^ 2 * (∏ j, inputL2Norm u j) ^ 2 :=
      mul_le_mul_of_nonneg_right (degree_constant L r κ k hk) (sq_nonneg _)
    _ = _ := (mul_pow _ _ _).symm

#print axioms envelope_even_bound
#print axioms envelope_odd_bound
end QuantumNLS.Local005
