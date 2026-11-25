import Mathlib
import QuantumNLS.StrongLimitBulk
import QuantumNLS.QuantileTransport

/-!
# CC:F04:deterministic-gap (R-C455C541), step 4: quadratic Wasserstein convergence gives strong `L²` convergence of the step quantiles

Source: `F04.tex` line 315: "assume in addition that the endpoint empirical measures converge to `μ` in quadratic Wasserstein distance ...
`W₂(μ_N(s), μ_N(1)) ≤ N^{-1/2} ‖q_N(s) − q_N(1)‖_{ℓ²} ≤ 2π(a−b)/(L√N)`. Hence the empirical quantiles tend to `Q` in `L²`,
uniformly in `s`."  Uses `QuantileTransport.W2_eq_eLpNorm_quantile_of_prob` (`F05:quantile-formula`).

* `step_quantile_ae`: the quantile of the empirical measure of an ordered array is its step function a.e.;
* `norm_step_sub_Q2`: `‖stepL2 q − Q‖_{L²(0,1)} = W₂(empirical q, μ)`;
* `l2_shift_le`: `‖stepL2 q − stepL2 q'‖ ≤ N^{-1/2} Σ_j |q_j − q'_j|`;
* `quantile_conv_of_W2`: if `W₂(μ_N(0), μ) → 0` and `Σ_j |q_j(s_N) − q_j(0)| ≤ C` then `‖stepL2 q(s_N) − Q‖ → 0`.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

noncomputable section
open MeasureTheory Filter Topology Set Finset
open scoped ENNReal NNReal BigOperators

namespace QuantumNLS.DetGapW2

open QuantumNLS.StepIntegrals (stepL2 stepF stepL2_ae idx ext ext_fin norm_sq_step stepL2_sub)
open QuantumNLS.BulkResponseForm (L2Unit BulkResponseData)
open QuantumNLS.QuantileForm (uI quantile_ae_qm)
open QuantumNLS.QuantileTransport (qm quantile empirical W2 quantile_empirical Ioo_ae_eq_iUnion
  isProbabilityMeasure_empirical W2_eq_eLpNorm_quantile_of_prob)
open QuantumNLS.StrongLimitBulk (Q2)
open QuantumNLS.FiniteResponse (L2N)

theorem step_quantile_ae {N : ℕ} (hN : 0 < N) {x : Fin N → ℝ} (hx : Monotone x) :
    quantile (empirical N x) =ᵐ[uI] stepF N x := by
  have h := Ioo_ae_eq_iUnion hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  refine (ae_restrict_iff' measurableSet_Ioo).2 ?_
  filter_upwards [h.mem_iff] with s hs hs01
  obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hs.1 hs01)
  rw [quantile_empirical hN hx j hj]
  unfold stepF
  have hid : idx N s = (j : ℕ) := by
    unfold idx
    rw [Nat.floor_eq_iff (by have := hs01.1; positivity)]
    have h1 := hj.1
    have h2 := hj.2
    rw [div_lt_iff₀ hNr] at h1
    rw [lt_div_iff₀ hNr] at h2
    constructor <;> nlinarith
  rw [hid, ext_fin]

theorem norm_step_sub_Q2 (D : BulkResponseData) {N : ℕ} (hN : 0 < N) {x : Fin N → ℝ}
    (hx : Monotone x) :
    ‖stepL2 x - Q2 D‖ = (W2 (empirical N x) D.μ).toReal := by
  haveI := D.hμ.isProbability
  haveI := isProbabilityMeasure_empirical hN x
  rw [W2_eq_eLpNorm_quantile_of_prob, Lp.norm_def]
  congr 1
  refine eLpNorm_congr_ae ?_
  filter_upwards [Lp.coeFn_sub (stepL2 x) (Q2 D), stepL2_ae x,
    MemLp.coeFn_toLp (QuantumNLS.StrongLimitBulk.memLp_qm_bulk D), step_quantile_ae hN hx,
    quantile_ae_qm D.μ] with s h1 h2 h3 h4 h5
  rw [h1, Pi.sub_apply, h2]
  simp only [Q2] at h3 ⊢
  rw [h3, h4, ← h5]

theorem l2_shift_le {n : ℕ} (q q' : Fin (n + 1) → ℝ) :
    ‖stepL2 q - stepL2 q'‖ ≤ (1 / Real.sqrt ((n : ℝ) + 1)) * ∑ j, |q j - q' j| := by
  have hN : 0 < n + 1 := Nat.succ_pos n
  rw [← stepL2_sub]
  have h := norm_sq_step hN (q - q')
  have hNr : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hs : ∑ j, (q - q') j ^ 2 ≤ (∑ j, |q j - q' j|) ^ 2 := by
    have : ∀ j, (q - q') j ^ 2 = |q j - q' j| ^ 2 := fun j => by simp [sq_abs]
    simp_rw [this]
    exact Finset.sum_sq_le_sq_sum_of_nonneg (f := fun j => |q j - q' j|) (fun j _ => abs_nonneg _)
  have hS : 0 ≤ ∑ j, |q j - q' j| := Finset.sum_nonneg fun j _ => abs_nonneg _
  have h2 : ‖stepL2 (q - q')‖ ^ 2 ≤ ((1 / Real.sqrt ((n : ℝ) + 1)) * ∑ j, |q j - q' j|) ^ 2 := by
    rw [h, mul_pow, div_pow, Real.sq_sqrt hNr.le, one_pow]
    unfold L2N
    push_cast
    calc 1 / ((n : ℝ) + 1) * ∑ j, (q - q') j ^ 2 ≤ 1 / ((n : ℝ) + 1) * (∑ j, |q j - q' j|) ^ 2 :=
          mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).1 h2

theorem quantile_conv_of_W2 (D : BulkResponseData) {q0 q : ∀ n : ℕ, Fin (n + 1) → ℝ} {C : ℝ}
    (hq0 : ∀ n, Monotone (q0 n))
    (hW : Tendsto (fun n : ℕ => W2 (empirical (n + 1) (q0 n)) D.μ) atTop (𝓝 0))
    (hC : ∀ n, ∑ j, |q n j - q0 n j| ≤ C) :
    Tendsto (fun n : ℕ => ‖stepL2 (q n) - Q2 D‖) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => ‖stepL2 (q0 n) - Q2 D‖) atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hW
    simp only [ENNReal.toReal_zero] at h
    refine h.congr fun n => ?_
    exact (norm_step_sub_Q2 D (Nat.succ_pos n) (hq0 n)).symm
  have h2 : Tendsto (fun n : ℕ => (1 / Real.sqrt ((n : ℝ) + 1)) * C) atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ => Real.sqrt ((n : ℝ) + 1)) atTop atTop := by
      refine Real.tendsto_sqrt_atTop.comp ?_
      exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    simpa using (this.inv_tendsto_atTop).mul_const C
  have h3 : Tendsto (fun n : ℕ => (1 / Real.sqrt ((n : ℝ) + 1)) * C + ‖stepL2 (q0 n) - Q2 D‖) atTop
      (𝓝 0) := by
    have := h2.add h1
    rwa [add_zero] at this
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h3
  calc ‖stepL2 (q n) - Q2 D‖ = ‖(stepL2 (q n) - stepL2 (q0 n)) + (stepL2 (q0 n) - Q2 D)‖ := by
        congr 1; abel
    _ ≤ ‖stepL2 (q n) - stepL2 (q0 n)‖ + ‖stepL2 (q0 n) - Q2 D‖ := norm_add_le _ _
    _ ≤ (1 / Real.sqrt ((n : ℝ) + 1)) * C + ‖stepL2 (q0 n) - Q2 D‖ := by
        refine add_le_add ?_ le_rfl
        refine (l2_shift_le (q n) (q0 n)).trans ?_
        exact mul_le_mul_of_nonneg_left (hC n) (by positivity)

end QuantumNLS.DetGapW2

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.DetGapW2.step_quantile_ae
#print axioms QuantumNLS.DetGapW2.norm_step_sub_Q2
#print axioms QuantumNLS.DetGapW2.l2_shift_le
#print axioms QuantumNLS.DetGapW2.quantile_conv_of_W2
