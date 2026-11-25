import Mathlib
import QuantumNLS.VarResponse
import QuantumNLS.StrongLimitBulk
import QuantumNLS.GaudinResponse

/-!
# CC:F04:variable-coupling (R-C88B5D59), step 7: the strong bulk response limit at contact `κ_N/N`

Source: `F04.tex` line 412 (proof): "Thus any strongly convergent empirical quantiles give the same strong `L²` response limit at `κ_N` as at `κ`. Theorem CC:F03:deterministic applies to the same arrays `q`, since that theorem requires no Bethe equation at its fixed response coupling."

`resp_shift_le`: `‖stepL2 f' − stepL2 f‖ ≤ (m−1)/((2−m) L) ‖stepL2 q‖` (CC:F04:parameter-response-bound, from `VarResponse.param_response`, `m = max(c'/c, c/c') = 1 + ε`).
`strong_response_V`: if the step quantiles `stepL2 (q n) → Q` in `L²(0,1)` and `Fv n` solves the response equation at contact `κs n/(n+1)`, `κs → κ = D.κ`, then `‖stepL2 (Fv n) − F‖ → 0` with `F` the bulk response at `κ` (`StrongLimitBulk.strong_limit_bulk` at the fixed coupling `κ`, plus the parameter bound).
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

noncomputable section
open MeasureTheory Filter Topology Set Finset
open scoped ENNReal NNReal BigOperators Matrix

namespace QuantumNLS.VarStrong

open QuantumNLS.FiniteResponse (Bop wt L2N)
open QuantumNLS.StepIntegrals (stepL2 stepL2_sub norm_sq_step)
open QuantumNLS.BulkResponseForm (L2Unit BulkResponseData)
open QuantumNLS.StrongLimitBulk (Q2 strong_limit_bulk)
open QuantumNLS.GaudinResponse (gaudinMatrix gaudinMatrix_mulVec responseVec gaudin_responseVec)

theorem bop_eq_gaudin' {N : ℕ} (L c : ℝ) (q v : Fin N → ℝ) :
    Bop L c q v = gaudinMatrix L c q *ᵥ v := by
  funext i
  rw [QuantumNLS.FiniteResponse.Bop_eq_erase, gaudinMatrix_mulVec]
  congr 1
  all_goals (try (refine Finset.sum_congr rfl fun j _ => ?_))
  all_goals (try (simp only [QuantumNLS.FiniteResponse.wt, div_eq_mul_inv]))

theorem resp_shift_le {n : ℕ} {L c c' : ℝ} (hL : 0 < L) (hc : 0 < c) (hc' : 0 < c')
    (q f f' : Fin (n + 1) → ℝ) (hf : Bop L c q f = q) (hf' : Bop L c' q f' = q)
    (hm2 : max (c' / c) (c / c') < 2) :
    ‖stepL2 f' - stepL2 f‖ ≤
      (max (c' / c) (c / c') - 1) / ((2 - max (c' / c) (c / c')) * L) * ‖stepL2 q‖ := by
  set m := max (c' / c) (c / c') with hm
  have hm1 : 1 ≤ m := QuantumNLS.VarResponse.one_le_m hc hc'
  have hN : 0 < n + 1 := Nat.succ_pos n
  have hNr : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have h := QuantumNLS.VarResponse.param_response hL hc hc' q f f' hf hf' hm2
  rw [← stepL2_sub]
  have hd := norm_sq_step hN (f' - f)
  have hq := norm_sq_step hN q
  unfold L2N at hd hq
  have e1 : ‖stepL2 (f' - f)‖ ^ 2 = 1 / ((n + 1 : ℕ) : ℝ) * ∑ i, (f' i - f i) ^ 2 := by
    rw [hd]; simp [Pi.sub_apply]
  have e2 : ‖stepL2 q‖ ^ 2 = 1 / ((n + 1 : ℕ) : ℝ) * ∑ i, q i ^ 2 := hq
  have h2m : 0 < 2 - m := by linarith
  have hsq : (‖stepL2 (f' - f)‖ * ((2 - m) * L)) ^ 2 ≤ ((m - 1) * ‖stepL2 q‖) ^ 2 := by
    have : (‖stepL2 (f' - f)‖ * ((2 - m) * L)) ^ 2 =
        1 / ((n + 1 : ℕ) : ℝ) * ((2 - m) ^ 2 * L ^ 2 * ∑ i, (f' i - f i) ^ 2) := by
      rw [mul_pow, e1]; ring
    rw [this, mul_pow, e2]
    calc 1 / ((n + 1 : ℕ) : ℝ) * ((2 - m) ^ 2 * L ^ 2 * ∑ i, (f' i - f i) ^ 2)
        ≤ 1 / ((n + 1 : ℕ) : ℝ) * ((m - 1) ^ 2 * ∑ i, q i ^ 2) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = _ := by ring
  have h3 := (pow_le_pow_iff_left₀ (by positivity) (by have := norm_nonneg (stepL2 q); nlinarith)
    (two_ne_zero)).1 hsq
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  linarith

theorem strong_response_V (D : BulkResponseData) {F : L2Unit} (hF : D.IsResponse F)
    {κs : ℕ → ℝ} (hκs : Tendsto κs atTop (𝓝 D.κ)) (hpos : ∀ n, 0 < κs n)
    (q : ∀ n : ℕ, Fin (n + 1) → ℝ) (Fv : ∀ n : ℕ, Fin (n + 1) → ℝ)
    (hFv : ∀ n : ℕ, Bop D.L (κs n / ((n + 1 : ℕ) : ℝ)) (q n) (Fv n) = q n)
    (hQc : Tendsto (fun n : ℕ => ‖stepL2 (q n) - Q2 D‖) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => ‖stepL2 (Fv n) - F‖) atTop (𝓝 0) := by
  have hL : 0 < D.L := D.hL
  have hκ : 0 < D.κ := D.hκ
  set f : ∀ n : ℕ, Fin (n + 1) → ℝ := fun n => responseVec D.L (D.κ / ((n + 1 : ℕ) : ℝ)) (q n)
    with hfdef
  have hcn : ∀ n : ℕ, 0 < D.κ / ((n + 1 : ℕ) : ℝ) := fun n => by positivity
  have hf : ∀ n : ℕ, Bop D.L (D.κ / ((n + 1 : ℕ) : ℝ)) (q n) (f n) = q n := by
    intro n
    rw [bop_eq_gaudin']
    exact gaudin_responseVec hL (hcn n) (q n)
  have h1 : Tendsto (fun n : ℕ => ‖stepL2 (f n) - F‖) atTop (𝓝 0) :=
    (strong_limit_bulk D hF (N := fun n => n + 1) (fun n => Nat.succ_pos n)
      (tendsto_add_atTop_nat 1) q f hf hQc).1
  -- the parameter shift
  set mm : ℕ → ℝ := fun n => max (κs n / D.κ) (D.κ / κs n) with hmm
  have hmm1 : Tendsto mm atTop (𝓝 1) := by
    have a1 : Tendsto (fun n => κs n / D.κ) atTop (𝓝 1) := by
      simpa [div_self hκ.ne'] using hκs.div_const D.κ
    have a2 : Tendsto (fun n => D.κ / κs n) atTop (𝓝 1) := by
      have h := (tendsto_const_nhds (x := D.κ)).div hκs hκ.ne'
      rw [div_self hκ.ne'] at h
      exact h
    have := a1.max a2
    simpa using this
  have hratio : ∀ n : ℕ, max ((κs n / ((n + 1 : ℕ) : ℝ)) / (D.κ / ((n + 1 : ℕ) : ℝ)))
      ((D.κ / ((n + 1 : ℕ) : ℝ)) / (κs n / ((n + 1 : ℕ) : ℝ))) = mm n := by
    intro n
    have hN : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have e1 : (κs n / ((n + 1 : ℕ) : ℝ)) / (D.κ / ((n + 1 : ℕ) : ℝ)) = κs n / D.κ := by
      field_simp
    have e2 : (D.κ / ((n + 1 : ℕ) : ℝ)) / (κs n / ((n + 1 : ℕ) : ℝ)) = D.κ / κs n := by
      field_simp [(hpos n).ne']
    rw [e1, e2]
  have hQb : ∀ᶠ n : ℕ in atTop, ‖stepL2 (q n)‖ ≤ ‖Q2 D‖ + 1 := by
    filter_upwards [hQc.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with n hn
    have := norm_sub_norm_le (stepL2 (q n)) (Q2 D)
    linarith
  have hm2 : ∀ᶠ n : ℕ in atTop, mm n < 2 := hmm1.eventually (gt_mem_nhds (by norm_num))
  have hbd : Tendsto (fun n : ℕ => (mm n - 1) / ((2 - mm n) * D.L) * (‖Q2 D‖ + 1)) atTop (𝓝 0) := by
    have h2 : Tendsto (fun n : ℕ => (mm n - 1) / ((2 - mm n) * D.L)) atTop
        (𝓝 ((1 - 1) / ((2 - 1) * D.L))) := by
      refine (hmm1.sub_const 1).div ((tendsto_const_nhds.sub hmm1).mul_const D.L) ?_
      norm_num; exact hL.ne'
    simpa using h2.mul_const (‖Q2 D‖ + 1)
  have h3 : Tendsto (fun n : ℕ => ‖stepL2 (Fv n) - stepL2 (f n)‖) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hbd
    filter_upwards [hQb, hm2] with n hn hm
    have hcpos : 0 < κs n / ((n + 1 : ℕ) : ℝ) := div_pos (hpos n) (by positivity)
    have := resp_shift_le hL (hcn n) hcpos (q n) (f n) (Fv n) (hf n) (hFv n)
      (by rw [hratio n]; exact hm)
    rw [hratio n] at this
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    refine this.trans ?_
    have hm1 : 1 ≤ mm n := by
      have := QuantumNLS.VarResponse.one_le_m (hcn n) hcpos
      rwa [hratio n] at this
    have : 0 ≤ (mm n - 1) / ((2 - mm n) * D.L) := by
      apply div_nonneg (by linarith)
      exact mul_nonneg (by linarith) hL.le
    exact mul_le_mul_of_nonneg_left hn this
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) (by have := h3.add h1; rwa [add_zero] at this)
  calc ‖stepL2 (Fv n) - F‖ = ‖(stepL2 (Fv n) - stepL2 (f n)) + (stepL2 (f n) - F)‖ := by
        congr 1; abel
    _ ≤ _ := norm_add_le _ _

end QuantumNLS.VarStrong

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.VarStrong.resp_shift_le
#print axioms QuantumNLS.VarStrong.strong_response_V
