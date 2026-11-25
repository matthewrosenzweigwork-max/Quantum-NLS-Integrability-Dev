import Mathlib
import QuantumNLS.DetGapRowLim
import QuantumNLS.DetGapW2
import QuantumNLS.F04SelRank
import QuantumNLS.F04SelSetup

/-!
# CC:F04:variable-coupling (R-C88B5D59), step 9: quadratic Wasserstein convergence of one endpoint measure

Source: `F04.tex` line 412: "one endpoint empirical root measure for the transfer `η^{(N)} ↦ η^{(N)} − e_b + e_a` converges to `μ` in quadratic Wasserstein distance" and (proof) "The path-distance identity (CC:F04:path-distance) is independent of the contact parameter, so its quadratic-Wasserstein estimate and uniformity in the interpolation parameter remain valid."

* `weak_of_W2`: `W₂(μ_N, μ) → 0` implies the weak convergence `EmpiricalWeakConv q μ` (used by the selection proposition): for a bounded Lipschitz test `f`, `|∫f dμ_N − ∫ f dμ| ≤ Lip(f) ‖stepL2 q − Q‖_{L²(0,1)}` through the quantile representation (`DetGapW2.norm_step_sub_Q2`), and bounded Lipschitz tests determine weak convergence (Portmanteau).
* `weak_shift`: the weak limit passes between the two endpoints `s = 0, 1` (path `ℓ¹` bound, `F04SelSetup.path_l1`).
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

noncomputable section
open MeasureTheory Filter Topology Set Finset
open scoped ENNReal NNReal BigOperators

namespace QuantumNLS.VarW2Weak

open QuantumNLS.DetGapRowLim (oneL2 stepL2_one integral_pull)
open QuantumNLS.DetGapW2 (norm_step_sub_Q2)
open QuantumNLS.FiniteResponse (ipN dot L2N)
open QuantumNLS.StepIntegrals (stepL2 stepF stepL2_ae measurable_stepF inner_step norm_sq_step)
open QuantumNLS.SmoothJ (compL2 compL2_ae norm_compL2_sub_le stepL2_comp)
open QuantumNLS.BulkResponseForm (L2Unit BulkResponseData)
open QuantumNLS.QuantileForm (uI)
open QuantumNLS.QuantileTransport (qm quantile empirical W2 measurable_qm)
open QuantumNLS.StrongLimitBulk (Q2)
open QuantumNLS.BulkResponseRiesz (inner_eq_integral)
open QuantumNLS.LocalHeight (EmpiricalWeakConv)
open QuantumNLS.F04SelRank (tendsto_weakConv integral_empP pmOf)

theorem norm_oneL2 : ‖oneL2‖ = 1 := by
  have h := norm_sq_step (Nat.succ_pos 0) (fun _ : Fin 1 => (1 : ℝ))
  rw [stepL2_one 0] at h
  have h2 : ‖oneL2‖ ^ 2 = 1 := by
    rw [h]; unfold L2N; simp
  have h0 := norm_nonneg oneL2
  exact le_antisymm (by nlinarith) (by nlinarith)

theorem weak_of_W2 (D : BulkResponseData) {q : ∀ n : ℕ, Fin (n + 1) → ℝ}
    (hq : ∀ n, Monotone (q n))
    (hW : Tendsto (fun n : ℕ => W2 (empirical (n + 1) (q n)) D.μ) atTop (𝓝 0)) :
    EmpiricalWeakConv q D.μ := by
  haveI := D.hμ.isProbability
  have hQ : Tendsto (fun n : ℕ => ‖stepL2 (q n) - Q2 D‖) atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hW
    simp only [ENNReal.toReal_zero] at h
    refine h.congr fun n => ?_
    exact (norm_step_sub_Q2 D (Nat.succ_pos n) (hq n)).symm
  have hQm : Measurable (qm D.μ) := measurable_qm D.μ
  have hQ0 : ((Q2 D : L2Unit) : ℝ → ℝ) =ᵐ[uI] qm D.μ := MemLp.coeFn_toLp _
  apply tendsto_weakConv
  rw [MeasureTheory.tendsto_iff_forall_lipschitz_integral_tendsto]
  rintro f ⟨C, hC⟩ ⟨Lip, hLip⟩
  have hB : ∀ x, |f x| ≤ |f 0| + C := fun x => by
    have := hC x 0
    rw [Real.dist_eq] at this
    linarith [abs_sub_abs_le_abs_sub (f x) (f 0)]
  have hm : Measurable f := hLip.continuous.measurable
  -- the pointwise estimate
  have key : ∀ n : ℕ, |∫ x, f x ∂(QuantumNLS.F04SelRank.empP (q n) : Measure ℝ) - ∫ x, f x ∂D.μ| ≤
      (Lip : ℝ) * ‖stepL2 (q n) - Q2 D‖ := by
    intro n
    have hN : 0 < n + 1 := Nat.succ_pos n
    have e1 : ∫ x, f x ∂(QuantumNLS.F04SelRank.empP (q n) : Measure ℝ) =
        inner ℝ (compL2 hm hB (measurable_stepF (q n))) oneL2 := by
      rw [integral_empP, ← stepL2_comp hN hm hB (q n), ← stepL2_one n, inner_step hN]
      unfold ipN dot
      simp only [mul_one]
      push_cast
      rw [one_div]
    have e2 : ∫ x, f x ∂D.μ = inner ℝ (compL2 hm hB hQm) oneL2 := by
      rw [inner_eq_integral]
      have : ∫ t, (compL2 hm hB hQm : ℝ → ℝ) t * (oneL2 : ℝ → ℝ) t ∂uI =
          ∫ t, f (qm D.μ t) ∂uI := by
        refine integral_congr_ae ?_
        filter_upwards [compL2_ae hm hB hQm,
          MemLp.coeFn_toLp (memLp_const (1 : ℝ) : MemLp (fun _ : ℝ => (1 : ℝ)) 2 uI)] with t h1 h2
        simp only [oneL2] at h2 ⊢
        rw [h1, h2]; simp
      rw [this, integral_pull D.μ hm]
    rw [e1, e2, ← inner_sub_left]
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [norm_oneL2, mul_one]
    exact norm_compL2_sub_le hLip hB (measurable_stepF (q n)) hQm (stepL2_ae (q n)) hQ0
  have hlim : Tendsto (fun n : ℕ => (Lip : ℝ) * ‖stepL2 (q n) - Q2 D‖) atTop (𝓝 0) := by
    simpa using hQ.const_mul (Lip : ℝ)
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) hlim
  rw [Real.dist_eq]
  exact key n

/-- Weak convergence of the old endpoint from that of the new endpoint (and conversely): the `ℓ¹` distance
of the two endpoint arrays is `2π(a−b)/L` (CC:F04:path-distance), independent of the contact `c`. -/
theorem weak_shift {L : ℝ} (hL : 0 < L) {cs : ℕ → ℝ} (hcs : ∀ n, 0 < cs n) {μ : Measure ℝ}
    [IsProbabilityMeasure μ] {a b : ℤ} (hab : b < a)
    (η : (n : ℕ) → QuantumNLS.BetheLabels.MArr (n + 1)) (hb : ∀ n, 1 ≤ (η n).1 b)
    (hend : EmpiricalWeakConv (fun n => QuantumNLS.F02FiniteGap.qPath L (cs n) (η n) (hb n) a 1) μ) :
    EmpiricalWeakConv (fun n => QuantumNLS.F02FiniteGap.qPath L (cs n) (η n) (hb n) a 0) μ := by
  refine QuantumNLS.F04SelSetup.weakConv_of_l1 hend ?_
  have hC : Tendsto (fun N : ℕ => (1 / ((N : ℝ) + 1)) * (2 * Real.pi * ((a : ℝ) - b) / L)) atTop
      (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const
      (2 * Real.pi * ((a : ℝ) - b) / L)
    simpa using this
  refine squeeze_zero (fun N => by positivity) (fun N => ?_) hC
  have h0 := QuantumNLS.F04SelSetup.path_l1 hL (hcs N) (η N) (hb N) hab (le_refl (0 : ℝ)) zero_le_one
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [h0]; simp

end QuantumNLS.VarW2Weak

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.VarW2Weak.weak_of_W2
#print axioms QuantumNLS.VarW2Weak.weak_shift
