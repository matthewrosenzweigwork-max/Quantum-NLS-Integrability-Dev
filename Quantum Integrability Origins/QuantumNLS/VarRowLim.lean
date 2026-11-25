import Mathlib
import QuantumNLS.DetGapRowLim

/-!
# CC:F04:variable-coupling (R-C88B5D59), step 6: the row limit at contact `c_N = κ_N/N`

Source: `F04.tex` line 412 (proof): "The separated row equation (CC:F04:row) has `κ_N` in place of `κ` at finite `N`; the strong bulk limit just proved and `κ_N → κ` give its stated limit."

`row_limitV` is `DetGapRowLim.row_limit` (read-only, whose proof is followed verbatim) for the row equation at contact `κs n/(n+1)`: the response `Fv n` solves `Bop L (κs n/(n+1)) (q n) (Fv n) = q n`, the step responses converge strongly to the `F` of the fixed coupling `κ = D.κ` (`hFc`), and `κs → κ`.  The limit is the same `f_ext` at `κ`.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

noncomputable section
open MeasureTheory Filter Topology Set Finset
open scoped ENNReal NNReal BigOperators

namespace QuantumNLS.VarRowLim

open QuantumNLS.DetGapRow (row_identity kk kk_eq kk_pos kk_le hker hker_bdd hker_lip kernel_L2_tendsto)
open QuantumNLS.DetGapRowLim (fext oneL2 stepL2_one integral_pull hker_ae)
open QuantumNLS.FiniteResponse (Bop wt ipN dot)
open QuantumNLS.StepIntegrals (stepL2 stepF stepL2_ae inner_step idx)
open QuantumNLS.SmoothJ (compL2 compL2_ae)
open QuantumNLS.BulkResponseForm (L2Unit BulkResponseData)
open QuantumNLS.QuantileForm (uI)
open QuantumNLS.QuantileTransport (qm map_qm measurable_qm)
open QuantumNLS.StrongLimitBulk (Q2)
open QuantumNLS.BulkResponseRiesz (inner_eq_integral)

/-- **The row limit at contact `κs n/(n+1)`.** -/
theorem row_limitV (D : BulkResponseData) {κs : ℕ → ℝ} (hκs : Tendsto κs atTop (𝓝 D.κ))
    (hpos : ∀ n, 0 < κs n) {F : L2Unit} {f : ℝ → ℝ} (hfm : Measurable f)
    (hF : (F : ℝ → ℝ) =ᵐ[uI] fun t => f (qm D.μ t))
    (q : ∀ n : ℕ, Fin (n + 1) → ℝ) (Fv : ∀ n : ℕ, Fin (n + 1) → ℝ)
    (hFv : ∀ n : ℕ, Bop D.L (κs n / ((n + 1 : ℕ) : ℝ)) (q n) (Fv n) = q n)
    (hQc : Tendsto (fun n : ℕ => ‖stepL2 (q n) - Q2 D‖) atTop (𝓝 0))
    (hFc : Tendsto (fun n : ℕ => ‖stepL2 (Fv n) - F‖) atTop (𝓝 0))
    (i : ∀ n : ℕ, Fin (n + 1)) {x ε : ℝ} (hε : 0 < ε)
    (hz : Tendsto (fun n : ℕ => q n (i n)) atTop (𝓝 x))
    (hsep : ∀ᶠ n : ℕ in atTop, ∀ j : Fin (n + 1), j ≠ i n → ε ≤ |q n (i n) - q n j|)
    (hμ : D.μ (Ioo (x - ε) (x + ε)) = 0)
    {M : ℝ} (hM : ∀ᶠ n : ℕ in atTop, |Fv n (i n)| ≤ M) :
    Tendsto (fun n : ℕ => Fv n (i n)) atTop (𝓝 (fext D.L D.κ D.μ f x)) := by
  haveI := D.hμ.isProbability
  have hL : 0 < D.L := D.hL
  have hκ : 0 < D.κ := D.hκ
  have hQm : Measurable (qm D.μ) := measurable_qm D.μ
  set κ := D.κ with hκdef
  set L := D.L with hLdef
  -- the data
  set c : ℕ → ℝ := fun n => κs n / ((n + 1 : ℕ) : ℝ) with hcdef
  set r : ℕ → ℝ := fun n => 1 / ((n + 1 : ℕ) : ℝ) with hrdef
  have hr0 : Tendsto r atTop (𝓝 0) := by
    have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    refine this.congr fun n => ?_
    simp [hrdef]
  have hc0 : Tendsto c atTop (𝓝 0) := by
    have := hκs.mul hr0
    rw [mul_zero] at this
    refine this.congr fun n => ?_
    simp [hcdef, hrdef, div_eq_mul_inv]
  have hcpos : ∀ n, 0 < c n := fun n => by
    simp only [hcdef]; exact div_pos (hpos n) (by positivity)
  set z : ℕ → ℝ := fun n => q n (i n) with hzdef
  set kv : ∀ n : ℕ, Fin (n + 1) → ℝ := fun n j => kk (c n) ε (z n - q n j) with hkvdef
  set kerL : L2Unit := compL2 (hker_lip hε x).continuous.measurable (hker_bdd hε x) hQm with hkerL
  -- strong convergence of the kernel tests
  have hQ0 : ((Q2 D : L2Unit) : ℝ → ℝ) =ᵐ[uI] qm D.μ := MemLp.coeFn_toLp _
  have hkc : Tendsto (fun n : ℕ => ‖stepL2 (kv n) - kerL‖) atTop (𝓝 0) :=
    kernel_L2_tendsto hε hQm hQ0 hQc hz hc0
  have hkc' : Tendsto (fun n : ℕ => stepL2 (kv n)) atTop (𝓝 kerL) :=
    tendsto_iff_norm_sub_tendsto_zero.2 hkc
  have hFc' : Tendsto (fun n : ℕ => stepL2 (Fv n)) atTop (𝓝 F) :=
    tendsto_iff_norm_sub_tendsto_zero.2 hFc
  -- the two pairings
  have hS2 : Tendsto (fun n : ℕ => ipN (n + 1) (Fv n) (kv n)) atTop (𝓝 (inner ℝ F kerL)) := by
    have := Filter.Tendsto.inner (𝕜 := ℝ) hFc' hkc'
    refine this.congr fun n => ?_
    exact inner_step (Nat.succ_pos n) (Fv n) (kv n)
  have hS1 : Tendsto (fun n : ℕ => ipN (n + 1) (fun _ => (1 : ℝ)) (kv n)) atTop
      (𝓝 (inner ℝ oneL2 kerL)) := by
    have := Filter.Tendsto.inner (𝕜 := ℝ) (tendsto_const_nhds (x := oneL2)) hkc'
    refine this.congr fun n => ?_
    rw [← stepL2_one n]
    exact inner_step (Nat.succ_pos n) (fun _ => (1 : ℝ)) (kv n)
  -- identification of the limits
  have hkAE : (kerL : ℝ → ℝ) =ᵐ[uI] fun t => hker x ε (qm D.μ t) := compL2_ae _ _ _
  have hhm : Measurable (hker x ε) := (hker_lip hε x).continuous.measurable
  have hA : inner ℝ oneL2 kerL = ∫ y, 1 / (x - y) ^ 2 ∂D.μ := by
    rw [inner_eq_integral]
    have h1 : ∫ t, ((oneL2 : L2Unit) : ℝ → ℝ) t * (kerL : ℝ → ℝ) t ∂uI =
        ∫ t, hker x ε (qm D.μ t) ∂uI := by
      refine integral_congr_ae ?_
      filter_upwards [MemLp.coeFn_toLp (memLp_const (1 : ℝ) : MemLp (fun _ : ℝ => (1 : ℝ)) 2 uI),
        hkAE] with t h1 h2
      simp only [oneL2] at h1 ⊢
      rw [h1, h2]; simp
    rw [h1, integral_pull D.μ hhm]
    exact integral_congr_ae (hker_ae D.μ hε hμ)
  have hB : inner ℝ F kerL = ∫ y, f y / (x - y) ^ 2 ∂D.μ := by
    rw [inner_eq_integral]
    have h1 : ∫ t, (F : ℝ → ℝ) t * (kerL : ℝ → ℝ) t ∂uI =
        ∫ t, f (qm D.μ t) * hker x ε (qm D.μ t) ∂uI := by
      refine integral_congr_ae ?_
      filter_upwards [hF, hkAE] with t h1 h2
      rw [h1, h2]
    rw [h1, integral_pull D.μ (g := fun y => f y * hker x ε y) (hfm.mul hhm)]
    refine integral_congr_ae ?_
    filter_upwards [hker_ae D.μ hε hμ] with y hy
    simp only [hy]
    ring
  rw [hA] at hS1
  rw [hB] at hS2
  -- the diagonal terms
  have hdiag : ∀ n, 0 ≤ kv n (i n) ∧ kv n (i n) ≤ 1 / ε ^ 2 := fun n =>
    ⟨(kk_pos hε _).le, kk_le hε _⟩
  have hd1 : Tendsto (fun n : ℕ => r n * kv n (i n)) atTop (𝓝 0) := by
    have hb : Tendsto (fun n : ℕ => r n * (1 / ε ^ 2)) atTop (𝓝 0) := by
      have := hr0.mul_const (1 / ε ^ 2)
      rwa [zero_mul] at this
    refine squeeze_zero (fun n => ?_) (fun n => ?_) hb
    · have : 0 ≤ r n := by simp only [hrdef]; positivity
      exact mul_nonneg this (hdiag n).1
    · have : 0 ≤ r n := by simp only [hrdef]; positivity
      exact mul_le_mul_of_nonneg_left (hdiag n).2 this
  have hd2 : Tendsto (fun n : ℕ => r n * (Fv n (i n) * kv n (i n))) atTop (𝓝 0) := by
    have hb : Tendsto (fun n : ℕ => r n * (|M| * (1 / ε ^ 2))) atTop (𝓝 0) := by
      have := hr0.mul_const (|M| * (1 / ε ^ 2))
      rwa [zero_mul] at this
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [hM] with n hn
    have h0 : 0 ≤ r n := by simp only [hrdef]; positivity
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0, abs_mul, abs_of_nonneg (hdiag n).1]
    refine mul_le_mul_of_nonneg_left ?_ h0
    exact mul_le_mul (hn.trans (le_abs_self M)) (hdiag n).2 (hdiag n).1 (abs_nonneg _)
  -- numerator and denominator
  set num : ℕ → ℝ := fun n => z n + 2 * κs n * (ipN (n + 1) (Fv n) (kv n) - r n * (Fv n (i n) * kv n (i n)))
    with hnum
  set den : ℕ → ℝ := fun n => L + 2 * κs n * (ipN (n + 1) (fun _ => (1 : ℝ)) (kv n) - r n * kv n (i n))
    with hden
  have hnumT : Tendsto num atTop (𝓝 (x + 2 * κ * ∫ y, f y / (x - y) ^ 2 ∂D.μ)) := by
    have := hz.add ((hκs.const_mul 2).mul (hS2.sub hd2))
    simpa [hnum] using this
  have hdenT : Tendsto den atTop (𝓝 (L + 2 * κ * ∫ y, 1 / (x - y) ^ 2 ∂D.μ)) := by
    have := (tendsto_const_nhds (x := L)).add ((hκs.const_mul 2).mul (hS1.sub hd1))
    simpa [hden] using this
  have hden_pos : 0 < L + 2 * κ * ∫ y, 1 / (x - y) ^ 2 ∂D.μ := by
    have h0 : 0 ≤ ∫ y, 1 / (x - y) ^ 2 ∂D.μ := integral_nonneg fun y => by positivity
    positivity
  have hlim := hnumT.div hdenT hden_pos.ne'
  refine hlim.congr' ?_
  filter_upwards [hsep] with n hn
  -- the exact row equation
  have hrow := row_identity (q n) (Fv n) (hFv n) (i n)
  have hw : ∀ j ∈ univ.erase (i n), wt (c n) (q n (i n)) (q n j) = 2 * κs n * r n * kv n j := by
    intro j hj
    have hji : j ≠ i n := Finset.ne_of_mem_erase hj
    have := kk_eq (c := c n) (hn j hji) hε
    simp only [hkvdef, hzdef]
    rw [this]
    simp only [wt, hcdef, hrdef]
    field_simp
  have hsum1 : ∑ j ∈ univ.erase (i n), wt (c n) (q n (i n)) (q n j) =
      2 * κs n * (ipN (n + 1) (fun _ => (1 : ℝ)) (kv n) - r n * kv n (i n)) := by
    rw [Finset.sum_congr rfl hw, ← Finset.mul_sum, Finset.sum_erase_eq_sub (mem_univ _)]
    unfold ipN dot
    simp only [one_mul, hrdef]
    ring
  have hsum2 : ∑ j ∈ univ.erase (i n), wt (c n) (q n (i n)) (q n j) * Fv n j =
      2 * κs n * (ipN (n + 1) (Fv n) (kv n) - r n * (Fv n (i n) * kv n (i n))) := by
    have : ∀ j ∈ univ.erase (i n), wt (c n) (q n (i n)) (q n j) * Fv n j =
        2 * κs n * r n * (Fv n j * kv n j) := by
      intro j hj
      rw [hw j hj]; ring
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, Finset.sum_erase_eq_sub (mem_univ _)]
    unfold ipN dot
    simp only [hrdef]
    ring
  rw [hsum1, hsum2] at hrow
  have hdpos : 0 < den n := by
    have h0 : 0 ≤ 2 * κs n * (ipN (n + 1) (fun _ => (1 : ℝ)) (kv n) - r n * kv n (i n)) := by
      rw [← hsum1]
      exact Finset.sum_nonneg fun j _ => by
        unfold wt
        have := hcpos n
        positivity
    simp only [hden]
    linarith
  rw [Pi.div_apply, div_eq_iff hdpos.ne']
  simp only [hnum, hden, hzdef] at hrow ⊢
  linear_combination (-1 : ℝ) * hrow

end QuantumNLS.VarRowLim

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.VarRowLim.row_limitV
