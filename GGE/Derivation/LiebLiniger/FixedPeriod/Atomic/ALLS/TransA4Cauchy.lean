import Mathlib

/-! # Track A, step A4 (generic): uniform Cauchy-type bounds for iterated derivatives

Author: Claude Opus 5.5 (track A).  Not self-reviewed, not accepted.

For a real-analytic map `f : E → F` between real normed spaces (`F` complete) and a point `x`,
there are `C, ρ > 0` such that for every order `k` and every `y` with `‖y‖ ≤ ρ`

  `‖D^k f(x + y)‖ ≤ C · k! · ρ^{-k}`.

This real-variable estimate plays the role of the complex Cauchy estimates in the Pro report
("Local complex bounds", "Holomorphy in the stronger target"): it bounds the derivative of the
base-level map uniformly on a small ball around a real center.  Proof: re-expand the power
series at `x + y` (`HasFPowerSeriesOnBall.changeOrigin`), bound the re-expanded coefficients by
`nnnorm_changeOriginSeries_le_tsum` and `C(k+l, l) ≤ 2^{k+l}`, and use the permutation-sum formula
for iterated derivatives (`HasFPowerSeriesOnBall.iteratedFDeriv_eq_sum_of_completeSpace`).

Also: the mean-value (Lipschitz) bound for `D^k f` on that ball when `f` is analytic everywhere. -/

set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal Nat

namespace NlsGge.ALLS.TransA

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- Norm of the `l`-th term of the change-of-origin series. -/
theorem norm_changeOriginSeries_apply_le (p : FormalMultilinearSeries ℝ E F) (k l : ℕ) (y : E) :
    ‖p.changeOriginSeries k l (fun _ => y)‖ ≤ ((k + l).choose l : ℝ) * ‖p (k + l)‖ * ‖y‖ ^ l := by
  have h := p.nnnorm_changeOriginSeries_apply_le_tsum k l y
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_finset_len,
    Fintype.card_fin, nsmul_eq_mul] at h
  have h' := NNReal.coe_le_coe.2 h
  simpa [mul_assoc] using h'

/-- Uniform bound on the re-expanded coefficients near the center. -/
theorem norm_changeOrigin_le (p : FormalMultilinearSeries ℝ E F) {r C : ℝ} (hr : 0 < r)
    (hC : ∀ n, ‖p n‖ ≤ C / r ^ n) (k : ℕ) {y : E} (hy : ‖y‖ ≤ r / 4) :
    ‖p.changeOrigin y k‖ ≤ 2 * C * (2 / r) ^ k := by
  have hC0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hC 0); simpa using this
  have hterm : ∀ l : ℕ, ‖p.changeOriginSeries k l (fun _ => y)‖ ≤ C * (2 / r) ^ k * (1 / 2) ^ l := by
    intro l
    refine (norm_changeOriginSeries_apply_le p k l y).trans ?_
    have hch : ((k + l).choose l : ℝ) ≤ 2 ^ (k + l) := by exact_mod_cast Nat.choose_le_two_pow _ _
    have hyl : ‖y‖ ^ l ≤ (r / 4) ^ l := pow_le_pow_left₀ (norm_nonneg _) hy l
    have hp := hC (k + l)
    calc ((k + l).choose l : ℝ) * ‖p (k + l)‖ * ‖y‖ ^ l
        ≤ 2 ^ (k + l) * (C / r ^ (k + l)) * (r / 4) ^ l := by gcongr
      _ = C * (2 / r) ^ k * (1 / 2) ^ l := by
        have h4 : (4 : ℝ) ^ l = 2 ^ l * 2 ^ l := by rw [← mul_pow]; norm_num
        rw [pow_add, pow_add, div_pow, div_pow, div_pow, one_pow, h4]
        field_simp
        try ring
  have hsum : Summable fun l : ℕ => C * (2 / r) ^ k * (1 / 2 : ℝ) ^ l :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hsn : Summable fun l : ℕ => ‖p.changeOriginSeries k l (fun _ => y)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hsum
  calc ‖p.changeOrigin y k‖
      = ‖∑' l, p.changeOriginSeries k l (fun _ => y)‖ := rfl
    _ ≤ ∑' l, ‖p.changeOriginSeries k l (fun _ => y)‖ := norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' l : ℕ, C * (2 / r) ^ k * (1 / 2 : ℝ) ^ l := hsn.tsum_le_tsum hterm hsum
    _ = 2 * C * (2 / r) ^ k := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
        ring

/-- The operator norm of the `k`-th iterated derivative is at most `k!` times the norm of the
`k`-th coefficient of any power series of `f` at that point. -/
theorem norm_iteratedFDeriv_le_factorial_mul [CompleteSpace F] {f : E → F}
    {p : FormalMultilinearSeries ℝ E F} {x : E} {R : ℝ≥0∞} (h : HasFPowerSeriesOnBall f p x R)
    (k : ℕ) : ‖iteratedFDeriv ℝ k f x‖ ≤ k ! * ‖p k‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun v => ?_
  rw [h.iteratedFDeriv_eq_sum_of_completeSpace]
  calc ‖∑ σ : Equiv.Perm (Fin k), p k (fun i => v (σ i))‖
      ≤ ∑ σ : Equiv.Perm (Fin k), ‖p k (fun i => v (σ i))‖ := norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin k), ‖p k‖ * ∏ i, ‖v i‖ := by
        refine Finset.sum_le_sum fun σ _ => ?_
        refine ((p k).le_opNorm _).trans_eq ?_
        congr 1
        exact Equiv.prod_comp σ (fun i => ‖v i‖)
    _ = k ! * ‖p k‖ * ∏ i, ‖v i‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul,
          mul_assoc]

/-- **Uniform Cauchy-type bound**: `‖D^k f(x + y)‖ ≤ C · k! · ρ^{-k}` for `‖y‖ ≤ ρ`. -/
theorem exists_iteratedFDeriv_bound [CompleteSpace F] {f : E → F} {x : E} (hf : AnalyticAt ℝ f x) :
    ∃ C ρ : ℝ, 0 < C ∧ 0 < ρ ∧ ∀ (k : ℕ) (y : E), ‖y‖ ≤ ρ →
      ‖iteratedFDeriv ℝ k f (x + y)‖ ≤ C * k ! * (ρ⁻¹) ^ k := by
  obtain ⟨p, R, hp⟩ := hf
  obtain ⟨r, hr0, hrR⟩ : ∃ r : ℝ≥0, 0 < r ∧ (r : ℝ≥0∞) < R := by
    obtain ⟨r, hr, hrR⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hp.r_pos
    exact ⟨r, by exact_mod_cast hr, hrR⟩
  have hrad : (r : ℝ≥0∞) < p.radius := hrR.trans_le hp.r_le
  obtain ⟨C, hC, hCb⟩ := p.norm_le_div_pow_of_pos_of_lt_radius hr0 hrad
  have hr : (0 : ℝ) < r := by exact_mod_cast hr0
  refine ⟨2 * C, (r : ℝ) / 4, by positivity, by positivity, fun k y hy => ?_⟩
  have hyR : (‖y‖₊ : ℝ≥0∞) < R := by
    refine lt_of_le_of_lt ?_ hrR
    have : ‖y‖ ≤ (r : ℝ) := hy.trans (by linarith)
    exact_mod_cast this
  have hpy := hp.changeOrigin hyR
  calc ‖iteratedFDeriv ℝ k f (x + y)‖ ≤ k ! * ‖p.changeOrigin y k‖ :=
        norm_iteratedFDeriv_le_factorial_mul hpy k
    _ ≤ k ! * (2 * C * (2 / r) ^ k) := by
        gcongr
        exact norm_changeOrigin_le p hr hCb k hy
    _ ≤ k ! * (2 * C * (4 / (r : ℝ)) ^ k) := by
        gcongr
        linarith
    _ = 2 * C * k ! * (((r : ℝ) / 4)⁻¹) ^ k := by
        rw [inv_div]; ring

/-- **Lipschitz bound for iterated derivatives** on the Cauchy ball, for `f` analytic everywhere:
`‖D^k f(x + y) - D^k f(x + y')‖ ≤ C (k+1)! ρ^{-(k+1)} ‖y - y'‖` for `‖y‖, ‖y'‖ ≤ ρ`. -/
theorem iteratedFDeriv_lipschitz_on_ball [CompleteSpace F] {f : E → F}
    (hf : AnalyticOnNhd ℝ f Set.univ) {x : E} {C ρ : ℝ}
    (hb : ∀ (k : ℕ) (y : E), ‖y‖ ≤ ρ → ‖iteratedFDeriv ℝ k f (x + y)‖ ≤ C * k ! * (ρ⁻¹) ^ k)
    (k : ℕ) {y y' : E} (hy : ‖y‖ ≤ ρ) (hy' : ‖y'‖ ≤ ρ) :
    ‖iteratedFDeriv ℝ k f (x + y) - iteratedFDeriv ℝ k f (x + y')‖ ≤
      C * (k + 1)! * (ρ⁻¹) ^ (k + 1) * ‖y - y'‖ := by
  have hcd : ContDiff ℝ (k + 1) f := hf.contDiff
  have hdiff : Differentiable ℝ fun z => iteratedFDeriv ℝ k f z :=
    hcd.differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self k)
  have hconv : Convex ℝ (Metric.closedBall x ρ) := convex_closedBall x ρ
  have hmem : ∀ z : E, ‖z‖ ≤ ρ → x + z ∈ Metric.closedBall x ρ := by
    intro z hz; rw [Metric.mem_closedBall, dist_eq_norm]; simpa using hz
  have key := hconv.norm_image_sub_le_of_norm_fderiv_le (f := fun z => iteratedFDeriv ℝ k f z)
    (C := C * (k + 1)! * (ρ⁻¹) ^ (k + 1)) (fun z _ => hdiff z) (fun z hz => by
      rw [norm_fderiv_iteratedFDeriv]
      have hz' : ‖z - x‖ ≤ ρ := by rw [← dist_eq_norm]; exact Metric.mem_closedBall.1 hz
      have := hb (k + 1) (z - x) hz'
      simpa using this) (hmem y' hy') (hmem y hy)
  simpa using key

end NlsGge.ALLS.TransA
