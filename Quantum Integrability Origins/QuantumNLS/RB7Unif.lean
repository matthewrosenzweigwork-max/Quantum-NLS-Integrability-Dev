import Mathlib
import QuantumNLS.RB7Grad

/-!
# R-7B122087 `thm:hierarchy`, uniform Hessian estimate on compact sets and the chart-derivative limit (sequence side)

Printed: "For a compact smooth initial class, the union of its modulus tori and coordinate-erasure sets is compact at every required order.  The Hessian
constants can therefore be chosen uniformly."  and "Full Hilbert symplecticity, tested against smooth variations, identifies its derivative with
`-i ∇ I_{r+1}(u(t))`.  The test gradients and vectors are smooth and the sums converge."

* `tl T z` (tail of `z` outside the finite set `T`), `exists_finset_tail_compact`: uniform tails of a compact subset of `h(W)`.
* `grad_bound_compact`: for `F` `C²` and rotation invariant on `h(W)` and `K ⊆ h(W)` compact there is one constant `C` with
  `‖∇_j F(z)‖ ≤ C W_j ‖z_j‖` for all `z ∈ K`, `j ∈ ℤ` (the uniform printed Hessian estimate).
* `hasDerivAt_curve` (sequence side of the gradient identification): if `ζ : ℝ → h(U)` is continuous (`W_j² ≤ U_j`, `1 ≤ W_j`), and
  `(ζ_ε - ζ_0)/ε → d` in the unweighted `ℓ²` (the chart derivative in `ℓ²`), then `ε ↦ F(ζ_ε)` is differentiable at `0` with
  derivative `2 Re Σ_j conj(∇_j F(ζ_0)) d_j`.  Only the continuity of the curve in the weighted spaces `h(U)` (the REG-015 homeomorphism
  input at the physical side) is used; no Lipschitz bound of the chart in `h(U)` is needed.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open scoped ComplexConjugate Topology
open Filter Set Metric

namespace QuantumNLS.RB7

open QuantumNLS.Sobolev
open QuantumNLS.Sobolev.PosWeight

section Tails

variable {W : PosWeight}

/-- The tail of `z` outside the finite set `T`. -/
def tl (T : Finset ℤ) (z : WSeq W) : WSeq W := z - trunc T z

@[simp] theorem tl_val (T : Finset ℤ) (z : WSeq W) (j : ℤ) :
    (tl T z).val j = if j ∈ T then 0 else z.val j := by
  by_cases h : j ∈ T <;> simp [tl, h]

theorem tl_sub (T : Finset ℤ) (x y : WSeq W) : tl T (x - y) = tl T x - tl T y :=
  WSeq.ext (funext fun j => by by_cases h : j ∈ T <;> simp [h])

theorem norm_tl_le (T : Finset ℤ) (z : WSeq W) : ‖tl T z‖ ≤ ‖z‖ := by
  refine le_of_sq_le_sq' (norm_nonneg _) ?_
  rw [norm_sq_eq_tsum, norm_sq_eq_tsum]
  refine Summable.tsum_le_tsum (fun n => ?_) (WSeq.summable _) (WSeq.summable _)
  rw [tl_val]
  by_cases h : n ∈ T <;> simp [h, (W.pos n).le, mul_nonneg]

theorem tendsto_tl (z : WSeq W) : Tendsto (fun T : Finset ℤ => ‖tl T z‖) atTop (𝓝 0) := by
  have h := (tendsto_const_nhds (x := z)).sub (tendsto_trunc z)
  rw [sub_self] at h
  have := h.norm
  simpa [tl] using this

/-- Uniform tails of a compact set. -/
theorem exists_finset_tail_compact {K : Set (WSeq W)} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Finset ℤ, ∀ z ∈ K, ‖tl T z‖ < ε := by
  obtain ⟨t, htK, htf, hcov⟩ := hK.finite_cover_balls (e := ε / 2) (by linarith)
  have hev : ∀ᶠ T : Finset ℤ in atTop, ∀ x ∈ t, ‖tl T x‖ < ε / 2 := by
    rw [Filter.eventually_all_finite htf]
    intro x _
    exact (tendsto_tl x).eventually (gt_mem_nhds (by linarith))
  obtain ⟨T, hT⟩ := hev.exists
  refine ⟨T, fun z hz => ?_⟩
  have := hcov hz
  simp only [mem_iUnion] at this
  obtain ⟨x, hx, hzx⟩ := this
  rw [Metric.mem_ball, dist_eq_norm] at hzx
  have h1 : tl T z = tl T x + tl T (z - x) := by rw [tl_sub]; abel
  calc ‖tl T z‖ ≤ ‖tl T x‖ + ‖tl T (z - x)‖ := by rw [h1]; exact norm_add_le _ _
    _ ≤ ‖tl T x‖ + ‖z - x‖ := by gcongr; exact norm_tl_le _ _
    _ < ε / 2 + ε / 2 := by have := hT x hx; linarith
    _ = ε := by ring

/-- For coordinates outside `T` the weighted coordinate is controlled by the tail. -/
theorem sqrt_w_mul_norm_le_tl (T : Finset ℤ) (z : WSeq W) (j : ℤ) (hj : j ∉ T) :
    Real.sqrt (W.w j) * ‖z.val j‖ ≤ ‖tl T z‖ := by
  have := sqrt_w_mul_norm_le (tl T z) j
  simpa [tl_val, hj] using this

end Tails

section Unif

variable {W : PosWeight} {F : WSeq W → ℝ}

/-- **The uniform printed Hessian estimate**: one constant for all `z` in a compact set. -/
theorem grad_bound_compact (hF : ContDiff ℝ 2 F) (hinv : ∀ u z, F (rot u z) = F z)
    {K : Set (WSeq W)} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, ∀ j : ℤ, ‖grad (fderiv ℝ F z) j‖ ≤ C * W.w j * ‖z.val j‖ := by
  have hD1 : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  have hD2 : Continuous (fderiv ℝ (fderiv ℝ F)) := hD1.continuous_fderiv one_ne_zero
  have hN : Continuous fun y => ‖fderiv ℝ (fderiv ℝ F) y‖ :=
    (continuous_norm (E := WSeq W →L[ℝ] WSeq W →L[ℝ] ℝ)).comp hD2
  -- a bound on `K`
  obtain ⟨B0, hB0⟩ := hK.exists_bound_of_continuousOn hN.continuousOn
  -- a uniform thickening
  have hopen : IsOpen {y : WSeq W | ‖fderiv ℝ (fderiv ℝ F) y‖ < max B0 0 + 1} :=
    isOpen_lt hN continuous_const
  have hsub : K ⊆ {y : WSeq W | ‖fderiv ℝ (fderiv ℝ F) y‖ < max B0 0 + 1} := by
    intro z hz
    have : ‖fderiv ℝ (fderiv ℝ F) z‖ ≤ B0 := by
      have h := hB0 z hz
      simpa [abs_of_nonneg (norm_nonneg (fderiv ℝ (fderiv ℝ F) z))] using h
    show ‖fderiv ℝ (fderiv ℝ F) z‖ < max B0 0 + 1
    linarith [le_max_left B0 0]
  obtain ⟨δ, hδ, hthick⟩ := hK.exists_thickening_subset_open hopen hsub
  -- the finite set of coordinates where erasure may move far
  obtain ⟨T, hT⟩ := exists_finset_tail_compact hK hδ
  -- compact segment unions for `j ∈ T`
  have hcomp : ∀ j : ℤ, IsCompact ((fun p : WSeq W × ℝ => p.1 - p.2 • (p.1.val j • ev W j)) ''
      (K ×ˢ Icc (0 : ℝ) 1)) := fun j => by
    refine (hK.prod isCompact_Icc).image ?_
    have := (continuous_val (W := W) j)
    fun_prop
  choose B hB using fun j : ℤ =>
    (hcomp j).exists_bound_of_continuousOn (f := fderiv ℝ (fderiv ℝ F)) hD2.continuousOn
  set M : ℝ := max B0 0 + 1 + ∑ j ∈ T, |B j| with hMdef
  have hsum0 : 0 ≤ ∑ j ∈ T, |B j| := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hM0 : 0 ≤ M := by
    have := le_max_right B0 0
    linarith
  refine ⟨M, hM0, fun z hz j => grad_bound_seg hF hinv z j M (fun y hy => ?_)⟩
  by_cases hj : j ∈ T
  · have hy' : y ∈ (fun p : WSeq W × ℝ => p.1 - p.2 • (p.1.val j • ev W j)) '' (K ×ˢ Icc (0 : ℝ) 1) := by
      rw [segment_eq_image] at hy
      obtain ⟨θ, hθ, rfl⟩ := hy
      refine ⟨(z, 1 - θ), ⟨hz, by constructor <;> linarith [hθ.1, hθ.2]⟩, ?_⟩
      simp only
      module
    have h1 : ‖fderiv ℝ (fderiv ℝ F) y‖ ≤ B j := hB j y hy'
    have h2 : B j ≤ |B j| := le_abs_self _
    have h3 : |B j| ≤ ∑ j ∈ T, |B j| :=
      Finset.single_le_sum (f := fun j => |B j|) (fun j _ => abs_nonneg _) hj
    have := le_max_right B0 0
    linarith
  · have hnorm : ‖z.val j • ev W j‖ < δ := by
      have h1 := sqrt_w_mul_norm_le_tl T z j hj
      have h2 := hT z hz
      rw [norm_smul]
      have : ‖ev W j‖ = Real.sqrt (W.w j) := by
        rw [← Real.sqrt_sq (norm_nonneg (ev W j)), norm_ev_sq]
      rw [this, mul_comm]
      linarith
    have hball : segment ℝ (z - z.val j • ev W j) z ⊆ Metric.ball z δ := by
      refine (convex_ball z δ).segment_subset ?_ (Metric.mem_ball_self hδ)
      rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg]
      exact hnorm
    have hyin : y ∈ thickening δ K := by
      rw [mem_thickening_iff]
      exact ⟨z, hz, by simpa [dist_comm] using hball hy⟩
    have : ‖fderiv ℝ (fderiv ℝ F) y‖ < max B0 0 + 1 := hthick hyin
    linarith

end Unif


/-! ## Comparable weights and the `ℓ²` gradient -/

/-- `W` is the weight of the space on which `F` lives; points are taken in the smaller space `h(U)`: `1 ≤ W` and `W² ≤ U`. -/
structure Cmp (W U : PosWeight) : Prop where
  one_le : ∀ j, 1 ≤ W.w j
  sq_le : ∀ j, W.w j ^ 2 ≤ U.w j

theorem Cmp.le {W U : PosWeight} (c : Cmp W U) : ∀ n, W.w n ≤ 1 * U.w n := fun n => by
  have h1 := c.one_le n
  have h2 := c.sq_le n
  nlinarith

/-- The inclusion `h(U) ↪ h(W)`. -/
def iWU {W U : PosWeight} (c : Cmp W U) : WSeq U →L[ℂ] WSeq W := incl W U zero_le_one c.le

@[simp] theorem iWU_val {W U : PosWeight} (c : Cmp W U) (y : WSeq U) : (iWU c y).val = y.val := rfl

section Curve

variable {W U : PosWeight} {F : WSeq W → ℝ}

/-- The coordinate gradient of `F` at the point `y ∈ h(U)`. -/
def Gs (F : WSeq W → ℝ) (c : Cmp W U) (y : WSeq U) (j : ℤ) : ℂ := grad (fderiv ℝ F (iWU c y)) j

theorem Gs_bound (c : Cmp W U) (hF : ContDiff ℝ 2 F) (hinv : ∀ u z, F (rot u z) = F z)
    {K : Set (WSeq U)} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ j, ‖Gs F c y j‖ ≤ C * W.w j * ‖y.val j‖ := by
  obtain ⟨C, hC0, hC⟩ := grad_bound_compact hF hinv (hK.image (iWU c).continuous)
  exact ⟨C, hC0, fun y hy j => hC (iWU c y) ⟨y, hy, rfl⟩ j⟩

theorem Gs_sq_le (c : Cmp W U) {C : ℝ} (y : WSeq U) (j : ℤ) (h : ‖Gs F c y j‖ ≤ C * W.w j * ‖y.val j‖) :
    ‖Gs F c y j‖ ^ 2 ≤ C ^ 2 * (U.w j * ‖y.val j‖ ^ 2) := by
  have h0 : 0 ≤ C * W.w j * ‖y.val j‖ := le_trans (norm_nonneg _) h
  calc ‖Gs F c y j‖ ^ 2 ≤ (C * W.w j * ‖y.val j‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = C ^ 2 * (W.w j ^ 2 * ‖y.val j‖ ^ 2) := by ring
    _ ≤ C ^ 2 * (U.w j * ‖y.val j‖ ^ 2) := by
        gcongr
        exact c.sq_le j

theorem summable_Gs_sq (c : Cmp W U) (hF : ContDiff ℝ 2 F) (hinv : ∀ u z, F (rot u z) = F z) (y : WSeq U) :
    Summable fun j => ‖Gs F c y j‖ ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := Gs_bound c hF hinv (isCompact_singleton (x := y))
  exact Summable.of_nonneg_of_le (fun j => sq_nonneg _) (fun j => Gs_sq_le c y j (hC y rfl j))
    (y.summable.mul_left (C ^ 2) |>.congr (fun j => by ring) |> fun h => by
      simpa [mul_assoc] using h)

theorem summable_Gs_div (c : Cmp W U) (hF : ContDiff ℝ 2 F) (hinv : ∀ u z, F (rot u z) = F z) (y : WSeq U) :
    Summable fun j => ‖grad (fderiv ℝ F (iWU c y)) j‖ ^ 2 / W.w j := by
  obtain ⟨C, hC0, hC⟩ := Gs_bound c hF hinv (isCompact_singleton (x := y))
  refine Summable.of_nonneg_of_le (fun j => div_nonneg (sq_nonneg _) (W.pos j).le) (fun j => ?_)
    ((iWU c y).summable.mul_left (C ^ 2))
  have h := hC y rfl j
  have hw := W.pos j
  rw [div_le_iff₀ hw]
  have h0 : 0 ≤ C * W.w j * ‖y.val j‖ := le_trans (norm_nonneg _) h
  calc ‖grad (fderiv ℝ F (iWU c y)) j‖ ^ 2 ≤ (C * W.w j * ‖y.val j‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = C ^ 2 * (W.w j * ‖(iWU c y).val j‖ ^ 2) * W.w j := by simp only [iWU_val]; ring


theorem tsum_mul_le_sqrt (f g : ℤ → ℝ) (hf : ∀ j, 0 ≤ f j) (hg : ∀ j, 0 ≤ g j)
    (hf2 : Summable fun j => f j ^ 2) (hg2 : Summable fun j => g j ^ 2) :
    Summable (fun j => f j * g j) ∧
      ∑' j, f j * g j ≤ Real.sqrt (∑' j, f j ^ 2) * Real.sqrt (∑' j, g j ^ 2) := by
  have h := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg (p := 2) (q := 2)
    Real.HolderConjugate.two_two hf hg (by simpa using hf2) (by simpa using hg2)
  refine ⟨h.1, ?_⟩
  have e1 : (∑' j, f j ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) = Real.sqrt (∑' j, f j ^ 2) := by
    rw [Real.sqrt_eq_rpow]; simp
  have e2 : (∑' j, g j ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) = Real.sqrt (∑' j, g j ^ 2) := by
    rw [Real.sqrt_eq_rpow]; simp
  rw [← e1, ← e2]
  exact h.2

/-- The real pairing `Σ_j Re(conj a_j b_j)`. -/
def pair (a b : ℤ → ℂ) : ℝ := ∑' j, (conj (a j) * b j).re

theorem pair_summable (a b : ℤ → ℂ) (ha : Summable fun j => ‖a j‖ ^ 2) (hb : Summable fun j => ‖b j‖ ^ 2) :
    Summable fun j => (conj (a j) * b j).re := by
  have := (tsum_mul_le_sqrt (fun j => ‖a j‖) (fun j => ‖b j‖) (fun j => norm_nonneg _) (fun j => norm_nonneg _) ha hb).1
  refine Summable.of_norm_bounded this (fun j => ?_)
  calc ‖(conj (a j) * b j).re‖ ≤ ‖conj (a j) * b j‖ := Complex.abs_re_le_norm _
    _ = ‖a j‖ * ‖b j‖ := by rw [norm_mul, Complex.norm_conj]

theorem abs_pair_le (a b : ℤ → ℂ) (ha : Summable fun j => ‖a j‖ ^ 2) (hb : Summable fun j => ‖b j‖ ^ 2) :
    |pair a b| ≤ Real.sqrt (∑' j, ‖a j‖ ^ 2) * Real.sqrt (∑' j, ‖b j‖ ^ 2) := by
  obtain ⟨hs, hle⟩ := tsum_mul_le_sqrt (fun j => ‖a j‖) (fun j => ‖b j‖) (fun j => norm_nonneg _)
    (fun j => norm_nonneg _) ha hb
  have hps := pair_summable a b ha hb
  have hn : Summable fun j => ‖(conj (a j) * b j).re‖ := hps.norm
  calc |pair a b| = ‖∑' j, (conj (a j) * b j).re‖ := by rw [pair, Real.norm_eq_abs]
    _ ≤ ∑' j, ‖(conj (a j) * b j).re‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' j, ‖a j‖ * ‖b j‖ := by
        refine Summable.tsum_le_tsum (fun j => ?_) hn hs
        calc ‖(conj (a j) * b j).re‖ ≤ ‖conj (a j) * b j‖ := Complex.abs_re_le_norm _
          _ = ‖a j‖ * ‖b j‖ := by rw [norm_mul, Complex.norm_conj]
    _ ≤ _ := hle

theorem pair_sub_left (a a' b : ℤ → ℂ) (ha : Summable fun j => ‖a j‖ ^ 2) (ha' : Summable fun j => ‖a' j‖ ^ 2)
    (hb : Summable fun j => ‖b j‖ ^ 2) : pair (fun j => a j - a' j) b = pair a b - pair a' b := by
  unfold pair
  rw [← (pair_summable a b ha hb).tsum_sub (pair_summable a' b ha' hb)]
  congr 1; funext j
  simp [map_sub, sub_mul]

theorem pair_sub_right (a b b' : ℤ → ℂ) (ha : Summable fun j => ‖a j‖ ^ 2) (hb : Summable fun j => ‖b j‖ ^ 2)
    (hb' : Summable fun j => ‖b' j‖ ^ 2) : pair a (fun j => b j - b' j) = pair a b - pair a b' := by
  unfold pair
  rw [← (pair_summable a b ha hb).tsum_sub (pair_summable a b' ha hb')]
  congr 1; funext j
  simp [mul_sub]

theorem sq_sub_le (a b : ℂ) : ‖a - b‖ ^ 2 ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  have h := norm_sub_le a b
  have h2 : ‖a - b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

theorem summable_sq_sub {a b : ℤ → ℂ} (ha : Summable fun j => ‖a j‖ ^ 2) (hb : Summable fun j => ‖b j‖ ^ 2) :
    Summable fun j => ‖a j - b j‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (fun j => sq_nonneg _) (fun j => ?_) ((ha.add hb).mul_left 2)
  exact sq_sub_le (a j) (b j)

theorem summable_sq_seq (c : Cmp W U) (y : WSeq U) : Summable fun j => ‖y.val j‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (fun j => sq_nonneg _) (fun j => ?_) y.summable
  have h1 : 1 ≤ U.w j := by
    have := c.one_le j; have := c.sq_le j; nlinarith
  nlinarith [sq_nonneg ‖y.val j‖]

/-- Uniform `ℓ²`-continuity of the gradient on compact sets of `h(U)`. -/
theorem Gs_uniform (c : Cmp W U) (hF : ContDiff ℝ 2 F) (hinv : ∀ u z, F (rot u z) = F z)
    {K : Set (WSeq U)} (hK : IsCompact K) {η : ℝ} (hη : 0 < η) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ y ∈ K, ∀ y' ∈ K, ‖y - y'‖ < ρ →
      ∑' j, ‖Gs F c y j - Gs F c y' j‖ ^ 2 ≤ η := by
  obtain ⟨C, hC0, hC⟩ := Gs_bound c hF hinv hK
  set ε : ℝ := Real.sqrt (η / (8 * (C ^ 2 + 1))) with hε
  have hε0 : 0 < ε := Real.sqrt_pos.2 (by positivity)
  have hε2 : ε ^ 2 = η / (8 * (C ^ 2 + 1)) := Real.sq_sqrt (by positivity)
  obtain ⟨T, hT⟩ := exists_finset_tail_compact hK hε0
  -- head
  have hcont : Continuous fun y : WSeq U => (fun j : T => Gs F c y j) := by
    refine continuous_pi fun j => ?_
    exact (continuous_grad hF j.1).comp (iWU c).continuous
  obtain ⟨ρ, hρ, hρK⟩ := Metric.uniformContinuousOn_iff.1 (hK.uniformContinuousOn_of_continuous hcont.continuousOn)
    (Real.sqrt (η / (2 * (T.card + 1)))) (Real.sqrt_pos.2 (by positivity))
  refine ⟨ρ, hρ, fun y hy y' hy' hyy => ?_⟩
  have hd : dist y y' < ρ := by rwa [dist_eq_norm]
  have hhead := hρK y hy y' hy' hd
  have hhead_j : ∀ j ∈ T, ‖Gs F c y j - Gs F c y' j‖ ^ 2 ≤ η / (2 * (T.card + 1)) := by
    intro j hj
    have h1 : dist (Gs F c y j) (Gs F c y' j) ≤ dist (fun j : T => Gs F c y j) (fun j : T => Gs F c y' j) :=
      dist_le_pi_dist (fun j : T => Gs F c y j) (fun j : T => Gs F c y' j) ⟨j, hj⟩
    rw [dist_eq_norm] at h1
    have h2 : ‖Gs F c y j - Gs F c y' j‖ ≤ Real.sqrt (η / (2 * (T.card + 1))) :=
      h1.trans hhead.le
    calc ‖Gs F c y j - Gs F c y' j‖ ^ 2 ≤ (Real.sqrt (η / (2 * (T.card + 1)))) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h2 2
      _ = η / (2 * (T.card + 1)) := Real.sq_sqrt (by positivity)
  -- pointwise bound by an explicit summable majorant
  set g : ℤ → ℝ := fun j => (if j ∈ T then ‖Gs F c y j - Gs F c y' j‖ ^ 2 else 0) +
    2 * (C ^ 2 * (U.w j * ‖(tl T y).val j‖ ^ 2)) + 2 * (C ^ 2 * (U.w j * ‖(tl T y').val j‖ ^ 2)) with hg
  have hsy : Summable fun j => U.w j * ‖(tl T y).val j‖ ^ 2 := (tl T y).summable
  have hsy' : Summable fun j => U.w j * ‖(tl T y').val j‖ ^ 2 := (tl T y').summable
  have hghead : Summable fun j => if j ∈ T then ‖Gs F c y j - Gs F c y' j‖ ^ 2 else (0 : ℝ) :=
    summable_of_ne_finset_zero (s := T) (fun j hj => by simp [hj])
  have hgs : Summable g := (hghead.add (hsy.mul_left _ |>.mul_left 2)).add (hsy'.mul_left _ |>.mul_left 2)
  have hpt : ∀ j, ‖Gs F c y j - Gs F c y' j‖ ^ 2 ≤ g j := by
    intro j
    by_cases hj : j ∈ T
    · simp only [hg, hj, ite_true]
      have : 0 ≤ 2 * (C ^ 2 * (U.w j * ‖(tl T y).val j‖ ^ 2)) := by
        have := (U.pos j).le; positivity
      have : 0 ≤ 2 * (C ^ 2 * (U.w j * ‖(tl T y').val j‖ ^ 2)) := by
        have := (U.pos j).le; positivity
      linarith
    · simp only [hg, hj, ite_false, tl_val, zero_add]
      have h1 := Gs_sq_le c y j (hC y hy j)
      have h2 := Gs_sq_le c y' j (hC y' hy' j)
      have h3 := sq_sub_le (Gs F c y j) (Gs F c y' j)
      linarith
  have hlhs : Summable fun j => ‖Gs F c y j - Gs F c y' j‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun j => sq_nonneg _) hpt hgs
  have hsum := hlhs.tsum_le_tsum hpt hgs
  have e1 : ∑' j, (if j ∈ T then ‖Gs F c y j - Gs F c y' j‖ ^ 2 else (0 : ℝ)) =
      ∑ j ∈ T, ‖Gs F c y j - Gs F c y' j‖ ^ 2 := by
    rw [tsum_eq_sum (s := T) (fun j hj => by simp [hj])]
    exact Finset.sum_congr rfl fun j hj => by simp [hj]
  have e2 : ∑' j, g j = (∑ j ∈ T, ‖Gs F c y j - Gs F c y' j‖ ^ 2) +
      2 * (C ^ 2 * ‖tl T y‖ ^ 2) + 2 * (C ^ 2 * ‖tl T y'‖ ^ 2) := by
    simp only [hg]
    rw [(hghead.add (hsy.mul_left _ |>.mul_left 2)).tsum_add (hsy'.mul_left _ |>.mul_left 2),
      hghead.tsum_add (hsy.mul_left _ |>.mul_left 2), e1, tsum_mul_left, tsum_mul_left, tsum_mul_left,
      tsum_mul_left, ← norm_sq_eq_tsum, ← norm_sq_eq_tsum]
  have hH : ∑ j ∈ T, ‖Gs F c y j - Gs F c y' j‖ ^ 2 ≤ η / 2 := by
    calc ∑ j ∈ T, ‖Gs F c y j - Gs F c y' j‖ ^ 2 ≤ ∑ j ∈ T, η / (2 * (T.card + 1)) :=
          Finset.sum_le_sum hhead_j
      _ = T.card * (η / (2 * (T.card + 1))) := by simp
      _ ≤ η / 2 := by
          have hc0 : (0 : ℝ) ≤ T.card := Nat.cast_nonneg _
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
  have hty : ‖tl T y‖ ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hT y hy).le 2
  have hty' : ‖tl T y'‖ ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hT y' hy').le 2
  have hCε : C ^ 2 * ε ^ 2 ≤ η / 8 := by
    rw [hε2]
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg C]
  calc ∑' j, ‖Gs F c y j - Gs F c y' j‖ ^ 2 ≤ ∑' j, g j := hsum
    _ = _ := e2
    _ ≤ η / 2 + 2 * (C ^ 2 * ε ^ 2) + 2 * (C ^ 2 * ε ^ 2) := by
        gcongr
    _ ≤ η := by linarith
end Curve

section Deriv
variable {W U : PosWeight} {F : WSeq W → ℝ}

theorem hasDerivAt_seg (c : Cmp W U) (hF : ContDiff ℝ 2 F) (hinv : ∀ u z, F (rot u z) = F z)
    (y Δ : WSeq U) (τ : ℝ) :
    HasDerivAt (fun τ : ℝ => F (iWU c (y + τ • Δ))) (2 * pair (Gs F c (y + τ • Δ)) Δ.val) τ := by
  have hd : HasDerivAt (fun τ : ℝ => y + τ • Δ) Δ τ := by
    simpa using ((hasDerivAt_id τ).smul_const Δ).const_add y
  have h1 : HasDerivAt (fun τ : ℝ => iWU c (y + τ • Δ)) (iWU c Δ) τ :=
    ((iWU c).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt τ hd
  have hdiff : DifferentiableAt ℝ F (iWU c (y + τ • Δ)) := (hF.differentiable (by norm_num)) _
  have h2 : HasDerivAt (fun τ : ℝ => F (iWU c (y + τ • Δ))) (fderiv ℝ F (iWU c (y + τ • Δ)) (iWU c Δ)) τ :=
    hdiff.hasFDerivAt.comp_hasDerivAt τ h1
  have h3 := (hasSum_map (fderiv ℝ F (iWU c (y + τ • Δ))) (summable_Gs_div c hF hinv (y + τ • Δ))
    (iWU c Δ)).tsum_eq
  have h4 : fderiv ℝ F (iWU c (y + τ • Δ)) (iWU c Δ) = 2 * pair (Gs F c (y + τ • Δ)) Δ.val := by
    unfold pair Gs
    rw [show (iWU c Δ).val = Δ.val from rfl] at h3
    linarith
  rw [h4] at h2
  exact h2

theorem F_seg_bound (c : Cmp W U) (hF : ContDiff ℝ 2 F) (hinv : ∀ u z, F (rot u z) = F z)
    (y Δ : WSeq U) (M : ℝ)
    (hM : ∀ τ ∈ Icc (0 : ℝ) 1, |2 * pair (Gs F c (y + τ • Δ)) Δ.val - 2 * pair (Gs F c y) Δ.val| ≤ M) :
    |F (iWU c (y + Δ)) - F (iWU c y) - 2 * pair (Gs F c y) Δ.val| ≤ M := by
  set c1 : ℝ := 2 * pair (Gs F c y) Δ.val with hc1
  have hh : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (fun τ : ℝ => F (iWU c (y + τ • Δ)) - τ * c1)
      (2 * pair (Gs F c (y + x • Δ)) Δ.val - c1) (Icc (0 : ℝ) 1) x := by
    intro x _
    have h := (hasDerivAt_seg c hF hinv y Δ x).sub ((hasDerivAt_id x).mul_const c1)
    exact (h.congr_deriv (by simp)).hasDerivWithinAt
  have key := norm_image_sub_le_of_norm_deriv_le_segment' (a := 0) (b := 1) (C := M) hh
    (fun x hx => by rw [Real.norm_eq_abs]; exact hM x (Ico_subset_Icc_self hx)) 1 ⟨zero_le_one, le_rfl⟩
  simp only [one_smul, zero_smul, add_zero, zero_mul, sub_zero, one_mul, mul_one] at key
  rw [Real.norm_eq_abs] at key
  convert key using 2
  ring

theorem hasDerivAt_curve (c : Cmp W U) (hF : ContDiff ℝ 2 F) (hinv : ∀ u z, F (rot u z) = F z)
    (ζ : ℝ → WSeq U) (hζ : Continuous ζ) (d : ℤ → ℂ) (hd : Summable fun j => ‖d j‖ ^ 2)
    (hq : Tendsto (fun ε : ℝ => ∑' j, ‖(ζ ε - ζ 0).val j / (ε : ℂ) - d j‖ ^ 2) (𝓝[≠] 0) (𝓝 0)) :
    HasDerivAt (fun ε => F (iWU c (ζ ε))) (2 * pair (Gs F c (ζ 0)) d) 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero, Metric.tendsto_nhds]
  intro c0 hc0
  set G0 : ℤ → ℂ := Gs F c (ζ 0) with hG0
  have hG0s : Summable fun j => ‖G0 j‖ ^ 2 := summable_Gs_sq c hF hinv (ζ 0)
  set A0 : ℝ := ∑' j, ‖G0 j‖ ^ 2 with hA0
  set D : ℝ := ∑' j, ‖d j‖ ^ 2 with hD
  have hD0 : 0 ≤ D := tsum_nonneg fun j => sq_nonneg _
  have hA00 : 0 ≤ A0 := tsum_nonneg fun j => sq_nonneg _
  set s1 : ℝ := Real.sqrt (2 * (D + 1)) with hs1
  have hs1p : 0 < s1 := Real.sqrt_pos.2 (by positivity)
  set η : ℝ := (c0 / (8 * s1)) ^ 2 with hη
  have hηp : 0 < η := by positivity
  have hsη : Real.sqrt η = c0 / (8 * s1) := Real.sqrt_sq (by positivity)
  -- the compact set of segment points
  set K : Set (WSeq U) := (fun p : ℝ × ℝ => ζ 0 + p.2 • (ζ p.1 - ζ 0)) '' (Icc (-1 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
    with hK
  have hKc : IsCompact K := by
    refine (isCompact_Icc.prod isCompact_Icc).image ?_
    fun_prop
  obtain ⟨ρ, hρ, hρK⟩ := Gs_uniform c hF hinv hKc hηp
  set r0 : ℝ := min 1 ((c0 / (8 * (Real.sqrt A0 + 1))) ^ 2) with hr0
  have hr0p : 0 < r0 := lt_min one_pos (by positivity)
  have E1 : ∀ᶠ t in 𝓝 (0 : ℝ), |t| < 1 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with t ht
    rwa [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
  have E2 : ∀ᶠ t in 𝓝 (0 : ℝ), ‖ζ t - ζ 0‖ < ρ := by
    have := hζ.continuousAt (x := 0)
    filter_upwards [this.preimage_mem_nhds (Metric.ball_mem_nhds (ζ 0) hρ)] with t ht
    rwa [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at ht
  have E3 : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ∑' j, ‖(ζ t - ζ 0).val j / (t : ℂ) - d j‖ ^ 2 < r0 :=
    hq.eventually (gt_mem_nhds hr0p)
  filter_upwards [nhdsWithin_le_nhds E1, nhdsWithin_le_nhds E2, E3, self_mem_nhdsWithin]
    with t ht1 ht2 ht3 ht0
  have ht0' : t ≠ 0 := ht0
  set Δ : WSeq U := ζ t - ζ 0 with hΔ
  set R : ℝ := ∑' j, ‖Δ.val j / (t : ℂ) - d j‖ ^ 2 with hR
  have hR0 : 0 ≤ R := tsum_nonneg fun j => sq_nonneg _
  have hΔs : Summable fun j => ‖Δ.val j‖ ^ 2 := summable_sq_seq c Δ
  have hrs : Summable fun j => ‖Δ.val j / (t : ℂ) - d j‖ ^ 2 := by
    have h1 : Summable fun j => ‖Δ.val j / (t : ℂ)‖ ^ 2 := by
      refine (hΔs.mul_left (‖(t : ℂ)‖⁻¹ ^ 2)).congr (fun j => ?_)
      rw [norm_div, div_pow]; ring
    exact summable_sq_sub h1 hd
  -- the identity Δ_j = t (Δ_j / t)
  have hΔd : ∀ j, Δ.val j - (t : ℂ) * d j = (t : ℂ) * (Δ.val j / (t : ℂ) - d j) := by
    intro j
    have : (t : ℂ) ≠ 0 := by exact_mod_cast ht0'
    field_simp
  -- size of Δ
  have hB : ∑' j, ‖Δ.val j‖ ^ 2 ≤ 2 * t ^ 2 * (D + 1) := by
    have hpt : ∀ j, ‖Δ.val j‖ ^ 2 ≤ 2 * t ^ 2 * (‖d j‖ ^ 2 + ‖Δ.val j / (t : ℂ) - d j‖ ^ 2) := by
      intro j
      have e : Δ.val j = (t : ℂ) * d j + (t : ℂ) * (Δ.val j / (t : ℂ) - d j) := by
        rw [← hΔd j]; ring
      have h1 : ‖Δ.val j‖ ≤ |t| * ‖d j‖ + |t| * ‖Δ.val j / (t : ℂ) - d j‖ := by
        calc ‖Δ.val j‖ = ‖(t : ℂ) * d j + (t : ℂ) * (Δ.val j / (t : ℂ) - d j)‖ := by rw [← e]
          _ ≤ ‖(t : ℂ) * d j‖ + ‖(t : ℂ) * (Δ.val j / (t : ℂ) - d j)‖ := norm_add_le _ _
          _ = _ := by rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h2 : ‖Δ.val j‖ ^ 2 ≤ (|t| * ‖d j‖ + |t| * ‖Δ.val j / (t : ℂ) - d j‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
      have h3 : (|t| * ‖d j‖ + |t| * ‖Δ.val j / (t : ℂ) - d j‖) ^ 2 ≤
          2 * t ^ 2 * (‖d j‖ ^ 2 + ‖Δ.val j / (t : ℂ) - d j‖ ^ 2) := by
        have := sq_abs t
        nlinarith [sq_nonneg (|t| * ‖d j‖ - |t| * ‖Δ.val j / (t : ℂ) - d j‖)]
      exact h2.trans h3
    calc ∑' j, ‖Δ.val j‖ ^ 2 ≤ ∑' j, 2 * t ^ 2 * (‖d j‖ ^ 2 + ‖Δ.val j / (t : ℂ) - d j‖ ^ 2) :=
          hΔs.tsum_le_tsum hpt ((hd.add hrs).mul_left _)
      _ = 2 * t ^ 2 * (D + R) := by rw [tsum_mul_left, hd.tsum_add hrs]
      _ ≤ 2 * t ^ 2 * (D + 1) := by
          have : R ≤ 1 := by
            have := ht3; have := min_le_left (1 : ℝ) ((c0 / (8 * (Real.sqrt A0 + 1))) ^ 2)
            simp only [hR, hr0] at *; linarith
          gcongr
  have hsB : Real.sqrt (∑' j, ‖Δ.val j‖ ^ 2) ≤ |t| * s1 := by
    calc Real.sqrt (∑' j, ‖Δ.val j‖ ^ 2) ≤ Real.sqrt (2 * t ^ 2 * (D + 1)) := Real.sqrt_le_sqrt hB
      _ = |t| * s1 := by
          rw [show 2 * t ^ 2 * (D + 1) = t ^ 2 * (2 * (D + 1)) by ring, Real.sqrt_mul (sq_nonneg t),
            Real.sqrt_sq_eq_abs]
  -- the segment bound
  have hseg : ∀ τ ∈ Icc (0 : ℝ) 1,
      |2 * pair (Gs F c (ζ 0 + τ • Δ)) Δ.val - 2 * pair G0 Δ.val| ≤ 2 * (Real.sqrt η * (|t| * s1)) := by
    intro τ hτ
    have hmem : ζ 0 + τ • Δ ∈ K := ⟨(t, τ), ⟨⟨by linarith [(abs_lt.1 ht1).1], by linarith [(abs_lt.1 ht1).2]⟩, hτ⟩, rfl⟩
    have hmem0 : ζ 0 ∈ K := ⟨(0, 0), ⟨⟨by norm_num, by norm_num⟩, ⟨le_rfl, zero_le_one⟩⟩, by simp⟩
    have hdist : ‖(ζ 0 + τ • Δ) - ζ 0‖ < ρ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ.1]
      calc τ * ‖Δ‖ ≤ 1 * ‖Δ‖ := by gcongr; exact hτ.2
        _ < ρ := by rw [one_mul]; exact ht2
    have hηle := hρK _ hmem _ hmem0 hdist
    have hs1' := summable_Gs_sq c hF hinv (ζ 0 + τ • Δ)
    have hdiff : Summable fun j => ‖Gs F c (ζ 0 + τ • Δ) j - G0 j‖ ^ 2 := summable_sq_sub hs1' hG0s
    have hpl := pair_sub_left (Gs F c (ζ 0 + τ • Δ)) G0 Δ.val hs1' hG0s hΔs
    have : 2 * pair (Gs F c (ζ 0 + τ • Δ)) Δ.val - 2 * pair G0 Δ.val =
        2 * pair (fun j => Gs F c (ζ 0 + τ • Δ) j - G0 j) Δ.val := by rw [hpl]; ring
    rw [this, abs_mul, abs_two]
    have hcs := abs_pair_le (fun j => Gs F c (ζ 0 + τ • Δ) j - G0 j) Δ.val hdiff hΔs
    have h1 : Real.sqrt (∑' j, ‖Gs F c (ζ 0 + τ • Δ) j - G0 j‖ ^ 2) ≤ Real.sqrt η := Real.sqrt_le_sqrt hηle
    calc 2 * |pair (fun j => Gs F c (ζ 0 + τ • Δ) j - G0 j) Δ.val|
        ≤ 2 * (Real.sqrt (∑' j, ‖Gs F c (ζ 0 + τ • Δ) j - G0 j‖ ^ 2) * Real.sqrt (∑' j, ‖Δ.val j‖ ^ 2)) := by
          gcongr
      _ ≤ 2 * (Real.sqrt η * (|t| * s1)) := by gcongr
  have hF1 := F_seg_bound c hF hinv (ζ 0) Δ _ hseg
  have hζΔ : ζ 0 + Δ = ζ t := by
    rw [hΔ]
    abel
  rw [hζΔ] at hF1
  -- the remaining term
  have hrem : |2 * pair G0 Δ.val - t * (2 * pair G0 d)| ≤ 2 * (|t| * (Real.sqrt A0 * Real.sqrt R)) := by
    have hdt : Summable fun j => ‖(t : ℂ) * d j‖ ^ 2 := by
      refine (hd.mul_left (‖(t : ℂ)‖ ^ 2)).congr (fun j => ?_)
      rw [norm_mul, mul_pow]
    have h1 : pair G0 (fun j => Δ.val j - (t : ℂ) * d j) = pair G0 Δ.val - t * pair G0 d := by
      rw [pair_sub_right G0 Δ.val (fun j => (t : ℂ) * d j) hG0s hΔs hdt]
      congr 1
      unfold pair
      rw [← tsum_mul_left]
      congr 1; funext j
      simp
      ring
    have h2 : pair G0 (fun j => Δ.val j - (t : ℂ) * d j) = t * pair G0 (fun j => Δ.val j / (t : ℂ) - d j) := by
      unfold pair
      rw [← tsum_mul_left]
      congr 1; funext j
      show (conj (G0 j) * (Δ.val j - (t : ℂ) * d j)).re = t * (conj (G0 j) * (Δ.val j / (t : ℂ) - d j)).re
      rw [hΔd j, mul_left_comm, Complex.re_ofReal_mul]
    have h3 := abs_pair_le G0 (fun j => Δ.val j / (t : ℂ) - d j) hG0s hrs
    have e : 2 * pair G0 Δ.val - t * (2 * pair G0 d) = 2 * (t * pair G0 (fun j => Δ.val j / (t : ℂ) - d j)) := by
      rw [← h2, h1]; ring
    rw [e, abs_mul, abs_two, abs_mul]
    have h4 : |t| * |pair G0 (fun j => Δ.val j / (t : ℂ) - d j)| ≤ |t| * (Real.sqrt A0 * Real.sqrt R) :=
      mul_le_mul_of_nonneg_left h3 (abs_nonneg t)
    linarith
  -- conclude
  have hsR : Real.sqrt R ≤ c0 / (8 * (Real.sqrt A0 + 1)) := by
    have : R ≤ (c0 / (8 * (Real.sqrt A0 + 1))) ^ 2 := by
      have := ht3; have := min_le_right (1 : ℝ) ((c0 / (8 * (Real.sqrt A0 + 1))) ^ 2)
      simp only [hR, hr0] at *; linarith
    calc Real.sqrt R ≤ Real.sqrt ((c0 / (8 * (Real.sqrt A0 + 1))) ^ 2) := Real.sqrt_le_sqrt this
      _ = _ := Real.sqrt_sq (by positivity)
  have hA1 : Real.sqrt A0 * Real.sqrt R ≤ c0 / 8 := by
    calc Real.sqrt A0 * Real.sqrt R ≤ Real.sqrt A0 * (c0 / (8 * (Real.sqrt A0 + 1))) := by gcongr
      _ ≤ c0 / 8 := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [Real.sqrt_nonneg A0]
  have hB1 : Real.sqrt η * (|t| * s1) = c0 / 8 * |t| := by
    rw [hsη, div_mul_eq_mul_div, div_eq_iff (by positivity)]
    ring
  have hfin : |F (iWU c (ζ t)) - F (iWU c (ζ 0)) - t * (2 * pair G0 d)| ≤ c0 / 2 * |t| := by
    have : F (iWU c (ζ t)) - F (iWU c (ζ 0)) - t * (2 * pair G0 d) =
        (F (iWU c (ζ t)) - F (iWU c (ζ 0)) - 2 * pair G0 Δ.val) + (2 * pair G0 Δ.val - t * (2 * pair G0 d)) := by ring
    rw [this]
    calc _ ≤ |F (iWU c (ζ t)) - F (iWU c (ζ 0)) - 2 * pair G0 Δ.val| + |2 * pair G0 Δ.val - t * (2 * pair G0 d)| :=
          abs_add_le _ _
      _ ≤ 2 * (Real.sqrt η * (|t| * s1)) + 2 * (|t| * (Real.sqrt A0 * Real.sqrt R)) := add_le_add hF1 hrem
      _ ≤ 2 * (c0 / 8 * |t|) + 2 * (|t| * (c0 / 8)) := by
          rw [hB1]; gcongr
      _ = c0 / 2 * |t| := by ring
  have hlast : t⁻¹ • (F (iWU c (ζ (0 + t))) - F (iWU c (ζ 0))) - 2 * pair G0 d =
      t⁻¹ * (F (iWU c (ζ t)) - F (iWU c (ζ 0)) - t * (2 * pair G0 d)) := by
    simp only [zero_add, smul_eq_mul]
    have h5 : t⁻¹ * (t * (2 * pair G0 d)) = 2 * pair G0 d := by
      rw [← mul_assoc, inv_mul_cancel₀ ht0', one_mul]
    linear_combination h5
  have hlt : |t⁻¹ * (F (iWU c (ζ t)) - F (iWU c (ζ 0)) - t * (2 * pair G0 d))| < c0 := by
    rw [abs_mul, abs_inv]
    have hta : 0 < |t| := abs_pos.2 ht0'
    calc |t|⁻¹ * |F (iWU c (ζ t)) - F (iWU c (ζ 0)) - t * (2 * pair G0 d)|
        ≤ |t|⁻¹ * (c0 / 2 * |t|) := by gcongr
      _ = c0 / 2 := by rw [mul_comm (c0 / 2) |t|, ← mul_assoc, inv_mul_cancel₀ hta.ne', one_mul]
      _ < c0 := by linarith
  rw [Real.dist_eq, hlast]
  exact hlt

end Deriv

end QuantumNLS.RB7

#print axioms QuantumNLS.RB7.grad_bound_compact
#print axioms QuantumNLS.RB7.Gs_uniform
#print axioms QuantumNLS.RB7.hasDerivAt_curve
