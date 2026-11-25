import Mathlib

/-!
# DEF-017 C2, stage A: complex-differentiable maps on complex Banach spaces are `C¹` (Cauchy estimates on slices)

For `f : E → F` (complex normed spaces, `F` complete) `DifferentiableOn ℂ f U`, `U` open:
* `hasDerivAt_line`: the slice `s ↦ f (y + s • v)` has derivative `fderiv ℂ f y v` at `0`;
* `norm_fderiv_apply_le`: a local bound `‖f‖ ≤ K` on `ball y δ` gives `‖fderiv ℂ f y v‖ ≤ 2K/δ · ‖v‖` (one-variable
  Cauchy estimate on the slice, `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`);
* `exists_local_bound`, `exists_uniform_fderiv_bound`: local boundedness of `f` and of `fderiv ℂ f` near each point;
* `fderiv_lipschitz_near`: `fderiv ℂ f` is Lipschitz (in operator norm) near each point (mean value inequality plus the
  Cauchy estimate applied to the difference of two slices);
* `contDiffOn_one_of_differentiableOn`: `ContDiffOn ℂ 1 f U`.

This is stage A only. Higher smoothness (`ContDiffOn ℂ ⊤`) and the power series are later stages.
-/

set_option autoImplicit false
noncomputable section
open Filter Topology Metric Complex

namespace QuantumNLS.HolomorphicCauchyC1

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

theorem hasDerivAt_line {f : E → F} {y : E} (hf : DifferentiableAt ℂ f y) (v : E) :
    HasDerivAt (fun s : ℂ => f (y + s • v)) (fderiv ℂ f y v) 0 := by
  have hl : HasDerivAt (fun s : ℂ => y + s • v) v 0 := by
    have := ((hasDerivAt_id' (0 : ℂ)).smul_const v).const_add y
    simpa using this
  have hf0 : HasFDerivAt f (fderiv ℂ f y) (y + (0 : ℂ) • v) := by
    rw [zero_smul, add_zero]
    exact hf.hasFDerivAt
  exact hf0.comp_hasDerivAt (0 : ℂ) hl

theorem norm_fderiv_apply_le {U : Set E} {f : E → F} (hf : DifferentiableOn ℂ f U) {y : E} {δ K : ℝ}
    (hδ : 0 < δ) (hball : ball y δ ⊆ U) (hK : ∀ z ∈ ball y δ, ‖f z‖ ≤ K) (v : E) :
    ‖fderiv ℂ f y v‖ ≤ 2 * K / δ * ‖v‖ := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv
  set ρ : ℝ := δ / (2 * ‖v‖) with hρ
  have hρpos : 0 < ρ := div_pos hδ (by positivity)
  have hρv : ρ * ‖v‖ = δ / 2 := by
    rw [hρ]
    field_simp
  have hfb : DifferentiableOn ℂ f (ball y δ) := hf.mono hball
  have hline : ∀ t : ℂ, ‖t‖ ≤ ρ → y + t • v ∈ ball y δ := by
    intro t ht
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
    have h1 : ‖t‖ * ‖v‖ ≤ ρ * ‖v‖ := mul_le_mul_of_nonneg_right ht hvpos.le
    rw [hρv] at h1
    linarith
  have hdiffAt : ∀ t : ℂ, ‖t‖ ≤ ρ → DifferentiableAt ℂ (fun s : ℂ => f (y + s • v)) t := by
    intro t ht
    have h1 : DifferentiableAt ℂ f (y + t • v) :=
      hfb.differentiableAt (isOpen_ball.mem_nhds (hline t ht))
    have h2 : DifferentiableAt ℂ (fun s : ℂ => y + s • v) t := by fun_prop
    exact h1.comp t h2
  have hdiffOn : DifferentiableOn ℂ (fun s : ℂ => f (y + s • v)) (closedBall 0 ρ) := by
    intro t ht
    rw [mem_closedBall_zero_iff] at ht
    exact (hdiffAt t ht).differentiableWithinAt
  have hd : DiffContOnCl ℂ (fun s : ℂ => f (y + s • v)) (ball (0 : ℂ) ρ) :=
    (hdiffOn.mono closure_ball_subset_closedBall).diffContOnCl
  have hy0 : DifferentiableAt ℂ f y := hfb.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hδ))
  have hderiv : deriv (fun s : ℂ => f (y + s • v)) 0 = fderiv ℂ f y v :=
    (hasDerivAt_line hy0 v).deriv
  have hbound := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρpos hd (C := K) (by
    intro s hs
    rw [mem_sphere_zero_iff_norm] at hs
    exact hK _ (hline s (le_of_eq hs)))
  rw [← hderiv]
  calc ‖deriv (fun s : ℂ => f (y + s • v)) 0‖ ≤ K / ρ := hbound
    _ = 2 * K / δ * ‖v‖ := by
      rw [hρ]
      field_simp

theorem exists_local_bound {U : Set E} (hU : IsOpen U) {f : E → F} (hf : DifferentiableOn ℂ f U) {y : E}
    (hy : y ∈ U) :
    ∃ δ > 0, ball y δ ⊆ U ∧ ∃ K : ℝ, ∀ z ∈ ball y δ, ‖f z‖ ≤ K := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU y hy
  have hcont : ContinuousAt f y := (hf.differentiableAt (hU.mem_nhds hy)).continuousAt
  obtain ⟨δ1, hδ1, hδ1f⟩ := Metric.continuousAt_iff.1 hcont 1 one_pos
  refine ⟨min δ1 ε, lt_min hδ1 hε, (Metric.ball_subset_ball (min_le_right _ _)).trans hεU,
    ‖f y‖ + 1, fun z hz => ?_⟩
  have hzd : dist z y < δ1 := lt_of_lt_of_le (Metric.mem_ball.1 hz) (min_le_left _ _)
  have h := hδ1f hzd
  rw [dist_eq_norm] at h
  have := norm_sub_norm_le (f z) (f y)
  linarith

theorem exists_uniform_fderiv_bound {U : Set E} (hU : IsOpen U) {f : E → F} (hf : DifferentiableOn ℂ f U)
    {y : E} (hy : y ∈ U) :
    ∃ δ > 0, ball y δ ⊆ U ∧ ∃ K' : ℝ, 0 ≤ K' ∧ ∀ z ∈ ball y δ, ∀ v : E, ‖fderiv ℂ f z v‖ ≤ K' * ‖v‖ := by
  obtain ⟨δ, hδ, hball, K, hK⟩ := exists_local_bound hU hf hy
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK y (mem_ball_self hδ))
  refine ⟨δ / 2, half_pos hδ, (Metric.ball_subset_ball (by linarith)).trans hball, 4 * K / δ,
    by positivity, fun z hz v => ?_⟩
  have hzd : dist z y < δ / 2 := Metric.mem_ball.1 hz
  have hsub : ball z (δ / 2) ⊆ ball y δ := Metric.ball_subset_ball' (by linarith)
  have h := norm_fderiv_apply_le hf (half_pos hδ) (hsub.trans ?_) (fun w hw => hK w (hsub hw)) v
  · calc ‖fderiv ℂ f z v‖ ≤ 2 * K / (δ / 2) * ‖v‖ := h
      _ = 4 * K / δ * ‖v‖ := by
        field_simp
        ring
  · exact hball


theorem fderiv_lipschitz_near {U : Set E} (hU : IsOpen U) {f : E → F} (hf : DifferentiableOn ℂ f U) {y : E}
    (hy : y ∈ U) :
    ∃ D > 0, ∃ L : ℝ, 0 ≤ L ∧ ∀ z ∈ ball y (D / 4), ∀ w ∈ ball y (D / 4),
      ‖fderiv ℂ f z - fderiv ℂ f w‖ ≤ L * ‖z - w‖ := by
  obtain ⟨D, hD, hDU, K', hK'0, hfd⟩ := exists_uniform_fderiv_bound hU hf hy
  refine ⟨D, hD, 8 * K' / D, div_nonneg (by linarith) hD.le, fun z hz w hw => ?_⟩
  have hzD : z ∈ ball y D := Metric.ball_subset_ball (by linarith) hz
  have hwD : w ∈ ball y D := Metric.ball_subset_ball (by linarith) hw
  have hfy : ∀ x ∈ ball y D, DifferentiableAt ℂ f x := fun x hx =>
    hf.differentiableAt (hU.mem_nhds (hDU hx))
  have hR : ∀ x ∈ ball y D, HasFDerivWithinAt f ((fderiv ℂ f x).restrictScalars ℝ) (ball y D) x :=
    fun x hx => (((hfy x hx).hasFDerivAt).restrictScalars ℝ).hasFDerivWithinAt
  have hbnd : ∀ x ∈ ball y D, ‖(fderiv ℂ f x).restrictScalars ℝ‖ ≤ K' := by
    intro x hx
    refine ContinuousLinearMap.opNorm_le_bound _ hK'0 (fun v => ?_)
    have := hfd x hx v
    simpa using this
  have hmv : ∀ a ∈ ball y D, ∀ b ∈ ball y D, ‖f b - f a‖ ≤ K' * ‖b - a‖ := fun a ha b hb =>
    (convex_ball y D).norm_image_sub_le_of_norm_hasFDerivWithin_le hR hbnd ha hb
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (div_nonneg (by linarith) hD.le) (norm_nonneg _))
    (fun v => ?_)
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv
  set ρ : ℝ := (D / 8) / ‖v‖ with hρ
  have hρpos : 0 < ρ := div_pos (by linarith) hvpos
  have hρv : ρ * ‖v‖ = D / 8 := by
    rw [hρ]
    field_simp
  have hpt : ∀ x ∈ ball y (D / 4), ∀ s : ℂ, ‖s‖ ≤ ρ → x + s • v ∈ ball y D := by
    intro x hx s hs
    rw [Metric.mem_ball] at hx ⊢
    have h1 : ‖s • v‖ ≤ D / 8 := by
      rw [norm_smul]
      have := mul_le_mul_of_nonneg_right hs hvpos.le
      linarith [hρv]
    have h2 : dist (x + s • v) y ≤ dist x y + ‖s • v‖ := by
      rw [dist_eq_norm, dist_eq_norm]
      calc ‖x + s • v - y‖ = ‖(x - y) + s • v‖ := by congr 1; abel
        _ ≤ ‖x - y‖ + ‖s • v‖ := norm_add_le _ _
    linarith
  have hdiffAt : ∀ x ∈ ball y (D / 4), ∀ s : ℂ, ‖s‖ ≤ ρ →
      DifferentiableAt ℂ (fun t : ℂ => f (x + t • v)) s := by
    intro x hx s hs
    have h1 : DifferentiableAt ℂ f (x + s • v) := hfy _ (hpt x hx s hs)
    have h2 : DifferentiableAt ℂ (fun t : ℂ => x + t • v) s := by fun_prop
    exact h1.comp s h2
  set φ : ℂ → F := fun s => f (z + s • v) - f (w + s • v) with hφ
  have hφd : ∀ s : ℂ, ‖s‖ ≤ ρ → DifferentiableAt ℂ φ s := fun s hs =>
    (hdiffAt z (Metric.ball_subset_ball (by linarith) hz) s hs).sub
      (hdiffAt w (Metric.ball_subset_ball (by linarith) hw) s hs)
  have hdiffOn : DifferentiableOn ℂ φ (closedBall 0 ρ) := by
    intro s hs
    rw [mem_closedBall_zero_iff] at hs
    exact (hφd s hs).differentiableWithinAt
  have hd : DiffContOnCl ℂ φ (ball (0 : ℂ) ρ) :=
    (hdiffOn.mono closure_ball_subset_closedBall).diffContOnCl
  have hbound := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρpos hd (C := K' * ‖z - w‖) (by
    intro s hs
    rw [mem_sphere_zero_iff_norm] at hs
    have hsl := hmv (w + s • v) (hpt w hw s (le_of_eq hs)) (z + s • v) (hpt z hz s (le_of_eq hs))
    rw [add_sub_add_right_eq_sub] at hsl
    exact hsl)
  have hφ0 : HasDerivAt φ (fderiv ℂ f z v - fderiv ℂ f w v) 0 :=
    (hasDerivAt_line (hfy z hzD) v).sub (hasDerivAt_line (hfy w hwD) v)
  have hderiv : deriv φ 0 = fderiv ℂ f z v - fderiv ℂ f w v := hφ0.deriv
  rw [ContinuousLinearMap.sub_apply, ← hderiv]
  calc ‖deriv φ 0‖ ≤ K' * ‖z - w‖ / ρ := hbound
    _ = 8 * K' / D * ‖z - w‖ * ‖v‖ := by
      rw [hρ]
      field_simp

theorem contDiffOn_one_of_differentiableOn {U : Set E} (hU : IsOpen U) {f : E → F}
    (hf : DifferentiableOn ℂ f U) : ContDiffOn ℂ 1 f U := by
  have hcont : ContinuousOn (fun x => fderiv ℂ f x) U := by
    intro y hy
    apply ContinuousAt.continuousWithinAt
    obtain ⟨D, hD, L, hL0, hLip⟩ := fderiv_lipschitz_near hU hf hy
    rw [Metric.continuousAt_iff]
    intro ε hε
    refine ⟨min (D / 4) (ε / (L + 1)), lt_min (by linarith) (div_pos hε (by linarith)), fun {x} hx => ?_⟩
    have hxD : x ∈ ball y (D / 4) := Metric.mem_ball.2 (lt_of_lt_of_le hx (min_le_left _ _))
    have hyD : y ∈ ball y (D / 4) := mem_ball_self (by linarith)
    have h1 := hLip x hxD y hyD
    have h2 : dist x y < ε / (L + 1) := lt_of_lt_of_le hx (min_le_right _ _)
    rw [lt_div_iff₀ (by linarith)] at h2
    rw [dist_eq_norm]
    calc ‖fderiv ℂ f x - fderiv ℂ f y‖ ≤ L * ‖x - y‖ := h1
      _ = L * dist x y := by rw [dist_eq_norm]
      _ < ε := by nlinarith [dist_nonneg (x := x) (y := y)]
  have key := (contDiffOn_succ_iff_fderiv_of_isOpen (𝕜 := ℂ) (n := 0) (f := f) (s := U) hU).2
    ⟨hf, fun h => absurd h (by simp), contDiffOn_zero.2 hcont⟩
  exact key

end QuantumNLS.HolomorphicCauchyC1

#print axioms QuantumNLS.HolomorphicCauchyC1.exists_uniform_fderiv_bound
