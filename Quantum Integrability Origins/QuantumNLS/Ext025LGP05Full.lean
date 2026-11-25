import QuantumNLS.Ext025LGP05

/-!
# EXT-025 layer A (completion): FULL contract theorem for FIN-EXT025-GP-05

This module COMPLETES the frozen `Ext025LGP05` (sha256 f546c9c42cc6ca0eea5ae65bf7bd0d13ea3546e42e3e6744ad803450f1f7eed1,
not edited) by the one clause that module left open: bounded integration with a BANACH-DOMAIN
parameter.  It imports `Ext025LGP05` and re-uses its (frozen) clause statements.

Exact source text (FINAL_EXTERNAL_THEOREM_INSTANCES.json, sha256
82876b0400535292c74c814f70269d4dea6778fb05d4d3066b73e8a3d0d13782, instance
`FIN-EXT025-GP-05`, "Banach-valued Cauchy bounds and normally convergent holomorphic families"):

* Hypotheses: "A Banach-valued function is complex differentiable on a complex disk
  neighborhood and is bounded on a fixed enclosing circle. For parameters in a Banach domain
  the circle lies on a complex line inside a fixed common neighborhood." and "For a family or
  series the circle bounds are uniform, or summable in the indicated target Banach norm."
* Conclusion: "Cauchy integration gives derivative bounds and preserves holomorphy under
  locally uniform limits, sums and bounded integration. Polarization on a smaller ball yields
  bounded multilinear derivative coefficients."
* Normalization: "Shrinking the neighborhood is part of every derivative claim."
* application_wrapper (second item): "For the scalar Haar average of covectors, evaluate
  coefficients on fixed tangent vectors, integrate their scalar values, and use the uniform
  Cauchy/polarization bounds to recover a norm-convergent dual-valued series. No Bochner
  measurability in the operator-norm space is assumed."

Clause map of `contract_GP05_full` (every clause of the printed conclusion):
* "Cauchy integration gives derivative bounds" = `GP05_one` (one complex variable, Banach
  target, all orders), `GP05_banach` (Banach domain: bound on the closed ball from the bound on
  the circle (sphere) by the maximum principle on complex lines, full Frechet Cauchy bounds for
  all orders), `GP05_series_bounds` (summable circle bounds => term-wise and sum derivative
  bounds).
* "preserves holomorphy under locally uniform limits" = `GP05_limit` (limits uniform on a
  neighbourhood of each point, the notion of local uniformity for Banach domains),
  "sums" = `GP05_sum`, "bounded integration" = `GP05_int` (scalar parameter in `C`) AND
  `GP05_int_banach` (NEW, parameter in a Banach domain; see below).
* "Polarization on a smaller ball yields bounded multilinear derivative coefficients" =
  the multilinear power series part of `GP05_banach`.

The NEW clause `GP05_int_banach` (Frechet differentiation under the integral with an
operator-valued derivative).  Data: `E` a complex normed space (NOT assumed complete, NOT
assumed separable), `F` a complex Banach space, `(T, mu)` an arbitrary measure space,
`Phi : E -> T -> F`, `U ⊆ E` open, `b : T -> R` integrable.  Hypotheses: `Phi w` is a.e.
strongly measurable for every `w ∈ U` (this is ALL the measurability assumed: nothing about the
operator-norm space), and for a.e. `t`, `w ↦ Phi w t` is complex differentiable on `U` with
`‖Phi w t‖ ≤ b t` on `U`.  Conclusions: `w ↦ ∫ Phi w t dmu` is complex differentiable on `U`,
analytic at every point of `U` (this uses the frozen `HolomorphicStageD3` and so needs `E`, `F`
in one universe), and, for every `w ∈ U` and tangent vector `v`, the vector function
`t ↦ D_t v` (where `D_t = fderiv C (Phi · t) w`) is integrable and
`fderiv C (∫ Phi · dmu) w v = ∫ D_t v dmu`: the derivative of the integral is the integral of
the derivatives, evaluated on fixed tangent vectors (so no Bochner integral of the
operator-valued map `t ↦ D_t` is ever formed).

Proof (Taylor remainder with a measurable family of difference quotients).
* `taylor_one`: for `f` holomorphic on `ball 0 3` with `‖f‖ ≤ B` there: `‖f'(0)‖ ≤ B` and
  `‖f z - f 0 - z f'(0)‖ ≤ 2 B ‖z‖²` for `‖z‖ ≤ 1` (Cauchy estimates for `f'` and `f''` and two
  applications of the mean value inequality).
* `pointwise_taylor`: the Banach-domain consequence on a line through `w0`: `‖D v‖ ≤ (3B/r)‖v‖`
  and `‖phi (w0+v) - phi w0 - D v‖ ≤ 18 B ‖v‖²/r²` for `‖v‖ ≤ r/3`.
* measurability: `t ↦ D_t v` is an a.e. limit of the measurable difference quotients
  `(s_n)^{-1} (Phi (w0 + s_n v) t - Phi w0 t)`, `s_n → 0`; hence a.e. strongly measurable.
* `L v := ∫ D_t v` is a bounded linear map; the remainder estimate gives
  `‖∫ Phi (w0+h) - ∫ Phi w0 - L h‖ ≤ C ‖h‖²` for small `h`, hence the Frechet derivative.
No admitted interface, no held identifier, no extra axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 3200000
noncomputable section
open Set Filter Topology Metric MeasureTheory
open scoped ENNReal NNReal

namespace QuantumNLS.Ext025L

universe u v w

/-- Cauchy estimate for the derivative from a bound on a closed disk. -/
theorem cauchy_deriv_le {F : Type v} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {f : ℂ → F} {c : ℂ} {R B : ℝ} (hR : 0 < R)
    (hd : DifferentiableOn ℂ f (closedBall c R)) (hB : ∀ z ∈ sphere c R, ‖f z‖ ≤ B) :
    ‖deriv f c‖ ≤ B / R := by
  have hdcl : DiffContOnCl ℂ f (ball c R) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball c hR.ne']
    exact hd
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hdcl hB

/-- One-variable Taylor remainder with second order decay. -/
theorem taylor_one {F : Type v} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (f : ℂ → F) (B : ℝ) (hd : DifferentiableOn ℂ f (ball (0 : ℂ) 3))
    (hB : ∀ z ∈ ball (0 : ℂ) 3, ‖f z‖ ≤ B) :
    ‖deriv f 0‖ ≤ B ∧ ∀ z : ℂ, ‖z‖ ≤ 1 → ‖f z - f 0 - z • deriv f 0‖ ≤ 2 * B * ‖z‖ ^ 2 := by
  have hU : IsOpen (ball (0 : ℂ) 3) := isOpen_ball
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (by simp))
  have hψ : ∀ z ∈ closedBall (0 : ℂ) (3 / 2), ‖deriv f z‖ ≤ B := by
    intro z hz
    have hz' : ‖z‖ ≤ 3 / 2 := by simpa using hz
    have hsub : closedBall z 1 ⊆ ball (0 : ℂ) 3 := by
      intro y hy
      rw [mem_closedBall] at hy
      rw [mem_ball_zero_iff]
      have h1 : ‖y‖ ≤ ‖z‖ + ‖y - z‖ := by
        calc ‖y‖ = ‖z + (y - z)‖ := by rw [add_sub_cancel]
          _ ≤ ‖z‖ + ‖y - z‖ := norm_add_le _ _
      rw [dist_eq_norm] at hy
      linarith
    have := cauchy_deriv_le (f := f) (c := z) (R := 1) (B := B) one_pos (hd.mono hsub)
      (fun y hy => hB y (hsub (sphere_subset_closedBall hy)))
    simpa using this
  refine ⟨by simpa using hψ 0 (mem_closedBall_self (by norm_num)), ?_⟩
  have hψd : DifferentiableOn ℂ (deriv f) (ball (0 : ℂ) 3) := hd.deriv hU
  have hψ' : ∀ s : ℂ, ‖s‖ ≤ 1 → ‖deriv (deriv f) s‖ ≤ 2 * B := by
    intro s hs
    have hsub : closedBall s (1 / 2) ⊆ closedBall (0 : ℂ) (3 / 2) := by
      intro y hy
      rw [mem_closedBall, dist_eq_norm] at hy
      rw [mem_closedBall_zero_iff]
      have h1 : ‖y‖ ≤ ‖s‖ + ‖y - s‖ := by
        calc ‖y‖ = ‖s + (y - s)‖ := by rw [add_sub_cancel]
          _ ≤ ‖s‖ + ‖y - s‖ := norm_add_le _ _
      linarith
    have hsub2 : closedBall (0 : ℂ) (3 / 2) ⊆ ball (0 : ℂ) 3 := by
      intro y hy
      rw [mem_closedBall_zero_iff] at hy
      rw [mem_ball_zero_iff]
      linarith
    have := cauchy_deriv_le (f := deriv f) (c := s) (R := 1 / 2) (B := B) (by norm_num)
      (hψd.mono (hsub.trans hsub2))
      (fun y hy => hψ y (hsub (sphere_subset_closedBall hy)))
    have e : B / (1 / 2) = 2 * B := by ring
    rwa [e] at this
  intro z hz
  have hcl1 : closedBall (0 : ℂ) ‖z‖ ⊆ closedBall (0 : ℂ) 1 := closedBall_subset_closedBall hz
  have hcl3 : closedBall (0 : ℂ) 1 ⊆ ball (0 : ℂ) 3 := by
    intro y hy
    rw [mem_closedBall_zero_iff] at hy
    rw [mem_ball_zero_iff]
    linarith
  have hdiffAt : ∀ s ∈ closedBall (0 : ℂ) ‖z‖, DifferentiableAt ℂ f s := fun s hs =>
    hd.differentiableAt (hU.mem_nhds (hcl3 (hcl1 hs)))
  have hdiffAt' : ∀ s ∈ closedBall (0 : ℂ) ‖z‖, DifferentiableAt ℂ (deriv f) s := fun s hs =>
    hψd.differentiableAt (hU.mem_nhds (hcl3 (hcl1 hs)))
  -- first mean value inequality for the derivative
  have hmv1 : ∀ s ∈ closedBall (0 : ℂ) ‖z‖, ‖deriv f s - deriv f 0‖ ≤ 2 * B * ‖z‖ := by
    intro s hs
    have hs1 : ‖s‖ ≤ ‖z‖ := by simpa using hs
    have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := deriv f) (s := closedBall (0 : ℂ) ‖z‖)
      (C := 2 * B) hdiffAt' (fun x hx => hψ' x ((mem_closedBall_zero_iff.mp hx).trans hz))
      (convex_closedBall _ _) (mem_closedBall_self (norm_nonneg z)) hs
    calc ‖deriv f s - deriv f 0‖ ≤ 2 * B * ‖s - 0‖ := h
      _ ≤ 2 * B * ‖z‖ := by
        rw [sub_zero]
        exact mul_le_mul_of_nonneg_left hs1 (by linarith)
  -- second mean value inequality
  have hg : ∀ s ∈ closedBall (0 : ℂ) ‖z‖,
      HasDerivWithinAt (fun s : ℂ => f s - s • deriv f 0) (deriv f s - deriv f 0)
        (closedBall (0 : ℂ) ‖z‖) s := by
    intro s hs
    have h1 := (hdiffAt s hs).hasDerivAt
    have h2 : HasDerivAt (fun s : ℂ => s • deriv f 0) (deriv f 0) s := by
      simpa using (hasDerivAt_id s).smul_const (deriv f 0)
    exact (h1.sub h2).hasDerivWithinAt
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hg hmv1 (convex_closedBall _ _)
    (mem_closedBall_self (norm_nonneg z)) (x := 0)
    (by rw [mem_closedBall_zero_iff]) (y := z)
  have e : (fun s : ℂ => f s - s • deriv f 0) z - (fun s : ℂ => f s - s • deriv f 0) 0 =
      f z - f 0 - z • deriv f 0 := by
    simp only [zero_smul, sub_zero]
    abel
  rw [e, sub_zero] at h
  calc ‖f z - f 0 - z • deriv f 0‖ ≤ 2 * B * ‖z‖ * ‖z‖ := h
    _ = 2 * B * ‖z‖ ^ 2 := by ring

section pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Along a direction `e` of length at most `r/3`: derivative and second order remainder. -/
theorem line_taylor (φ : E → F) (w0 : E) (r B : ℝ) (hr : 0 < r)
    (hd : DifferentiableOn ℂ φ (ball w0 r)) (hB : ∀ w ∈ ball w0 r, ‖φ w‖ ≤ B)
    (e : E) (he : ‖e‖ ≤ r / 3) :
    ‖fderiv ℂ φ w0 e‖ ≤ B ∧ ∀ z : ℂ, ‖z‖ ≤ 1 →
      ‖φ (w0 + z • e) - φ w0 - z • fderiv ℂ φ w0 e‖ ≤ 2 * B * ‖z‖ ^ 2 := by
  have hmem : ∀ u : ℂ, ‖u‖ < 3 → w0 + u • e ∈ ball w0 r := by
    intro u hu
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
    by_cases h0 : ‖e‖ = 0
    · rw [h0, mul_zero]; exact hr
    · have hpos : 0 < ‖e‖ := lt_of_le_of_ne (norm_nonneg e) (Ne.symm h0)
      calc ‖u‖ * ‖e‖ < 3 * ‖e‖ := mul_lt_mul_of_pos_right hu hpos
        _ ≤ 3 * (r / 3) := by gcongr
        _ = r := by ring
  set f : ℂ → F := fun u => φ (w0 + u • e) with hf
  have hlin : DifferentiableOn ℂ (fun u : ℂ => w0 + u • e) (ball (0 : ℂ) 3) :=
    (by fun_prop : Differentiable ℂ (fun u : ℂ => w0 + u • e)).differentiableOn
  have hmaps : MapsTo (fun u : ℂ => w0 + u • e) (ball (0 : ℂ) 3) (ball w0 r) := fun u hu =>
    hmem u (by simpa using hu)
  have hfd : DifferentiableOn ℂ f (ball (0 : ℂ) 3) := DifferentiableOn.comp hd hlin hmaps
  have hfB : ∀ z ∈ ball (0 : ℂ) 3, ‖f z‖ ≤ B := fun z hz => hB _ (hmem z (by simpa using hz))
  have hder : deriv f 0 = fderiv ℂ φ w0 e := by
    have h0 : w0 + (0 : ℂ) • e = w0 := by simp
    have hφ : HasFDerivAt φ (fderiv ℂ φ w0) (w0 + (0 : ℂ) • e) := by
      rw [h0]
      exact (hd.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hr))).hasFDerivAt
    have hl : HasDerivAt (fun u : ℂ => w0 + u • e) e 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const e).const_add w0
    exact (hφ.comp_hasDerivAt (0 : ℂ) hl).deriv
  obtain ⟨h1, h2⟩ := taylor_one f B hfd hfB
  refine ⟨by rwa [hder] at h1, fun z hz => ?_⟩
  have := h2 z hz
  rw [hder] at this
  simpa [hf] using this

/-- Banach-domain pointwise bounds: operator-type bound for the derivative and a quadratic
Taylor remainder, for a function bounded on a ball. -/
theorem pointwise_taylor (φ : E → F) (w0 : E) (r B : ℝ) (hr : 0 < r)
    (hd : DifferentiableOn ℂ φ (ball w0 r)) (hB : ∀ w ∈ ball w0 r, ‖φ w‖ ≤ B) :
    (∀ v : E, ‖fderiv ℂ φ w0 v‖ ≤ 3 * B / r * ‖v‖) ∧
    (∀ v : E, ‖v‖ ≤ r / 3 → ‖φ (w0 + v) - φ w0 - fderiv ℂ φ w0 v‖ ≤ 18 * B / r ^ 2 * ‖v‖ ^ 2) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB w0 (mem_ball_self hr))
  -- normalised direction
  have key : ∀ v : E, v ≠ 0 → ∃ (z : ℂ) (e : E), ‖e‖ = r / 3 ∧ ‖z‖ = 3 * ‖v‖ / r ∧ v = z • e := by
    intro v hv
    have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
    refine ⟨((3 * ‖v‖ / r : ℝ) : ℂ), (((r / 3) / ‖v‖ : ℝ) : ℂ) • v, ?_, ?_, ?_⟩
    · rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      field_simp
    · rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    · rw [smul_smul, ← Complex.ofReal_mul]
      have : 3 * ‖v‖ / r * (r / 3 / ‖v‖) = 1 := by field_simp
      rw [this]; simp
  refine ⟨fun v => ?_, fun v hv => ?_⟩
  · by_cases h0 : v = 0
    · subst h0; simp
    · obtain ⟨z, e, he, hz, hve⟩ := key v h0
      have h1 := (line_taylor φ w0 r B hr hd hB e he.le).1
      have : fderiv ℂ φ w0 v = z • fderiv ℂ φ w0 e := by
        conv_lhs => rw [hve]
        exact map_smul _ _ _
      rw [this, norm_smul, hz]
      calc 3 * ‖v‖ / r * ‖fderiv ℂ φ w0 e‖ ≤ 3 * ‖v‖ / r * B :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = 3 * B / r * ‖v‖ := by ring
  · by_cases h0 : v = 0
    · subst h0; simp
    · obtain ⟨z, e, he, hz, hve⟩ := key v h0
      have hz1 : ‖z‖ ≤ 1 := by
        rw [hz, div_le_one hr]
        linarith
      have h2 := (line_taylor φ w0 r B hr hd hB e he.le).2 z hz1
      have hvz : z • e = v := hve.symm
      have hD : z • fderiv ℂ φ w0 e = fderiv ℂ φ w0 v := by
        conv_rhs => rw [hve]
        exact (map_smul _ _ _).symm
      rw [hvz, hD] at h2
      calc ‖φ (w0 + v) - φ w0 - fderiv ℂ φ w0 v‖ ≤ 2 * B * ‖z‖ ^ 2 := h2
        _ = 18 * B / r ^ 2 * ‖v‖ ^ 2 := by
          rw [hz]; field_simp; ring

end pointwise

section integration

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
variable {T : Type w} [MeasurableSpace T]

omit [CompleteSpace F] in
/-- Fixed-direction derivative of the integrand is a.e. strongly measurable, as an a.e. limit of
difference quotients (no measurability of the operator-valued map is used). -/
theorem deriv_dir_aesm (μ : Measure T) (Φ : E → T → F) (U : Set E) (w0 : E) (hw0 : w0 ∈ U)
    (r : ℝ) (hr : 0 < r) (hrU : ball w0 r ⊆ U)
    (hm : ∀ w ∈ U, AEStronglyMeasurable (Φ w) μ)
    (hg : ∀ᵐ t ∂μ, DifferentiableOn ℂ (fun w => Φ w t) U) (v : E) :
    AEStronglyMeasurable (fun t => fderiv ℂ (fun w => Φ w t) w0 v) μ := by
  set c : ℝ := r / (3 * (‖v‖ + 1)) with hc
  have hcpos : 0 < c := by positivity
  set s : ℕ → ℂ := fun n => ((c : ℝ) : ℂ) / ((n + 1 : ℕ) : ℂ) with hs
  have hc0 : ((c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hcpos.ne'
  have hs0 : Tendsto s atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩
    · exact (tendsto_const_div_atTop_nhds_zero_nat ((c : ℝ) : ℂ)).comp (tendsto_add_atTop_nat 1)
    · simp only [hs, mem_compl_iff, mem_singleton_iff]
      exact div_ne_zero hc0 (by exact_mod_cast Nat.succ_ne_zero n)
  have hsn : ∀ n, ‖s n‖ ≤ c := by
    intro n
    simp only [hs, norm_div, Complex.norm_natCast]
    have h1 : ‖((c : ℝ) : ℂ)‖ = c := by
      rw [Complex.norm_real, Real.norm_of_nonneg hcpos.le]
    rw [h1]
    have h2 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    calc c / ((n + 1 : ℕ) : ℝ) ≤ c / 1 := by gcongr
      _ = c := div_one c
  have hmem : ∀ n, w0 + s n • v ∈ ball w0 r := by
    intro n
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
    calc ‖s n‖ * ‖v‖ ≤ c * ‖v‖ := mul_le_mul_of_nonneg_right (hsn n) (norm_nonneg _)
      _ < r := by
        rw [hc]
        have h3 : ‖v‖ / (‖v‖ + 1) < 1 := by
          rw [div_lt_one (by positivity)]; linarith
        calc r / (3 * (‖v‖ + 1)) * ‖v‖ = r / 3 * (‖v‖ / (‖v‖ + 1)) := by field_simp
          _ < r / 3 * 1 := by gcongr
          _ < r := by linarith
  refine aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun n t => (s n)⁻¹ • (Φ (w0 + s n • v) t - Φ w0 t)) (fun n => ?_) ?_
  · have h1 := hm (w0 + s n • v) (hrU (hmem n))
    have h2 := hm w0 hw0
    exact (h1.sub h2).const_smul _
  · filter_upwards [hg] with t ht
    have hdφ : DifferentiableAt ℂ (fun w => Φ w t) w0 :=
      ht.differentiableAt (Filter.mem_of_superset (isOpen_ball.mem_nhds (mem_ball_self hr)) hrU)
    have hl : HasDerivAt (fun u : ℂ => w0 + u • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add w0
    have hφ : HasFDerivAt (fun w => Φ w t) (fderiv ℂ (fun w => Φ w t) w0) (w0 + (0 : ℂ) • v) := by
      simpa using hdφ.hasFDerivAt
    have hd := hφ.comp_hasDerivAt (0 : ℂ) hl
    have := (hasDerivAt_iff_tendsto_slope_zero.mp hd).comp hs0
    refine this.congr (fun n => ?_)
    simp

/-- The core differentiation-under-the-integral theorem with a Banach-domain parameter. -/
theorem int_banach_fderiv (μ : Measure T) (Φ : E → T → F) (U : Set E) (b : T → ℝ)
    (hU : IsOpen U) (hb : Integrable b μ)
    (hm : ∀ w ∈ U, AEStronglyMeasurable (Φ w) μ)
    (hg : ∀ᵐ t ∂μ, DifferentiableOn ℂ (fun w => Φ w t) U ∧ ∀ w ∈ U, ‖Φ w t‖ ≤ b t)
    (w0 : E) (hw0 : w0 ∈ U) :
    ∃ L : E →L[ℂ] F, HasFDerivAt (fun w => ∫ t, Φ w t ∂μ) L w0 ∧
      ∀ v : E, Integrable (fun t => fderiv ℂ (fun w => Φ w t) w0 v) μ ∧
        L v = ∫ t, fderiv ℂ (fun w => Φ w t) w0 v ∂μ := by
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU w0 hw0
  have hint : ∀ w ∈ U, Integrable (Φ w) μ := fun w hw =>
    hb.mono' (hm w hw) (by filter_upwards [hg] with t ht using ht.2 w hw)
  set D : T → E →L[ℂ] F := fun t => fderiv ℂ (fun w => Φ w t) w0 with hD
  have hdom : ∀ᵐ t ∂μ, (∀ v : E, ‖D t v‖ ≤ 3 * b t / r * ‖v‖) ∧
      (∀ v : E, ‖v‖ ≤ r / 3 →
        ‖Φ (w0 + v) t - Φ w0 t - D t v‖ ≤ 18 * b t / r ^ 2 * ‖v‖ ^ 2) := by
    filter_upwards [hg] with t ht
    exact pointwise_taylor (fun w => Φ w t) w0 r (b t) hr (ht.1.mono hrU)
      (fun w hw => ht.2 w (hrU hw))
  have hmD : ∀ v : E, AEStronglyMeasurable (fun t => D t v) μ := fun v =>
    deriv_dir_aesm μ Φ U w0 hw0 r hr hrU hm (by filter_upwards [hg] with t ht using ht.1) v
  have hDint : ∀ v : E, Integrable (fun t => D t v) μ := by
    intro v
    refine ((hb.const_mul (3 / r)).mul_const ‖v‖).mono' (hmD v) ?_
    filter_upwards [hdom] with t ht
    have := ht.1 v
    calc ‖D t v‖ ≤ 3 * b t / r * ‖v‖ := this
      _ = 3 / r * b t * ‖v‖ := by ring
  have hDlin : ∀ᵐ t ∂μ, True := Eventually.of_forall fun _ => trivial
  let Lf : E →ₗ[ℂ] F :=
    { toFun := fun v => ∫ t, D t v ∂μ
      map_add' := fun v v' => by
        rw [← integral_add (hDint v) (hDint v')]
        exact integral_congr_ae (Eventually.of_forall fun t => map_add (D t) v v')
      map_smul' := fun c v => by
        simp only [RingHom.id_apply]
        rw [← integral_smul]
        exact integral_congr_ae (Eventually.of_forall fun t => map_smul (D t) c v) }
  have hLb : ∀ v : E, ‖Lf v‖ ≤ (3 / r * ∫ t, b t ∂μ) * ‖v‖ := by
    intro v
    change ‖∫ t, D t v ∂μ‖ ≤ _
    have hbd : ∀ᵐ t ∂μ, ‖D t v‖ ≤ 3 / r * b t * ‖v‖ := by
      filter_upwards [hdom] with t ht
      calc ‖D t v‖ ≤ 3 * b t / r * ‖v‖ := ht.1 v
        _ = 3 / r * b t * ‖v‖ := by ring
    calc ‖∫ t, D t v ∂μ‖ ≤ ∫ t, 3 / r * b t * ‖v‖ ∂μ :=
          norm_integral_le_of_norm_le ((hb.const_mul (3 / r)).mul_const ‖v‖) hbd
      _ = (3 / r * ∫ t, b t ∂μ) * ‖v‖ := by
          rw [integral_mul_const, integral_const_mul]
  let L : E →L[ℂ] F := LinearMap.mkContinuous Lf (3 / r * ∫ t, b t ∂μ) hLb
  have hLv : ∀ v, L v = ∫ t, D t v ∂μ := fun v => rfl
  refine ⟨L, ?_, fun v => ⟨hDint v, hLv v⟩⟩
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have hbig : (fun h : E => ∫ t, Φ (w0 + h) t ∂μ - ∫ t, Φ w0 t ∂μ - L h) =O[𝓝 0]
      (fun h : E => ‖h‖ ^ 2) := by
    refine Asymptotics.IsBigO.of_bound (18 / r ^ 2 * ∫ t, b t ∂μ) ?_
    have hev : ∀ᶠ h in 𝓝 (0 : E), h ∈ ball (0 : E) (r / 3) := ball_mem_nhds 0 (by positivity)
    filter_upwards [hev] with h hh
    have hh' : ‖h‖ ≤ r / 3 := by simpa using hh.out.le
    have hhU : w0 + h ∈ U := hrU (by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
      linarith)
    have hrem : ∫ t, Φ (w0 + h) t ∂μ - ∫ t, Φ w0 t ∂μ - L h =
        ∫ t, (Φ (w0 + h) t - Φ w0 t - D t h) ∂μ := by
      have e1 : ∫ t, (Φ (w0 + h) t - Φ w0 t - D t h) ∂μ =
          ∫ t, (Φ (w0 + h) t - Φ w0 t) ∂μ - ∫ t, D t h ∂μ :=
        integral_sub (f := fun t => Φ (w0 + h) t - Φ w0 t) (g := fun t => D t h)
          ((hint _ hhU).sub (hint _ hw0)) (hDint h)
      have e2 : ∫ t, (Φ (w0 + h) t - Φ w0 t) ∂μ = ∫ t, Φ (w0 + h) t ∂μ - ∫ t, Φ w0 t ∂μ :=
        integral_sub (hint _ hhU) (hint _ hw0)
      rw [hLv, e1, e2]
    rw [hrem, Real.norm_of_nonneg (sq_nonneg _)]
    have hbd : ∀ᵐ t ∂μ, ‖Φ (w0 + h) t - Φ w0 t - D t h‖ ≤ 18 / r ^ 2 * b t * ‖h‖ ^ 2 := by
      filter_upwards [hdom] with t ht
      calc ‖Φ (w0 + h) t - Φ w0 t - D t h‖ ≤ 18 * b t / r ^ 2 * ‖h‖ ^ 2 := ht.2 h hh'
        _ = 18 / r ^ 2 * b t * ‖h‖ ^ 2 := by ring
    calc ‖∫ t, (Φ (w0 + h) t - Φ w0 t - D t h) ∂μ‖ ≤ ∫ t, 18 / r ^ 2 * b t * ‖h‖ ^ 2 ∂μ :=
          norm_integral_le_of_norm_le ((hb.const_mul (18 / r ^ 2)).mul_const (‖h‖ ^ 2)) hbd
      _ = 18 / r ^ 2 * (∫ t, b t ∂μ) * ‖h‖ ^ 2 := by
          rw [integral_mul_const, integral_const_mul]
  exact hbig.trans_isLittleO (Asymptotics.isLittleO_norm_pow_id one_lt_two)

end integration

/-- NEW clause: bounded integration with a Banach-domain parameter (Frechet differentiation
under the integral, operator-valued derivative, evaluated on fixed tangent vectors). -/
def GP05_int_banach : Prop :=
  ∀ (E F : Type u) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (T : Type w) [MeasurableSpace T] (μ : Measure T) (Φ : E → T → F) (U : Set E) (b : T → ℝ),
    IsOpen U → Integrable b μ → (∀ w ∈ U, AEStronglyMeasurable (Φ w) μ) →
    (∀ᵐ t ∂μ, DifferentiableOn ℂ (fun w => Φ w t) U ∧ ∀ w ∈ U, ‖Φ w t‖ ≤ b t) →
    DifferentiableOn ℂ (fun w => ∫ t, Φ w t ∂μ) U ∧
    AnalyticOnNhd ℂ (fun w => ∫ t, Φ w t ∂μ) U ∧
    ∀ w ∈ U, ∀ v : E, Integrable (fun t => fderiv ℂ (fun z => Φ z t) w v) μ ∧
      fderiv ℂ (fun z => ∫ t, Φ z t ∂μ) w v = ∫ t, fderiv ℂ (fun z => Φ z t) w v ∂μ

theorem gp05_int_banach : GP05_int_banach.{u, w} := by
  intro E F _ _ _ _ _ T _ μ Φ U b hU hb hm hg
  have hex := fun w (hw : w ∈ U) => int_banach_fderiv μ Φ U b hU hb hm hg w hw
  have hdiff : DifferentiableOn ℂ (fun w => ∫ t, Φ w t ∂μ) U := by
    intro w hw
    obtain ⟨L, hL, -⟩ := hex w hw
    exact hL.differentiableAt.differentiableWithinAt
  refine ⟨hdiff, HolomorphicStageD3.analyticOnNhd_of_differentiableOn hU hdiff, ?_⟩
  intro w hw v
  obtain ⟨L, hL, hLv⟩ := hex w hw
  obtain ⟨h1, h2⟩ := hLv v
  refine ⟨h1, ?_⟩
  rw [hL.fderiv]
  exact h2

/-- FIN-EXT025-GP-05 as a Lean theorem, FULL: every clause of the printed conclusion,
including bounded integration both for a scalar parameter and for a Banach-domain parameter.
(The first six conjuncts are the frozen `Ext025LGP05.contract_GP05`.) -/
theorem contract_GP05_full :
    GP05_one.{v} ∧ GP05_banach.{u} ∧ GP05_limit.{u} ∧ GP05_sum.{u} ∧ GP05_series_bounds.{u} ∧
      GP05_int.{v, w} ∧ GP05_int_banach.{u, w} :=
  ⟨gp05_one, gp05_banach, gp05_limit, gp05_sum, gp05_series_bounds, gp05_int, gp05_int_banach⟩

end QuantumNLS.Ext025L

#print axioms QuantumNLS.Ext025L.contract_GP05_full
#print axioms QuantumNLS.Ext025L.gp05_int_banach
