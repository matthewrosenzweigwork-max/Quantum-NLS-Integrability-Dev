import QuantumNLS.Ext025LGP05Full

/-!
# EXT-025 layer A (wrapper): the application_wrapper of FIN-EXT025-GP-05 and `contract_GP05_full2`

The frozen `Ext025LGP05Full` (sha256 82f8c8219c4b2201045d45c2b91fe5b5e57829d2ae065dc653a0f1723e0d9c80, not
edited) states bounded integration and fixed-tangent differentiation (`GP05_int_banach`), but,
per terra_review r236, NOT the construction printed in the second `application_wrapper` sentence
of FIN-EXT025-GP-05 (FINAL_EXTERNAL_THEOREM_INSTANCES.json, sha256
82876b0400535292c74c814f70269d4dea6778fb05d4d3066b73e8a3d0d13782):

  "For the scalar Haar average of covectors, evaluate coefficients on fixed tangent vectors,
   integrate their scalar values, and use the uniform Cauchy/polarization bounds to recover a
   norm-convergent dual-valued series. No Bochner measurability in the operator-norm space is
   assumed."

This module proves exactly that, and states `contract_GP05_full2 = contract_GP05_full ∧ GP05_wrapper`.

## READING of the printed sentence (explicit, for the reviewer)

* "covectors": elements of the strong dual `X* = StrongDual ℂ X` of a complex normed space `X`
  (the tangent space; `X` need not be complete, `X*` is always Banach).
* "scalar Haar average": `(T, mu)` is an ARBITRARY measure space (a Haar probability/finite measure
  is a special case; nothing about the group structure is used), `alpha : E -> T -> X*` is the
  covector family, `w ∈ U ⊆ E` the holomorphic parameter (`E` a complex normed space, "Banach
  domain"; `U` open: the fixed common neighbourhood of the printed hypotheses).
* hypotheses: uniform bound `‖alpha w t‖ ≤ b t` on `U` with `b` integrable (the printed
  "circle bounds are uniform/summable", here on the whole neighbourhood, as in the frozen
  `GP05_int`), a.e. `t`: `w ↦ alpha w t` complex differentiable on `U` into `X*` (operator norm),
  and ONLY SCALAR measurability: for every `w ∈ U` and fixed `v ∈ X`,
  `t ↦ alpha w t v` is a.e. strongly measurable.  Nothing is assumed about measurability of
  `t ↦ alpha w t` (or of `t ↦ D_t`) in the operator-norm space `X*`.
* "evaluate coefficients on fixed tangent vectors, integrate their scalar values":
  the `n`-th (Taylor/polarization) coefficient of the integrand at a point `x ∈ U`, evaluated on
  fixed tangent vectors `m : Fin n → E` (parameter directions) and a fixed covector argument
  `v ∈ X`, i.e. the scalar `(n!)^{-1} iteratedFDeriv ℂ n (alpha · t) x m v`, is shown a.e.
  strongly measurable and integrable in `t`, and its integral is the scalar value of the
  coefficient of the dual-valued function `A`.
* "recover a norm-convergent dual-valued series": the dual-valued function `A` with
  `A w v = ∫ alpha w t v dmu` exists (each `A w` is a bounded functional, `‖A w‖ ≤ ∫ b`), is
  complex differentiable and analytic as an `X*`-valued function (operator norm), the identity
  `((n!)^{-1} iteratedFDeriv ℂ n A x) m v = ∫ (n!)^{-1} iteratedFDeriv ℂ n (alpha · t) x m v` holds,
  the coefficients obey the uniform Cauchy/polarization bounds
  `‖iteratedFDeriv ℂ n A x‖ ≤ (∫ b) (4(n+1)/R)^n` and
  `‖(n!)^{-1} iteratedFDeriv ℂ n A x‖ (R/(4e))^n ≤ (∫ b) e`, and the series
  `∑ (n!)^{-1} iteratedFDeriv ℂ n A x (w - x)^n` converges to `A w` in the dual norm
  (`HasFPowerSeriesOnBall` of radius `R/(4e)` for any `R` with `closedBall x R ⊆ U`), with
  `∑ ‖coefficient_n‖ ρ^n < ∞` for every `ρ < R/(4e)` (absolute = norm convergence).
* The frozen clauses' common-universe limitation (`E`, `X*` in one universe `u`) is kept
  (`X : Type u`).  No `Nontrivial E` and no `0 ≤ M` is needed in the new clause.
* The parameter `T` lives in universe `w`; the integral is the Bochner integral of SCALARS only.

## Proof (all of it is new; frozen modules are only imported)
1. `avg_fderiv`: for each `w0 ∈ U`, the map `h ↦ (v ↦ ∫ D_t h v)` is a bounded bilinear map
   (scalar integrals of fixed-vector evaluations, `D_t = fderiv (alpha · t) w0`) and `A` has it as
   its operator-norm Frechet derivative (Taylor remainder bound in the DUAL norm from the frozen
   `pointwise_taylor`, uniform in `v`; measurability of `t ↦ D_t h v` from the frozen
   `deriv_dir_aesm` applied to the SCALAR integrand `alpha · · v`).
2. `iter_identity`: by induction on `n`, for all `y ∈ U`, `m`, `v`: the scalar function
   `t ↦ iteratedFDeriv ℂ n (alpha · t) y m v` is a.e. strongly measurable, integrable, and
   `iteratedFDeriv ℂ n A y m v` is its integral (step: `iteratedFDeriv_succ_apply_left`, the frozen
   `int_banach_fderiv` for the scalar integrand `Φ y t = iteratedFDeriv n (alpha·t) y (tail m) v`
   on a small ball, and the frozen `deriv_dir_aesm`).
3. Series and bounds: Cauchy estimates (`HolomorphicStageD1`, as in the frozen `gp05_banach`
   proof, here without `Nontrivial`) for `A` with `M = ∫ b`.
-/
set_option autoImplicit false
set_option maxHeartbeats 3200000
noncomputable section
open Set Filter Topology Metric MeasureTheory
open scoped ENNReal NNReal

namespace QuantumNLS.Ext025L

universe u v w

section series

/-- The series part of the frozen `gp05_banach`, restated with the bound on the open ball and
without `Nontrivial` (statement-level copy of the frozen proof). -/
theorem banach_series {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (f : E → F) (U : Set E) (x : E) (R M : ℝ) (hU : IsOpen U) (hR : 0 < R) (hM0 : 0 ≤ M)
    (hcl : closedBall x R ⊆ U) (hf : DifferentiableOn ℂ f U)
    (hM : ∀ z ∈ ball x R, ‖f z‖ ≤ M) :
    (∀ n : ℕ, ‖iteratedFDeriv ℂ n f x‖ ≤ M * (4 * ((n : ℝ) + 1) / R) ^ n) ∧
    (∀ n : ℕ, ‖((n.factorial : ℂ))⁻¹ • iteratedFDeriv ℂ n f x‖ * (R / (4 * Real.exp 1)) ^ n ≤
      M * Real.exp 1) ∧
    HasFPowerSeriesOnBall f (fun n : ℕ => ((n.factorial : ℂ))⁻¹ • iteratedFDeriv ℂ n f x) x
      (ENNReal.ofReal (R / (4 * Real.exp 1))) := by
  have hxU : ball x R ⊆ U := ball_subset_closedBall.trans hcl
  have hx : x ∈ U := hcl (mem_closedBall_self hR.le)
  have hexp : (2 : ℝ) < Real.exp 1 := by
    have := Real.add_one_lt_exp (one_ne_zero : (1 : ℝ) ≠ 0)
    linarith
  set r0 : ℝ := R / (4 * Real.exp 1) with hr0_def
  have hr0 : 0 < r0 := div_pos hR (by positivity)
  have hr0_lt : r0 < R / 2 := by
    rw [hr0_def, div_lt_iff₀ (by positivity)]
    nlinarith
  refine ⟨fun n => HolomorphicStageD1.norm_iteratedFDeriv_le hU hf hR hM0 hxU hM n,
    fun n => HolomorphicStageD1.coeff_radius_bound hU hf hR hM0 hxU hM n, ?_⟩
  obtain ⟨r, hrr⟩ : ∃ r : NNReal, (r : ℝ) = r0 := ⟨Real.toNNReal r0, Real.coe_toNNReal r0 hr0.le⟩
  have hr : (0 : NNReal) < r := by
    rw [← NNReal.coe_pos, hrr]
    exact hr0
  have hofr : ENNReal.ofReal r0 = (r : ℝ≥0∞) := by
    rw [← hrr, ENNReal.ofReal_coe_nnreal]
  rw [hofr]
  refine ⟨?_, ENNReal.coe_pos.2 hr, ?_⟩
  · exact FormalMultilinearSeries.le_radius_of_bound
      (p := fun n : ℕ => ((n.factorial : ℂ))⁻¹ • iteratedFDeriv ℂ n f x) (M * Real.exp 1)
      (r := r)
      (fun n => by
        rw [hrr]
        exact HolomorphicStageD1.coeff_radius_bound hU hf hR hM0 hxU hM n)
  · intro y hy
    have hyn : ‖y‖ < r0 := by
      have h1 : ‖y‖₊ < r := by
        rw [Metric.mem_eball, edist_zero_right] at hy
        exact ENNReal.coe_lt_coe.1 hy
      have h2 : (‖y‖₊ : ℝ) < (r : ℝ) := NNReal.coe_lt_coe.2 h1
      rw [coe_nnnorm, hrr] at h2
      exact h2
    have hsmul : ∀ t : ℂ, ‖t‖ < 2 → x + t • y ∈ U := by
      intro t ht
      apply hxU
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
      have hy2 : ‖y‖ < R / 2 := by linarith
      nlinarith [norm_nonneg t, norm_nonneg y]
    have hlin : DifferentiableOn ℂ (fun s : ℂ => x + s • y) (ball (0 : ℂ) 2) :=
      (by fun_prop : Differentiable ℂ (fun s : ℂ => x + s • y)).differentiableOn
    have hmaps : MapsTo (fun s : ℂ => x + s • y) (ball (0 : ℂ) 2) U := by
      intro s hs
      exact hsmul s (by simpa using hs)
    have hgd : DifferentiableOn ℂ (fun s : ℂ => f (x + s • y)) (ball (0 : ℂ) 2) :=
      DifferentiableOn.comp hf hlin hmaps
    have h1mem : (1 : ℂ) ∈ ball (0 : ℂ) 2 := by
      simp
    have hT := Complex.hasSum_taylorSeries_on_ball hgd h1mem
    have hT2 : HasSum (fun n : ℕ => (n.factorial : ℂ)⁻¹ • (1 - 0 : ℂ) ^ n •
        iteratedDeriv n (fun s : ℂ => f (x + s • y)) 0) (f (x + y)) := by
      have h := hT
      rwa [one_smul] at h
    have hdiag : ∀ n : ℕ, iteratedDeriv n (fun s : ℂ => f (x + s • y)) 0
        = iteratedFDeriv ℂ n f x (fun _ => y) := by
      intro n
      have h := HolomorphicStageD2.iteratedDeriv_slice hU hf x y n 0 (by simpa using hx)
      rw [zero_smul, add_zero] at h
      exact h
    convert hT2 using 1
    funext n
    simp only [smul_apply]
    rw [hdiag n]
    simp

end series

section covector

variable {E X : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable {T : Type w} [MeasurableSpace T]

/-- The hypotheses of the wrapper: only SCALAR measurability (`meas`). -/
structure CovHyp (μ : Measure T) (α : E → T → StrongDual ℂ X) (U : Set E) (b : T → ℝ) : Prop where
  isOpen : IsOpen U
  integrable : Integrable b μ
  meas : ∀ w ∈ U, ∀ v : X, AEStronglyMeasurable (fun t => α w t v) μ
  bound : ∀ᵐ t ∂μ, DifferentiableOn ℂ (fun w => α w t) U ∧ ∀ w ∈ U, ‖α w t‖ ≤ b t

/-- Fixed covector argument commutes with the Frechet derivative. -/
theorem fderiv_eval_apply (f : E → StrongDual ℂ X) (y : E) (hf : DifferentiableAt ℂ f y) (v : X)
    (h : E) : fderiv ℂ (fun w => f w v) y h = fderiv ℂ f y h v := by
  have h1 : HasFDerivAt (fun w => f w v)
      ((ContinuousLinearMap.apply ℂ ℂ v).comp (fderiv ℂ f y)) y :=
    (ContinuousLinearMap.apply ℂ ℂ v).hasFDerivAt.comp y hf.hasFDerivAt
  rw [h1.fderiv]
  rfl

/-- Differentiating `iteratedFDeriv` one more time, evaluated on fixed vectors. -/
theorem succ_eval (f : E → StrongDual ℂ X) (n : ℕ) (y : E)
    (hd : DifferentiableAt ℂ (iteratedFDeriv ℂ n f) y) (m : Fin (n + 1) → E) (v : X) :
    iteratedFDeriv ℂ (n + 1) f y m v =
      fderiv ℂ (fun z => iteratedFDeriv ℂ n f z (Fin.tail m) v) y (m 0) := by
  let ev : ContinuousMultilinearMap ℂ (fun _ : Fin n => E) (StrongDual ℂ X) →L[ℂ] ℂ :=
    (ContinuousLinearMap.apply ℂ ℂ v).comp
      (ContinuousMultilinearMap.apply ℂ (fun _ : Fin n => E) (StrongDual ℂ X) (Fin.tail m))
  have h0 := ev.hasFDerivAt.comp y hd.hasFDerivAt
  have hev : HasFDerivAt (fun z => iteratedFDeriv ℂ n f z (Fin.tail m) v)
      (ev.comp (fderiv ℂ (iteratedFDeriv ℂ n f) y)) y := h0
  rw [hev.fderiv, iteratedFDeriv_succ_apply_left]
  rfl

variable {μ : Measure T} {α : E → T → StrongDual ℂ X} {U : Set E} {b : T → ℝ}

theorem CovHyp.integrable_eval (H : CovHyp μ α U b) {w : E} (hw : w ∈ U) (v : X) :
    Integrable (fun t => α w t v) μ := by
  refine (H.integrable.mul_const ‖v‖).mono' (H.meas w hw v) ?_
  filter_upwards [H.bound] with t ht
  calc ‖α w t v‖ ≤ ‖α w t‖ * ‖v‖ := (α w t).le_opNorm v
    _ ≤ b t * ‖v‖ := mul_le_mul_of_nonneg_right (ht.2 w hw) (norm_nonneg _)

theorem CovHyp.b_nonneg (H : CovHyp μ α U b) {w : E} (hw : w ∈ U) : 0 ≤ ∫ t, b t ∂μ := by
  refine integral_nonneg_of_ae ?_
  filter_upwards [H.bound] with t ht
  exact (norm_nonneg _).trans (ht.2 w hw)

/-- Existence of the scalar-integral covector average `A` (only scalar integrals are used). -/
theorem CovHyp.exists_avg (H : CovHyp μ α U b) :
    ∃ A : E → StrongDual ℂ X, ∀ w ∈ U, (∀ v : X, A w v = ∫ t, α w t v ∂μ) ∧
      ‖A w‖ ≤ ∫ t, b t ∂μ := by
  have key : ∀ w : E, ∃ ℓ : StrongDual ℂ X, w ∈ U →
      (∀ v : X, ℓ v = ∫ t, α w t v ∂μ) ∧ ‖ℓ‖ ≤ ∫ t, b t ∂μ := by
    intro w
    by_cases hw : w ∈ U
    · let Lf : X →ₗ[ℂ] ℂ :=
        { toFun := fun v => ∫ t, α w t v ∂μ
          map_add' := fun v v' => by
            rw [← integral_add (H.integrable_eval hw v) (H.integrable_eval hw v')]
            exact integral_congr_ae (Eventually.of_forall fun t => map_add (α w t) v v')
          map_smul' := fun c v => by
            simp only [RingHom.id_apply]
            rw [← integral_smul]
            exact integral_congr_ae (Eventually.of_forall fun t => map_smul (α w t) c v) }
      have hb : ∀ v : X, ‖Lf v‖ ≤ (∫ t, b t ∂μ) * ‖v‖ := by
        intro v
        change ‖∫ t, α w t v ∂μ‖ ≤ _
        have hbd : ∀ᵐ t ∂μ, ‖α w t v‖ ≤ b t * ‖v‖ := by
          filter_upwards [H.bound] with t ht
          calc ‖α w t v‖ ≤ ‖α w t‖ * ‖v‖ := (α w t).le_opNorm v
            _ ≤ b t * ‖v‖ := mul_le_mul_of_nonneg_right (ht.2 w hw) (norm_nonneg _)
        calc ‖∫ t, α w t v ∂μ‖ ≤ ∫ t, b t * ‖v‖ ∂μ :=
              norm_integral_le_of_norm_le (H.integrable.mul_const ‖v‖) hbd
          _ = (∫ t, b t ∂μ) * ‖v‖ := integral_mul_const _ _
      exact ⟨LinearMap.mkContinuous Lf _ hb, fun _ => ⟨fun v => rfl,
        LinearMap.mkContinuous_norm_le _ (H.b_nonneg hw) hb⟩⟩
    · exact ⟨0, fun h => absurd h hw⟩
  choose A hA using key
  exact ⟨A, fun w hw => hA w hw⟩

/-- Step 1: the covector average is Frechet differentiable in the OPERATOR norm of `X*`, with
derivative given by scalar integrals of fixed-vector evaluations of the integrand's derivative. -/
theorem avg_fderiv (H : CovHyp μ α U b) {A : E → StrongDual ℂ X}
    (hA : ∀ w ∈ U, ∀ v : X, A w v = ∫ t, α w t v ∂μ) (w0 : E) (hw0 : w0 ∈ U) :
    ∃ L : E →L[ℂ] StrongDual ℂ X, HasFDerivAt A L w0 ∧
      ∀ h : E, ∀ v : X, L h v = ∫ t, fderiv ℂ (fun w => α w t) w0 h v ∂μ := by
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp H.isOpen w0 hw0
  set D : T → E →L[ℂ] StrongDual ℂ X := fun t => fderiv ℂ (fun w => α w t) w0 with hD
  have hdom : ∀ᵐ t ∂μ, (∀ h : E, ‖D t h‖ ≤ 3 * b t / r * ‖h‖) ∧
      (∀ h : E, ‖h‖ ≤ r / 3 →
        ‖α (w0 + h) t - α w0 t - D t h‖ ≤ 18 * b t / r ^ 2 * ‖h‖ ^ 2) := by
    filter_upwards [H.bound] with t ht
    exact pointwise_taylor (fun w => α w t) w0 r (b t) hr (ht.1.mono hrU)
      (fun w hw => ht.2 w (hrU hw))
  have hmD : ∀ (h : E) (v : X), AEStronglyMeasurable (fun t => D t h v) μ := by
    intro h v
    have hm := deriv_dir_aesm μ (fun w t => α w t v) U w0 hw0 r hr hrU
      (fun w hw => H.meas w hw v)
      (by
        filter_upwards [H.bound] with t ht
        exact (ContinuousLinearMap.apply ℂ ℂ v).differentiable.comp_differentiableOn ht.1) h
    refine hm.congr ?_
    filter_upwards [H.bound] with t ht
    exact fderiv_eval_apply (fun w => α w t) w0
      (ht.1.differentiableAt (H.isOpen.mem_nhds hw0)) v h
  have hDle : ∀ (h : E) (v : X), ∀ᵐ t ∂μ,
      ‖D t h v‖ ≤ 3 / r * b t * (‖h‖ * ‖v‖) := by
    intro h v
    filter_upwards [hdom] with t ht
    calc ‖D t h v‖ ≤ ‖D t h‖ * ‖v‖ := (D t h).le_opNorm v
      _ ≤ 3 * b t / r * ‖h‖ * ‖v‖ :=
          mul_le_mul_of_nonneg_right (ht.1 h) (norm_nonneg _)
      _ = 3 / r * b t * (‖h‖ * ‖v‖) := by ring
  have hDint : ∀ (h : E) (v : X), Integrable (fun t => D t h v) μ := by
    intro h v
    exact ((H.integrable.const_mul (3 / r)).mul_const (‖h‖ * ‖v‖)).mono' (hmD h v) (hDle h v)
  let B : E →ₗ[ℂ] X →ₗ[ℂ] ℂ := LinearMap.mk₂ ℂ (fun h v => ∫ t, D t h v ∂μ)
    (fun h h' v => by
      rw [← integral_add (hDint h v) (hDint h' v)]
      exact integral_congr_ae (Eventually.of_forall fun t => by simp))
    (fun c h v => by
      rw [← integral_smul]
      exact integral_congr_ae (Eventually.of_forall fun t => by simp))
    (fun h v v' => by
      rw [← integral_add (hDint h v) (hDint h v')]
      exact integral_congr_ae (Eventually.of_forall fun t => by simp))
    (fun c h v => by
      rw [← integral_smul]
      exact integral_congr_ae (Eventually.of_forall fun t => by simp))
  have hBle : ∀ (h : E) (v : X), ‖B h v‖ ≤ (3 / r * ∫ t, b t ∂μ) * ‖h‖ * ‖v‖ := by
    intro h v
    change ‖∫ t, D t h v ∂μ‖ ≤ _
    calc ‖∫ t, D t h v ∂μ‖ ≤ ∫ t, 3 / r * b t * (‖h‖ * ‖v‖) ∂μ :=
          norm_integral_le_of_norm_le
            ((H.integrable.const_mul (3 / r)).mul_const (‖h‖ * ‖v‖)) (hDle h v)
      _ = (3 / r * ∫ t, b t ∂μ) * ‖h‖ * ‖v‖ := by
          rw [integral_mul_const, integral_const_mul]; ring
  let L : E →L[ℂ] StrongDual ℂ X := LinearMap.mkContinuous₂ B (3 / r * ∫ t, b t ∂μ) hBle
  have hLhv : ∀ (h : E) (v : X), L h v = ∫ t, D t h v ∂μ := fun h v => rfl
  refine ⟨L, ?_, hLhv⟩
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have hbig : (fun h : E => A (w0 + h) - A w0 - L h) =O[𝓝 0] (fun h : E => ‖h‖ ^ 2) := by
    have hC : 0 ≤ 18 / r ^ 2 * ∫ t, b t ∂μ :=
      mul_nonneg (by positivity) (H.b_nonneg hw0)
    refine Asymptotics.IsBigO.of_bound (18 / r ^ 2 * ∫ t, b t ∂μ) ?_
    have hev : ∀ᶠ h in 𝓝 (0 : E), h ∈ ball (0 : E) (r / 3) := ball_mem_nhds 0 (by positivity)
    filter_upwards [hev] with h hh
    have hh' : ‖h‖ ≤ r / 3 := by simpa using hh.out.le
    have hhU : w0 + h ∈ U := hrU (by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
      linarith)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC (sq_nonneg _)) (fun v => ?_)
    have hrem : (A (w0 + h) - A w0 - L h) v =
        ∫ t, (α (w0 + h) t - α w0 t - D t h) v ∂μ := by
      have e0 : ∀ t, (α (w0 + h) t - α w0 t - D t h) v =
          α (w0 + h) t v - α w0 t v - D t h v := fun t => by simp
      have e1 : ∫ t, (α (w0 + h) t - α w0 t - D t h) v ∂μ =
          ∫ t, α (w0 + h) t v ∂μ - ∫ t, α w0 t v ∂μ - ∫ t, D t h v ∂μ := by
        calc ∫ t, (α (w0 + h) t - α w0 t - D t h) v ∂μ
            = ∫ t, (α (w0 + h) t v - α w0 t v - D t h v) ∂μ :=
              integral_congr_ae (Eventually.of_forall e0)
          _ = ∫ t, (α (w0 + h) t v - α w0 t v) ∂μ - ∫ t, D t h v ∂μ :=
              integral_sub (f := fun t => α (w0 + h) t v - α w0 t v) (g := fun t => D t h v)
                ((H.integrable_eval hhU v).sub (H.integrable_eval hw0 v)) (hDint h v)
          _ = _ := by
              rw [integral_sub (H.integrable_eval hhU v) (H.integrable_eval hw0 v)]
      rw [e1, sub_apply, sub_apply, hA _ hhU, hA _ hw0, hLhv]
    rw [hrem]
    have hbd : ∀ᵐ t ∂μ,
        ‖(α (w0 + h) t - α w0 t - D t h) v‖ ≤ 18 / r ^ 2 * b t * ‖h‖ ^ 2 * ‖v‖ := by
      filter_upwards [hdom] with t ht
      calc ‖(α (w0 + h) t - α w0 t - D t h) v‖
          ≤ ‖α (w0 + h) t - α w0 t - D t h‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ v
        _ ≤ 18 * b t / r ^ 2 * ‖h‖ ^ 2 * ‖v‖ :=
            mul_le_mul_of_nonneg_right (ht.2 h hh') (norm_nonneg _)
        _ = 18 / r ^ 2 * b t * ‖h‖ ^ 2 * ‖v‖ := by ring
    calc ‖∫ t, (α (w0 + h) t - α w0 t - D t h) v ∂μ‖
        ≤ ∫ t, 18 / r ^ 2 * b t * ‖h‖ ^ 2 * ‖v‖ ∂μ :=
          norm_integral_le_of_norm_le
            (((H.integrable.const_mul (18 / r ^ 2)).mul_const (‖h‖ ^ 2)).mul_const ‖v‖) hbd
      _ = 18 / r ^ 2 * (∫ t, b t ∂μ) * ‖h‖ ^ 2 * ‖v‖ := by
          rw [integral_mul_const, integral_mul_const, integral_const_mul]
      _ = (18 / r ^ 2 * ∫ t, b t ∂μ) * ‖h‖ ^ 2 * ‖v‖ := by ring
  exact hbig.trans_isLittleO (Asymptotics.isLittleO_norm_pow_id one_lt_two)

/-- Pointwise Cauchy bound for the `n`-th derivative of the integrand at a point with a ball in `U`. -/
theorem iter_bound_pt (H : CovHyp μ α U b) {t : T}
    (ht : DifferentiableOn ℂ (fun w => α w t) U ∧ ∀ w ∈ U, ‖α w t‖ ≤ b t)
    {y : E} (hy : y ∈ U) {ρ : ℝ} (hρ : 0 < ρ) (hρU : ball y ρ ⊆ U) (n : ℕ) :
    ‖iteratedFDeriv ℂ n (fun w => α w t) y‖ ≤ b t * (4 * ((n : ℝ) + 1) / ρ) ^ n :=
  HolomorphicStageD1.norm_iteratedFDeriv_le H.isOpen ht.1 hρ
    ((norm_nonneg _).trans (ht.2 y hy)) hρU (fun z hz => ht.2 z (hρU hz)) n

theorem iter_eval_le (f : E → StrongDual ℂ X) (n : ℕ) (y : E) (m : Fin n → E) (v : X) :
    ‖iteratedFDeriv ℂ n f y m v‖ ≤ ‖iteratedFDeriv ℂ n f y‖ * (∏ i, ‖m i‖) * ‖v‖ :=
  calc ‖iteratedFDeriv ℂ n f y m v‖ ≤ ‖iteratedFDeriv ℂ n f y m‖ * ‖v‖ :=
        (iteratedFDeriv ℂ n f y m).le_opNorm v
    _ ≤ ‖iteratedFDeriv ℂ n f y‖ * (∏ i, ‖m i‖) * ‖v‖ :=
        mul_le_mul_of_nonneg_right ((iteratedFDeriv ℂ n f y).le_opNorm m) (norm_nonneg _)

/-- Integrability of the fixed-vector coefficient from its a.e. measurability and the Cauchy bound. -/
theorem iter_integrable (H : CovHyp μ α U b) {y : E} (hy : y ∈ U) (n : ℕ) (m : Fin n → E)
    (v : X) (hm : AEStronglyMeasurable (fun t => iteratedFDeriv ℂ n (fun w => α w t) y m v) μ) :
    Integrable (fun t => iteratedFDeriv ℂ n (fun w => α w t) y m v) μ := by
  obtain ⟨ρ, hρ, hρU⟩ := Metric.isOpen_iff.mp H.isOpen y hy
  refine (((H.integrable.mul_const ((4 * ((n : ℝ) + 1) / ρ) ^ n)).mul_const
    (∏ i, ‖m i‖)).mul_const ‖v‖).mono' hm ?_
  filter_upwards [H.bound] with t ht
  calc ‖iteratedFDeriv ℂ n (fun w => α w t) y m v‖
      ≤ ‖iteratedFDeriv ℂ n (fun w => α w t) y‖ * (∏ i, ‖m i‖) * ‖v‖ := iter_eval_le _ n y m v
    _ ≤ b t * (4 * ((n : ℝ) + 1) / ρ) ^ n * (∏ i, ‖m i‖) * ‖v‖ := by
        gcongr
        exact iter_bound_pt H ht hy hρ hρU n

/-- Step 2: measurability, integrability and the scalar-integral identity for all coefficients. -/
theorem iter_identity (H : CovHyp μ α U b) {A : E → StrongDual ℂ X}
    (hA : ∀ w ∈ U, ∀ v : X, A w v = ∫ t, α w t v ∂μ) (hAd : DifferentiableOn ℂ A U) :
    ∀ n : ℕ, ∀ y ∈ U, ∀ (m : Fin n → E) (v : X),
      AEStronglyMeasurable (fun t => iteratedFDeriv ℂ n (fun w => α w t) y m v) μ ∧
      Integrable (fun t => iteratedFDeriv ℂ n (fun w => α w t) y m v) μ ∧
      iteratedFDeriv ℂ n A y m v = ∫ t, iteratedFDeriv ℂ n (fun w => α w t) y m v ∂μ := by
  intro n
  induction n with
  | zero =>
    intro y hy m v
    have hm : AEStronglyMeasurable (fun t => iteratedFDeriv ℂ 0 (fun w => α w t) y m v) μ := by
      simpa only [iteratedFDeriv_zero_apply] using H.meas y hy v
    refine ⟨hm, iter_integrable H hy 0 m v hm, ?_⟩
    simp only [iteratedFDeriv_zero_apply]
    exact hA y hy v
  | succ n ih =>
    intro y0 hy0 m v
    obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp H.isOpen y0 hy0
    set ρ : ℝ := r / 2 with hρdef
    have hρ : 0 < ρ := by positivity
    have hρU : ball y0 ρ ⊆ U := (ball_subset_ball (by linarith)).trans hrU
    set tm : Fin n → E := Fin.tail m with htm
    set P : ℝ := ∏ i, ‖tm i‖ with hP
    set K : ℝ := (4 * ((n : ℝ) + 1) / ρ) ^ n with hK
    set C : ℝ := K * P * ‖v‖ with hC
    let Φ : E → T → ℂ := fun y t => iteratedFDeriv ℂ n (fun w => α w t) y tm v
    have hΦm : ∀ y ∈ ball y0 ρ, AEStronglyMeasurable (Φ y) μ := fun y hy =>
      (ih y (hρU hy) tm v).1
    -- the evaluation map
    let ev : ContinuousMultilinearMap ℂ (fun _ : Fin n => E) (StrongDual ℂ X) →L[ℂ] ℂ :=
      (ContinuousLinearMap.apply ℂ ℂ v).comp
        (ContinuousMultilinearMap.apply ℂ (fun _ : Fin n => E) (StrongDual ℂ X) tm)
    have hΦg : ∀ᵐ t ∂μ, DifferentiableOn ℂ (fun y => Φ y t) (ball y0 ρ) ∧
        ∀ y ∈ ball y0 ρ, ‖Φ y t‖ ≤ b t * C := by
      filter_upwards [H.bound] with t ht
      refine ⟨?_, fun y hy => ?_⟩
      · exact ev.differentiable.comp_differentiableOn
          ((HolomorphicStageD1.differentiableOn_iteratedFDeriv_of_differentiableOn H.isOpen ht.1
            n).mono hρU)
      · have hyU : y ∈ U := hρU hy
        have hsub : ball y ρ ⊆ U := by
          intro z hz
          apply hrU
          rw [mem_ball] at hz hy ⊢
          have := dist_triangle z y y0
          rw [hρdef] at hz hy
          linarith
        calc ‖Φ y t‖ ≤ ‖iteratedFDeriv ℂ n (fun w => α w t) y‖ * P * ‖v‖ := iter_eval_le _ n y tm v
          _ ≤ (b t * K) * P * ‖v‖ := by
              gcongr
              exact iter_bound_pt H ht hyU hρ hsub n
          _ = b t * C := by rw [hC]; ring
    have hb' : Integrable (fun t => b t * C) μ := H.integrable.mul_const C
    obtain ⟨L, hL, hLv⟩ := int_banach_fderiv μ Φ (ball y0 ρ) (fun t => b t * C) isOpen_ball hb'
      hΦm hΦg y0 (mem_ball_self hρ)
    have hdiffn : ∀ᵐ t ∂μ, DifferentiableAt ℂ (iteratedFDeriv ℂ n (fun w => α w t)) y0 := by
      filter_upwards [H.bound] with t ht
      exact ((HolomorphicStageD1.differentiableOn_iteratedFDeriv_of_differentiableOn H.isOpen
        ht.1 n) y0 hy0).differentiableAt (H.isOpen.mem_nhds hy0)
    have hcongr : ∀ᵐ t ∂μ, fderiv ℂ (fun y => Φ y t) y0 (m 0) =
        iteratedFDeriv ℂ (n + 1) (fun w => α w t) y0 m v := by
      filter_upwards [hdiffn] with t ht
      exact (succ_eval (fun w => α w t) n y0 ht m v).symm
    have hmeas : AEStronglyMeasurable
        (fun t => iteratedFDeriv ℂ (n + 1) (fun w => α w t) y0 m v) μ := by
      have h1 := deriv_dir_aesm μ Φ (ball y0 ρ) y0 (mem_ball_self hρ) ρ hρ subset_rfl hΦm
        (by filter_upwards [hΦg] with t ht using ht.1) (m 0)
      exact h1.congr hcongr
    refine ⟨hmeas, iter_integrable H hy0 (n + 1) m v hmeas, ?_⟩
    have hAn : DifferentiableAt ℂ (iteratedFDeriv ℂ n A) y0 :=
      ((HolomorphicStageD1.differentiableOn_iteratedFDeriv_of_differentiableOn H.isOpen hAd n)
        y0 hy0).differentiableAt (H.isOpen.mem_nhds hy0)
    have hev : (fun z => iteratedFDeriv ℂ n A z tm v) =ᶠ[𝓝 y0] (fun z => ∫ t, Φ z t ∂μ) := by
      filter_upwards [ball_mem_nhds y0 hρ] with z hz
      exact (ih z (hρU hz) tm v).2.2
    calc iteratedFDeriv ℂ (n + 1) A y0 m v
        = fderiv ℂ (fun z => iteratedFDeriv ℂ n A z tm v) y0 (m 0) := succ_eval A n y0 hAn m v
      _ = fderiv ℂ (fun z => ∫ t, Φ z t ∂μ) y0 (m 0) := by rw [hev.fderiv_eq]
      _ = L (m 0) := by rw [hL.fderiv]
      _ = ∫ t, fderiv ℂ (fun y => Φ y t) y0 (m 0) ∂μ := (hLv (m 0)).2
      _ = ∫ t, iteratedFDeriv ℂ (n + 1) (fun w => α w t) y0 m v ∂μ :=
          integral_congr_ae hcongr

end covector

section main

/-- The application_wrapper of FIN-EXT025-GP-05 (second sentence), as printed, in the reading
documented in the module header. -/
def GP05_wrapper : Prop :=
  ∀ (E X : Type u) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    (T : Type w) [MeasurableSpace T] (μ : Measure T) (α : E → T → StrongDual ℂ X)
    (U : Set E) (b : T → ℝ),
    IsOpen U → Integrable b μ →
    (∀ w ∈ U, ∀ v : X, AEStronglyMeasurable (fun t => α w t v) μ) →
    (∀ᵐ t ∂μ, DifferentiableOn ℂ (fun w => α w t) U ∧ ∀ w ∈ U, ‖α w t‖ ≤ b t) →
    ∃ A : E → StrongDual ℂ X,
      (∀ w ∈ U, ∀ v : X, Integrable (fun t => α w t v) μ ∧ A w v = ∫ t, α w t v ∂μ) ∧
      (∀ w ∈ U, ‖A w‖ ≤ ∫ t, b t ∂μ) ∧
      DifferentiableOn ℂ A U ∧ AnalyticOnNhd ℂ A U ∧
      ∀ x ∈ U, ∀ R : ℝ, 0 < R → closedBall x R ⊆ U →
        (∀ (n : ℕ) (m : Fin n → E) (v : X),
          AEStronglyMeasurable (fun t => iteratedFDeriv ℂ n (fun w => α w t) x m v) μ ∧
          Integrable (fun t => iteratedFDeriv ℂ n (fun w => α w t) x m v) μ ∧
          iteratedFDeriv ℂ n A x m v = ∫ t, iteratedFDeriv ℂ n (fun w => α w t) x m v ∂μ) ∧
        (∀ (n : ℕ) (m : Fin n → E) (v : X),
          Integrable (fun t => ((n.factorial : ℂ))⁻¹ • iteratedFDeriv ℂ n (fun w => α w t) x m v) μ ∧
          (((n.factorial : ℂ))⁻¹ • iteratedFDeriv ℂ n A x) m v =
            ∫ t, ((n.factorial : ℂ))⁻¹ • iteratedFDeriv ℂ n (fun w => α w t) x m v ∂μ) ∧
        (∀ n : ℕ, ‖iteratedFDeriv ℂ n A x‖ ≤ (∫ t, b t ∂μ) * (4 * ((n : ℝ) + 1) / R) ^ n) ∧
        (∀ n : ℕ, ‖((n.factorial : ℂ))⁻¹ • iteratedFDeriv ℂ n A x‖ * (R / (4 * Real.exp 1)) ^ n ≤
          (∫ t, b t ∂μ) * Real.exp 1) ∧
        HasFPowerSeriesOnBall A (fun n : ℕ => ((n.factorial : ℂ))⁻¹ • iteratedFDeriv ℂ n A x) x
          (ENNReal.ofReal (R / (4 * Real.exp 1))) ∧
        (∀ ρ : ℝ≥0, (ρ : ℝ) < R / (4 * Real.exp 1) →
          Summable fun n : ℕ => ‖((n.factorial : ℂ))⁻¹ • iteratedFDeriv ℂ n A x‖ * (ρ : ℝ) ^ n)

theorem gp05_wrapper : GP05_wrapper.{u, w} := by
  intro E X _ _ _ _ T _ μ α U b hU hb hm hg
  have H : CovHyp μ α U b := ⟨hU, hb, hm, hg⟩
  obtain ⟨A, hA⟩ := H.exists_avg
  have hAv : ∀ w ∈ U, ∀ v : X, A w v = ∫ t, α w t v ∂μ := fun w hw => (hA w hw).1
  have hAb : ∀ w ∈ U, ‖A w‖ ≤ ∫ t, b t ∂μ := fun w hw => (hA w hw).2
  have hAd : DifferentiableOn ℂ A U := by
    intro w hw
    obtain ⟨L, hL, -⟩ := avg_fderiv H hAv w hw
    exact hL.differentiableAt.differentiableWithinAt
  refine ⟨A, fun w hw v => ⟨H.integrable_eval hw v, hAv w hw v⟩, hAb, hAd,
    HolomorphicStageD3.analyticOnNhd_of_differentiableOn hU hAd, ?_⟩
  intro x hx R hR hcl
  have hxU : ball x R ⊆ U := ball_subset_closedBall.trans hcl
  have hI := iter_identity H hAv hAd
  have hM0 : 0 ≤ ∫ t, b t ∂μ := H.b_nonneg hx
  obtain ⟨hs1, hs2, hs3⟩ := banach_series A U x R (∫ t, b t ∂μ) hU hR hM0 hcl hAd
    (fun z hz => hAb z (hxU hz))
  refine ⟨fun n m v => hI n x hx m v, fun n m v => ⟨?_, ?_⟩, hs1, hs2, hs3, ?_⟩
  · exact (iter_integrable H hx n m v (hI n x hx m v).1).smul ((n.factorial : ℂ)⁻¹)
  · rw [integral_smul, ← (hI n x hx m v).2.2]
    rfl
  · intro ρ hρ
    refine FormalMultilinearSeries.summable_norm_mul_pow
      (p := fun n : ℕ => ((n.factorial : ℂ))⁻¹ • iteratedFDeriv ℂ n A x) ?_
    calc ((ρ : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (ρ : ℝ) := (ENNReal.ofReal_coe_nnreal).symm
      _ < ENNReal.ofReal (R / (4 * Real.exp 1)) :=
          (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hρ
      _ ≤ _ := hs3.r_le

/-- FIN-EXT025-GP-05 as a Lean theorem, FULL, including the application_wrapper's construction:
the six frozen conjuncts of `contract_GP05_full`, the Banach-domain integration clause
`GP05_int_banach`, and the NEW clause `GP05_wrapper` (norm-convergent dual-valued series from
scalar covector evaluations, with only scalar measurability assumed). -/
theorem contract_GP05_full2 :
    GP05_one.{v} ∧ GP05_banach.{u} ∧ GP05_limit.{u} ∧ GP05_sum.{u} ∧ GP05_series_bounds.{u} ∧
      GP05_int.{v, w} ∧ GP05_int_banach.{u, w} ∧ GP05_wrapper.{u, w} :=
  ⟨gp05_one, gp05_banach, gp05_limit, gp05_sum, gp05_series_bounds, gp05_int, gp05_int_banach,
    gp05_wrapper⟩

end main

end QuantumNLS.Ext025L

#print axioms QuantumNLS.Ext025L.contract_GP05_full2
#print axioms QuantumNLS.Ext025L.gp05_wrapper
#print axioms QuantumNLS.Ext025L.iter_identity
#print axioms QuantumNLS.Ext025L.avg_fderiv
