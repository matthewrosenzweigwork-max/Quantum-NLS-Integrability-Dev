import QuantumNLS.HolomorphicStageD1
import QuantumNLS.HolomorphicStageD2
import QuantumNLS.HolomorphicStageD3
import QuantumNLS.Ext025A4AnalyticFlow

/-!
# EXT-025 layer A: contract theorem for FIN-EXT025-GP-05

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

Lean reading (`contract_GP05`, conjunction of the clauses below).
* (1) one complex variable, Banach target: if `f` is differentiable on an open `U` containing
  the closed disk and `‖f‖ ≤ M` on the circle, then the Cauchy estimates
  `‖f^(n)(c)‖ ≤ n! M / R^n` hold for all `n`, and `f` is the sum of a power series on the disk.
* (2) Banach domain (`E` a nontrivial complex normed space, target complete): bounded on the
  sphere `{‖w-x‖=R} ⊆ ` closed ball `⊆ U`; the maximum principle on complex lines gives the bound
  on the whole ball; the full operator-norm Cauchy bound for all Frechet derivatives holds, and
  on the smaller ball of radius `R/(4e)` the series of bounded multilinear maps
  `(n!)⁻¹ D^n f(x)` converges to `f` with the coefficient bounds `‖p_n‖ r^n ≤ M e` (the
  "polarization" clause is the multilinear, not merely diagonal, form of the coefficients).
* (3) holomorphy is preserved under limits that are uniform on a neighbourhood of every point
  (the notion of local uniformity for Banach domains), under sums that are locally dominated
  by a summable series (and their Frechet derivatives are bounded term by term by the
  Cauchy bound), and under integration against a measure with an integrable bound
  (clause (4)).
* (4) bounded integration: `Φ : E → T → F` holomorphic in the parameter for a.e. `t`, jointly
  a.e. bounded by an integrable `b(t)` on `U`, measurable in `t`; then `w ↦ ∫ Φ(w,t) dμ(t)` is
  holomorphic on `U`.
Banach domains and targets are in one universe `Type u` (as the frozen
`HolomorphicStageD3` requires).  No admitted interface or held identifier is used.
-/
set_option autoImplicit false
set_option maxHeartbeats 3200000
noncomputable section
open Set Filter Topology Metric MeasureTheory
open scoped ENNReal NNReal

namespace QuantumNLS.Ext025L

universe u v w

/-- Clause (1): Cauchy estimates in one complex variable with a Banach target. -/
def GP05_one : Prop :=
  ∀ (F : Type v) [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (f : ℂ → F) (U : Set ℂ) (c : ℂ) (R M : ℝ), IsOpen U → 0 < R → closedBall c R ⊆ U →
    DifferentiableOn ℂ f U → (∀ z ∈ sphere c R, ‖f z‖ ≤ M) →
    (∀ n : ℕ, ‖iteratedDeriv n f c‖ ≤ n.factorial * M / R ^ n) ∧ ‖deriv f c‖ ≤ M / R ∧
    ∃ p : FormalMultilinearSeries ℂ ℂ F, HasFPowerSeriesOnBall f p c (R.toNNReal : ℝ≥0∞)

theorem gp05_one : GP05_one.{v} := by
  intro F _ _ _ f U c R M hU hR hcl hd hM
  have hdc : DifferentiableOn ℂ f (closedBall c R) := hd.mono hcl
  have hdcl : DiffContOnCl ℂ f (ball c R) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball c hR.ne']
    exact hdc
  have h1 : ∀ n : ℕ, ‖iteratedDeriv n f c‖ ≤ n.factorial * M / R ^ n := fun n =>
    Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR hdcl hM
  refine ⟨h1, ?_, ?_⟩
  · have := h1 1
    simpa using this
  · have hd' : DifferentiableOn ℂ f (closedBall c ((R.toNNReal : ℝ≥0) : ℝ)) := by
      rw [Real.coe_toNNReal _ hR.le]
      exact hdc
    exact ⟨_, hd'.hasFPowerSeriesOnBall (by simpa using hR)⟩

/-- Clause (2): Cauchy bounds and the multilinear series in a Banach domain. -/
def GP05_banach : Prop :=
  ∀ (E F : Type u) [NormedAddCommGroup E] [NormedSpace ℂ E] [Nontrivial E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (f : E → F) (U : Set E) (x : E) (R M : ℝ), IsOpen U → 0 < R → 0 ≤ M →
    closedBall x R ⊆ U → DifferentiableOn ℂ f U → (∀ w ∈ sphere x R, ‖f w‖ ≤ M) →
    (∀ w ∈ closedBall x R, ‖f w‖ ≤ M) ∧
    (∀ n : ℕ, ‖iteratedFDeriv ℂ n f x‖ ≤ M * (4 * ((n : ℝ) + 1) / R) ^ n) ∧
    (∀ n : ℕ, ‖((n.factorial : ℂ))⁻¹ • iteratedFDeriv ℂ n f x‖ * (R / (4 * Real.exp 1)) ^ n ≤
      M * Real.exp 1) ∧
    HasFPowerSeriesOnBall f (fun n : ℕ => ((n.factorial : ℂ))⁻¹ • iteratedFDeriv ℂ n f x) x
      (ENNReal.ofReal (R / (4 * Real.exp 1)))

theorem gp05_banach : GP05_banach.{u} := by
  intro E F _ _ _ _ _ _ f U x R M hU hR hM0 hcl hf hMs
  have hdc : DifferentiableOn ℂ f (closedBall x R) := hf.mono hcl
  have hball : ∀ w ∈ closedBall x R, ‖f w‖ ≤ M := by
    intro w hw
    have hdcl : DiffContOnCl ℂ f (ball x R) := by
      refine DifferentiableOn.diffContOnCl ?_
      rw [closure_ball x hR.ne']
      exact hdc
    refine Complex.norm_le_of_forall_mem_frontier_norm_le (U := ball x R) Metric.isBounded_ball
      hdcl ?_ (by rwa [closure_ball x hR.ne'])
    intro z hz
    rw [frontier_ball x hR.ne'] at hz
    exact hMs z hz
  have hxU : ball x R ⊆ U := ball_subset_closedBall.trans hcl
  have hx : x ∈ U := hcl (mem_closedBall_self hR.le)
  have hM : ∀ z ∈ ball x R, ‖f z‖ ≤ M := fun z hz => hball z (ball_subset_closedBall hz)
  have hexp : (2 : ℝ) < Real.exp 1 := by
    have := Real.add_one_lt_exp (one_ne_zero : (1 : ℝ) ≠ 0)
    linarith
  set r0 : ℝ := R / (4 * Real.exp 1) with hr0_def
  have hr0 : 0 < r0 := div_pos hR (by positivity)
  have hr0_lt : r0 < R / 2 := by
    rw [hr0_def, div_lt_iff₀ (by positivity)]
    nlinarith
  refine ⟨hball, fun n => HolomorphicStageD1.norm_iteratedFDeriv_le hU hf hR hM0 hxU hM n,
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
      exact hsmul s (by simpa [mem_ball_zero_iff] using hs)
    have hgd : DifferentiableOn ℂ (fun s : ℂ => f (x + s • y)) (ball (0 : ℂ) 2) :=
      DifferentiableOn.comp hf hlin hmaps
    have h1mem : (1 : ℂ) ∈ ball (0 : ℂ) 2 := by
      simp [mem_ball_zero_iff]
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

/-- Clause (3a): limits uniform on a neighbourhood of each point. -/
def GP05_limit : Prop :=
  ∀ (E F : Type u) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (f : ℕ → E → F) (g : E → F) (U : Set E), IsOpen U → (∀ n, DifferentiableOn ℂ (f n) U) →
    (∀ x ∈ U, ∃ N ∈ 𝓝 x, TendstoUniformlyOn f g atTop N) →
    DifferentiableOn ℂ g U ∧ AnalyticOnNhd ℂ g U

theorem gp05_limit : GP05_limit.{u} := by
  intro E F _ _ _ _ _ f g U hU hf hlim
  have hd : DifferentiableOn ℂ g U := by
    intro a ha
    obtain ⟨N, hN, hu⟩ := hlim a ha
    obtain ⟨R, hR, hRsub⟩ := Metric.mem_nhds_iff.mp (inter_mem hN (hU.mem_nhds ha))
    have hsub : ball a R ⊆ N := fun z hz => (hRsub hz).1
    have hsubU : ball a R ⊆ U := fun z hz => (hRsub hz).2
    have h := Ext025A4AnalyticLimit.differentiableOn_uniformLimit hR
      (fun n => (hf n).mono hsubU) (hu.mono hsub)
    exact (h.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self (half_pos hR)))).differentiableWithinAt
  exact ⟨hd, HolomorphicStageD3.analyticOnNhd_of_differentiableOn hU hd⟩

/-- Clause (3b): sums locally dominated by a summable series. -/
def GP05_sum : Prop :=
  ∀ (E F : Type u) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (f : ℕ → E → F) (U : Set E), IsOpen U → (∀ k, DifferentiableOn ℂ (f k) U) →
    (∀ x ∈ U, ∃ N ∈ 𝓝 x, ∃ b : ℕ → ℝ, Summable b ∧ ∀ k, ∀ w ∈ N, ‖f k w‖ ≤ b k) →
    DifferentiableOn ℂ (fun w => ∑' k, f k w) U ∧ AnalyticOnNhd ℂ (fun w => ∑' k, f k w) U

theorem gp05_sum : GP05_sum.{u} := by
  intro E F _ _ _ _ _ f U hU hf hloc
  refine gp05_limit E F (fun n w => ∑ k ∈ Finset.range n, f k w) (fun w => ∑' k, f k w) U hU
    (fun n => DifferentiableOn.fun_sum fun k _ => hf k) ?_
  intro x hx
  obtain ⟨N, hN, b, hb, hfb⟩ := hloc x hx
  refine ⟨N, hN, ?_⟩
  have h := tendstoUniformlyOn_tsum hb (s := N) (f := f) hfb
  have hc : Tendsto Finset.range atTop atTop := tendsto_finset_range
  exact fun u hu => hc.eventually (h u hu)

/-- Clause (3c): derivative bounds for a series with summable circle bounds. -/
def GP05_series_bounds : Prop :=
  ∀ (E F : Type u) [NormedAddCommGroup E] [NormedSpace ℂ E] [Nontrivial E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (f : ℕ → E → F) (U : Set E) (x : E) (R : ℝ) (b : ℕ → ℝ), IsOpen U → 0 < R →
    closedBall x R ⊆ U → (∀ k, DifferentiableOn ℂ (f k) U) → Summable b →
    (∀ k, ∀ w ∈ sphere x R, ‖f k w‖ ≤ b k) →
    (∀ n : ℕ, Summable fun k => ‖iteratedFDeriv ℂ n (f k) x‖) ∧
    (∀ n : ℕ, ‖iteratedFDeriv ℂ n (fun w => ∑' k, f k w) x‖ ≤
      (∑' k, b k) * (4 * ((n : ℝ) + 1) / R) ^ n)

theorem gp05_series_bounds : GP05_series_bounds.{u} := by
  intro E F _ _ _ _ _ _ f U x R b hU hR hcl hf hb hbound
  have hb0 : ∀ k, 0 ≤ b k := by
    intro k
    obtain ⟨w, hw⟩ := (NormedSpace.sphere_nonempty (x := x) (r := R)).mpr hR.le
    exact (norm_nonneg _).trans (hbound k w hw)
  have hxU : ball x R ⊆ U := ball_subset_closedBall.trans hcl
  have hball : ∀ k, ∀ w ∈ closedBall x R, ‖f k w‖ ≤ b k := fun k =>
    (gp05_banach E F (f k) U x R (b k) hU hR (hb0 k) hcl (hf k) (hbound k)).1
  have hsum0 : 0 ≤ ∑' k, b k := tsum_nonneg hb0
  refine ⟨fun n => ?_, fun n => ?_⟩
  · refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
      (hb.mul_right ((4 * ((n : ℝ) + 1) / R) ^ n))
    exact (gp05_banach E F (f k) U x R (b k) hU hR (hb0 k) hcl (hf k) (hbound k)).2.1 n
  · have hdiff : DifferentiableOn ℂ (fun w => ∑' k, f k w) (ball x R) := by
      refine (gp05_sum E F f (ball x R) isOpen_ball (fun k => (hf k).mono hxU) ?_).1
      intro w hw
      exact ⟨ball x R, isOpen_ball.mem_nhds hw, b, hb,
        fun k z hz => hball k z (ball_subset_closedBall hz)⟩
    have hgM : ∀ z ∈ ball x R, ‖∑' k, f k z‖ ≤ ∑' k, b k := by
      intro z hz
      exact tsum_of_norm_bounded hb.hasSum fun k => hball k z (ball_subset_closedBall hz)
    exact HolomorphicStageD1.norm_iteratedFDeriv_le isOpen_ball hdiff hR hsum0 subset_rfl hgM n

/-- Clause (4): bounded integration, holomorphic parameter on an open set of `ℂ`,
Banach-valued integrand. -/
def GP05_int : Prop :=
  ∀ (F : Type v) [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (T : Type w) [MeasurableSpace T] (μ : Measure T) (Φ : ℂ → T → F) (U : Set ℂ) (b : T → ℝ),
    IsOpen U → Integrable b μ → (∀ w ∈ U, AEStronglyMeasurable (Φ w) μ) →
    (∀ᵐ t ∂μ, DifferentiableOn ℂ (fun w => Φ w t) U ∧ ∀ w ∈ U, ‖Φ w t‖ ≤ b t) →
    DifferentiableOn ℂ (fun w => ∫ t, Φ w t ∂μ) U

theorem gp05_int : GP05_int.{v, w} := by
  intro F _ _ _ T _ μ Φ U b hU hb hm hg w0 hw0
  obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.mp hU w0 hw0
  have hint : ∀ w ∈ U, Integrable (Φ w) μ := fun w hw =>
    hb.mono' (hm w hw) (by filter_upwards [hg] with t ht using ht.2 w hw)
  have hcb : ∀ w ∈ ball w0 (R / 2), closedBall w (R / 2) ⊆ U := by
    intro w hw z hz
    apply hRU
    rw [mem_ball] at hw ⊢
    rw [mem_closedBall] at hz
    have := dist_triangle z w w0
    linarith
  have hhalf : ball w0 (R / 2) ⊆ U := fun w hw => hRU (ball_subset_ball (by linarith) hw)
  have hder : ∀ᵐ t ∂μ, ∀ w ∈ ball w0 (R / 2),
      HasDerivAt (fun z => Φ z t) (deriv (fun z => Φ z t) w) w ∧
      ‖deriv (fun z => Φ z t) w‖ ≤ b t / (R / 2) := by
    filter_upwards [hg] with t ht w hw
    have hdiff : DifferentiableOn ℂ (fun z => Φ z t) (closedBall w (R / 2)) :=
      ht.1.mono (hcb w hw)
    refine ⟨(ht.1.differentiableAt (hU.mem_nhds
      (hcb w hw (mem_closedBall_self (by linarith))))).hasDerivAt, ?_⟩
    have hdcl : DiffContOnCl ℂ (fun z => Φ z t) (ball w (R / 2)) := by
      refine DifferentiableOn.diffContOnCl ?_
      rw [closure_ball w (by linarith)]
      exact hdiff
    exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (half_pos hR) hdcl
      (fun z hz => ht.2 z (hcb w hw (sphere_subset_closedBall hz)))
  set s : ℕ → ℂ := fun n => ((R / 4 : ℝ) : ℂ) / ((n + 1 : ℕ) : ℂ) with hs
  have hR4 : ((R / 4 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by linarith : R / 4 ≠ 0)
  have hs0 : Tendsto s atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩
    · exact (tendsto_const_div_atTop_nhds_zero_nat ((R / 4 : ℝ) : ℂ)).comp
        (tendsto_add_atTop_nat 1)
    · simp only [hs, mem_compl_iff, mem_singleton_iff]
      exact div_ne_zero hR4 (by exact_mod_cast Nat.succ_ne_zero n)
  have hsmem : ∀ n, w0 + s n ∈ ball w0 (R / 2) := by
    intro n
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
    simp only [hs, norm_div, Complex.norm_natCast]
    have h1 : ‖((R / 4 : ℝ) : ℂ)‖ = R / 4 := by
      rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    rw [h1]
    have h2 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    calc R / 4 / ((n + 1 : ℕ) : ℝ) ≤ R / 4 / 1 := by gcongr
      _ < R / 2 := by linarith
  have hmeasD : AEStronglyMeasurable (fun t => deriv (fun z => Φ z t) w0) μ := by
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun n t => (s n)⁻¹ • (Φ (w0 + s n) t - Φ w0 t)) (fun n => ?_) ?_
    · have h1 := hm (w0 + s n) (hhalf (hsmem n))
      have h2 := hm w0 hw0
      exact (h1.sub h2).const_smul _
    · filter_upwards [hder] with t ht
      have hd := (ht w0 (mem_ball_self (by linarith))).1
      exact (hasDerivAt_iff_tendsto_slope_zero.mp hd).comp hs0
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := w0)
    (F := fun w t => Φ w t) (F' := fun w t => deriv (fun z => Φ z t) w)
    (bound := fun t => b t / (R / 2)) (s := ball w0 (R / 2)) (ball_mem_nhds w0 (half_pos hR))
    (Filter.mem_of_superset (ball_mem_nhds w0 (half_pos hR)) fun w hw => hm w (hhalf hw))
    (hint w0 hw0) hmeasD
    (by filter_upwards [hder] with t ht w hw using (ht w hw).2) (hb.div_const _)
    (by filter_upwards [hder] with t ht w hw using (ht w hw).1)
  exact hmain.2.differentiableAt.differentiableWithinAt

/-- FIN-EXT025-GP-05 as a Lean theorem.  NOTE: clause (4) is stated for a scalar
(`ℂ`) parameter; the Banach-domain parameter integral is NOT part of this theorem. -/
theorem contract_GP05 :
    GP05_one.{v} ∧ GP05_banach.{u} ∧ GP05_limit.{u} ∧ GP05_sum.{u} ∧ GP05_series_bounds.{u} ∧
      GP05_int.{v, w} :=
  ⟨gp05_one, gp05_banach, gp05_limit, gp05_sum, gp05_series_bounds, gp05_int⟩

end QuantumNLS.Ext025L

#print axioms QuantumNLS.Ext025L.contract_GP05
