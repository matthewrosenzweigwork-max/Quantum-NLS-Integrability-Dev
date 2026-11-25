import NlsGge.Ramer.DivergenceProductRule

/-!
# Finite Gaussian divergence estimate under polynomial growth

See `FiniteDivergenceGrowth.md`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter Real
open scoped Topology RealInnerProductSpace ENNReal

namespace NlsGge.Ramer

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### Gaussian polynomial moments -/

theorem integrable_rexp_neg_quarter_sq_norm :
    Integrable (fun x : V => Real.exp (-(1 / 4 : ℝ) * ‖x‖ ^ 2)) := by
  apply Integrable.of_integral_ne_zero
  rw [GaussianFourier.integral_rexp_neg_mul_sq_norm (V := V) (b := (1 / 4 : ℝ)) (by norm_num)]
  exact (Real.rpow_pos_of_pos (by positivity) _).ne'

theorem pow_one_add_mul_exp_le (m : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    (1 + r) ^ m * Real.exp (-(1 / 2 : ℝ) * r ^ 2) ≤
      (m.factorial : ℝ) * Real.exp 2 * Real.exp (-(1 / 4 : ℝ) * r ^ 2) := by
  have h1 : (1 + r) ^ m / (m.factorial : ℝ) ≤ Real.exp (1 + r) :=
    Real.pow_div_factorial_le_exp _ (by linarith) m
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast m.factorial_pos
  have h2 : (1 + r) ^ m ≤ (m.factorial : ℝ) * Real.exp (1 + r) := by
    rwa [div_le_iff₀ hf, mul_comm] at h1
  have h3 : Real.exp (1 + r) ≤ Real.exp 2 * Real.exp ((1 / 4 : ℝ) * r ^ 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg (r / 2 - 1)]
  calc (1 + r) ^ m * Real.exp (-(1 / 2 : ℝ) * r ^ 2)
      ≤ ((m.factorial : ℝ) * (Real.exp 2 * Real.exp ((1 / 4 : ℝ) * r ^ 2))) *
          Real.exp (-(1 / 2 : ℝ) * r ^ 2) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact h2.trans (mul_le_mul_of_nonneg_left h3 hf.le)
    _ = (m.factorial : ℝ) * Real.exp 2 * Real.exp (-(1 / 4 : ℝ) * r ^ 2) := by
        have : Real.exp ((1 / 4 : ℝ) * r ^ 2) * Real.exp (-(1 / 2 : ℝ) * r ^ 2) =
            Real.exp (-(1 / 4 : ℝ) * r ^ 2) := by
          rw [← Real.exp_add]; congr 1; ring
        calc _ = (m.factorial : ℝ) * Real.exp 2 *
              (Real.exp ((1 / 4 : ℝ) * r ^ 2) * Real.exp (-(1 / 2 : ℝ) * r ^ 2)) := by ring
          _ = _ := by rw [this]

/-- Polynomial moments of the finite standard Gaussian. -/
theorem integrable_pow_one_add_norm (m : ℕ) :
    Integrable (fun x : V => (1 + ‖x‖) ^ m) (finiteStdGaussian V) := by
  rw [finiteStdGaussian, integrable_withDensity_iff_integrable_smul'
    (continuous_finiteGaussianDensity.measurable.ennreal_ofReal)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  have hmeas : AEStronglyMeasurable (fun x : V => ((ENNReal.ofReal (finiteGaussianDensity V x)).toReal •
      (1 + ‖x‖) ^ m)) volume := by
    have : Continuous (fun x : V => finiteGaussianDensity V x * (1 + ‖x‖) ^ m) := by
      have := continuous_finiteGaussianDensity (V := V); fun_prop
    refine this.aestronglyMeasurable.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [ENNReal.toReal_ofReal (finiteGaussianDensity_pos x).le]
  refine Integrable.mono' (g := fun x : V => ((2 * π) ^ (-(Module.finrank ℝ V : ℝ) / 2) *
    ((m.factorial : ℝ) * Real.exp 2)) * Real.exp (-(1 / 4 : ℝ) * ‖x‖ ^ 2))
    (integrable_rexp_neg_quarter_sq_norm.const_mul _) hmeas (Filter.Eventually.of_forall fun x => ?_)
  rw [ENNReal.toReal_ofReal (finiteGaussianDensity_pos x).le, smul_eq_mul, Real.norm_eq_abs,
    abs_of_nonneg (by have := finiteGaussianDensity_pos (V := V) x; positivity)]
  unfold finiteGaussianDensity
  have := pow_one_add_mul_exp_le m ‖x‖ (norm_nonneg x)
  have hc : (0 : ℝ) ≤ (2 * π) ^ (-(Module.finrank ℝ V : ℝ) / 2) := by positivity
  have e : Real.exp (-(‖x‖ ^ 2) / 2) = Real.exp (-(1 / 2 : ℝ) * ‖x‖ ^ 2) := by congr 1; ring
  rw [e]
  calc (2 * π) ^ (-(Module.finrank ℝ V : ℝ) / 2) * Real.exp (-(1 / 2 : ℝ) * ‖x‖ ^ 2) *
        (1 + ‖x‖) ^ m
      = (2 * π) ^ (-(Module.finrank ℝ V : ℝ) / 2) *
        ((1 + ‖x‖) ^ m * Real.exp (-(1 / 2 : ℝ) * ‖x‖ ^ 2)) := by ring
    _ ≤ (2 * π) ^ (-(Module.finrank ℝ V : ℝ) / 2) *
        ((m.factorial : ℝ) * Real.exp 2 * Real.exp (-(1 / 4 : ℝ) * ‖x‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left this hc
    _ = _ := by ring

/-- Integrability from a polynomial bound. -/
theorem integrable_of_le_poly {g : V → ℝ} (hg : AEStronglyMeasurable g (finiteStdGaussian V))
    (K : ℝ) (m : ℕ) (h : ∀ x, ‖g x‖ ≤ K * (1 + ‖x‖) ^ m) :
    Integrable g (finiteStdGaussian V) :=
  Integrable.mono' ((integrable_pow_one_add_norm m).const_mul K) hg
    (Filter.Eventually.of_forall h)


/-! ### Pointwise bounds on trace, Hilbert–Schmidt norm and divergence -/

theorem abs_traceCLM_le (A : V →L[ℝ] V) :
    |traceCLM V A| ≤ (Module.finrank ℝ V : ℝ) * ‖A‖ := by
  set b := stdOrthonormalBasis ℝ V
  rw [traceCLM_eq_sum b]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ i ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ V))),
      |⟪b i, A (b i)⟫| ≤ ‖A‖ := by
    intro i _
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [b.orthonormal.1 i, one_mul]
    simpa [b.orthonormal.1 i] using A.le_opNorm (b i)
  refine (Finset.sum_le_sum this).trans ?_
  simp

theorem hsNormSq_le_finrank_sq_mul (A : V →L[ℝ] V) :
    hsNormSq A ≤ (Module.finrank ℝ V : ℝ) ^ 2 * ‖A‖ ^ 2 := by
  set b := stdOrthonormalBasis ℝ V
  unfold hsNormSq
  have : ∀ i j, ⟪b i, A (b j)⟫ ^ 2 ≤ ‖A‖ ^ 2 := by
    intro i j
    have h1 : |⟪b i, A (b j)⟫| ≤ ‖A‖ := by
      refine (abs_real_inner_le_norm _ _).trans ?_
      simpa [b.orthonormal.1 i, b.orthonormal.1 j] using A.le_opNorm (b j)
    calc ⟪b i, A (b j)⟫ ^ 2 = |⟪b i, A (b j)⟫| ^ 2 := (sq_abs _).symm
      _ ≤ ‖A‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  calc ∑ i, ∑ j, ⟪b i, A (b j)⟫ ^ 2 ≤ ∑ _i : Fin (Module.finrank ℝ V), ∑ _j : Fin (Module.finrank ℝ V), ‖A‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => this i j
    _ = _ := by simp; ring

/-- Polynomial bound for the divergence from polynomial bounds on `F` and `DF`. -/
theorem abs_finiteGaussianDivergence_le_poly {F : V → V} {A B : ℝ} {k : ℕ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (x : V)
    (hF : ‖F x‖ ≤ A * (1 + ‖x‖) ^ k) (hD : ‖fderiv ℝ F x‖ ≤ B * (1 + ‖x‖) ^ k) :
    |finiteGaussianDivergence F x| ≤
      (A + (Module.finrank ℝ V : ℝ) * B) * (1 + ‖x‖) ^ (k + 1) := by
  have hd : |finiteGaussianDivergence F x| ≤
      ‖x‖ * ‖F x‖ + (Module.finrank ℝ V : ℝ) * ‖fderiv ℝ F x‖ := by
    rw [finiteGaussianDivergence_eq_traceCLM]
    refine (abs_sub _ _).trans (add_le_add ?_ (abs_traceCLM_le _))
    exact (abs_real_inner_le_norm _ _)
  have hp : (1 + ‖x‖) ^ k ≤ (1 + ‖x‖) ^ (k + 1) :=
    pow_le_pow_right₀ (by linarith [norm_nonneg x]) (Nat.le_succ k)
  have hx : ‖x‖ ≤ 1 + ‖x‖ := by linarith
  have hk : 0 ≤ (1 + ‖x‖) ^ k := by positivity
  have hfd : (0 : ℝ) ≤ Module.finrank ℝ V := Nat.cast_nonneg _
  calc |finiteGaussianDivergence F x|
      ≤ ‖x‖ * ‖F x‖ + (Module.finrank ℝ V : ℝ) * ‖fderiv ℝ F x‖ := hd
    _ ≤ ‖x‖ * (A * (1 + ‖x‖) ^ k) + (Module.finrank ℝ V : ℝ) * (B * (1 + ‖x‖) ^ k) :=
        add_le_add (mul_le_mul_of_nonneg_left hF (norm_nonneg _))
          (mul_le_mul_of_nonneg_left hD hfd)
    _ ≤ (1 + ‖x‖) * (A * (1 + ‖x‖) ^ k) + (Module.finrank ℝ V : ℝ) * (B * (1 + ‖x‖) ^ (k + 1)) := by
        gcongr
    _ = (A + (Module.finrank ℝ V : ℝ) * B) * (1 + ‖x‖) ^ (k + 1) := by ring


/-! ### Dominated convergence with polynomial domination -/

theorem tendsto_integral_of_poly_bound {g : ℕ → V → ℝ} {g0 : V → ℝ}
    (hmeas : ∀ n, AEStronglyMeasurable (g n) (finiteStdGaussian V))
    (K : ℝ) (m : ℕ) (hb : ∀ n x, ‖g n x‖ ≤ K * (1 + ‖x‖) ^ m)
    (hev : ∀ x, ∃ N, ∀ n ≥ N, g n x = g0 x) :
    Tendsto (fun n => ∫ x, g n x ∂(finiteStdGaussian V)) atTop
      (𝓝 (∫ x, g0 x ∂(finiteStdGaussian V))) := by
  refine tendsto_integral_of_dominated_convergence (fun x => K * (1 + ‖x‖) ^ m) hmeas
    ((integrable_pow_one_add_norm m).const_mul K)
    (fun n => Filter.Eventually.of_forall (hb n)) (Filter.Eventually.of_forall fun x => ?_)
  obtain ⟨N, hN⟩ := hev x
  exact tendsto_const_nhds.congr' (Filter.eventually_atTop.2 ⟨N, fun n hn => (hN n hn).symm⟩)

/-! ### The cutoff -/

variable (V) in
/-- Fixed smooth bump: `1` on the closed unit ball, supported in the ball of radius `2`. -/
def stdCut : ContDiffBump (0 : V) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The rescaled cutoff `x ↦ χ(x/R)`. -/
def cutR (R : ℝ) (x : V) : ℝ := stdCut V (R⁻¹ • x)

theorem contDiff_cutR (R : ℝ) (n : ℕ) : ContDiff ℝ n (cutR (V := V) R) := by
  have h : ContDiff ℝ n (stdCut V) := by exact_mod_cast (stdCut V).contDiff (n := n)
  exact h.comp (contDiff_const.smul contDiff_id)

theorem cutR_nonneg (R : ℝ) (x : V) : 0 ≤ cutR R x := (stdCut V).nonneg

theorem cutR_le_one (R : ℝ) (x : V) : cutR R x ≤ 1 := (stdCut V).le_one

theorem hasCompactSupport_cutR {R : ℝ} (hR : 0 < R) : HasCompactSupport (cutR (V := V) R) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : V) (2 * R)) fun x hx => ?_
  rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx
  apply (stdCut V).zero_of_le_dist
  rw [dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hR]
  show 2 ≤ R⁻¹ * ‖x‖
  rw [← div_eq_inv_mul, le_div_iff₀ hR]
  linarith

theorem cutR_eq_one {R : ℝ} (hR : 0 < R) {x : V} (hx : ‖x‖ < R) : cutR R x = 1 := by
  apply (stdCut V).one_of_mem_closedBall
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs,
    abs_of_pos hR]
  show R⁻¹ * ‖x‖ ≤ 1
  rw [← div_eq_inv_mul, div_le_one hR]
  exact hx.le

/-- Uniform bound on the derivative of the rescaled cutoff, for `R ≥ 1`. -/
theorem exists_norm_fderiv_cutR_le :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ R : ℝ, 1 ≤ R → ∀ x : V, ‖fderiv ℝ (cutR R) x‖ ≤ M := by
  have h1 : ContDiff ℝ 1 (stdCut V) := by exact_mod_cast (stdCut V).contDiff (n := 1)
  have hc : Continuous (fderiv ℝ (stdCut V)) := h1.continuous_fderiv (by simp)
  obtain ⟨M, hM⟩ := hc.bounded_above_of_compact_support
    ((stdCut V).hasCompactSupport.fderiv ℝ)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  refine ⟨M, hM0, fun R hR x => ?_⟩
  have hR0 : 0 < R := by linarith
  have hd : DifferentiableAt ℝ (stdCut V) (R⁻¹ • x) :=
    (h1.differentiable (by simp)) _
  have h := hd.hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul R⁻¹)
  have h2 : fderiv ℝ (cutR (V := V) R) x =
      (fderiv ℝ (stdCut V) (R⁻¹ • x)).comp (R⁻¹ • ContinuousLinearMap.id ℝ V) := by
    exact h.fderiv
  rw [h2]
  refine ContinuousLinearMap.opNorm_le_bound _ hM0 fun v => ?_
  have hinv : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR
  calc ‖((fderiv ℝ (stdCut V) (R⁻¹ • x)).comp (R⁻¹ • ContinuousLinearMap.id ℝ V)) v‖
      = ‖fderiv ℝ (stdCut V) (R⁻¹ • x) (R⁻¹ • v)‖ := by simp
    _ ≤ ‖fderiv ℝ (stdCut V) (R⁻¹ • x)‖ * ‖R⁻¹ • v‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ M * ‖v‖ := by
        have : ‖R⁻¹ • v‖ ≤ ‖v‖ := by
          rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hR0]
          exact mul_le_of_le_one_left (norm_nonneg _) hinv
        exact mul_le_mul (hM _) this (norm_nonneg _) hM0


/-! ### The cut-off field `χ_R F` -/

theorem sq_norm_le_poly {a K p : ℝ} (m : ℕ) (h : |a| ≤ K * p ^ m) :
    ‖a ^ 2‖ ≤ K ^ 2 * p ^ (2 * m) := by
  rw [Real.norm_eq_abs, abs_pow]
  calc |a| ^ 2 ≤ (K * p ^ m) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
    _ = K ^ 2 * p ^ (2 * m) := by rw [mul_pow, ← pow_mul, mul_comm m 2]

theorem sq_le_poly_of_nonneg {y K p : ℝ} (hy : 0 ≤ y) (m : ℕ) (h : y ≤ K * p ^ m) :
    y ^ 2 ≤ K ^ 2 * p ^ (2 * m) := by
  have := sq_norm_le_poly (a := y) m (by rwa [abs_of_nonneg hy])
  rwa [Real.norm_eq_abs, abs_pow, abs_of_nonneg hy] at this

theorem norm_cutR_smul_le (R : ℝ) (F : V → V) (x : V) : ‖cutR R x • F x‖ ≤ ‖F x‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (cutR_nonneg R x)]
  exact mul_le_of_le_one_left (norm_nonneg _) (cutR_le_one R x)

theorem fderiv_cutR_smul {F : V → V} (hF : Differentiable ℝ F) (R : ℝ) (x : V) :
    fderiv ℝ (fun y => cutR R y • F y) x =
      cutR R x • fderiv ℝ F x + (fderiv ℝ (cutR R) x).smulRight (F x) := by
  have hc : DifferentiableAt ℝ (cutR (V := V) R) x :=
    ((contDiff_cutR (V := V) R 1).differentiable (by simp)) x
  exact (hc.hasFDerivAt.smul (hF x).hasFDerivAt).fderiv

theorem norm_fderiv_cutR_smul_le {F : V → V} (hF : Differentiable ℝ F) {R M : ℝ}
    (hM : ∀ x : V, ‖fderiv ℝ (cutR (V := V) R) x‖ ≤ M) (x : V) :
    ‖fderiv ℝ (fun y => cutR R y • F y) x‖ ≤ ‖fderiv ℝ F x‖ + M * ‖F x‖ := by
  rw [fderiv_cutR_smul hF]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (cutR_nonneg R x)]
    exact mul_le_of_le_one_left (norm_nonneg _) (cutR_le_one R x)
  · rw [ContinuousLinearMap.norm_smulRight_apply]
    exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _)

theorem cutR_smul_eventuallyEq {R : ℝ} (hR : 0 < R) (F : V → V) {x : V} (hx : ‖x‖ < R) :
    (fun y => cutR R y • F y) =ᶠ[𝓝 x] F := by
  have hU : Metric.ball (0 : V) R ∈ 𝓝 x := Metric.isOpen_ball.mem_nhds (by simpa using hx)
  filter_upwards [hU] with y hy
  rw [cutR_eq_one hR (by simpa using hy), one_smul]

theorem finiteGaussianDivergence_cutR_smul {R : ℝ} (hR : 0 < R) (F : V → V) {x : V}
    (hx : ‖x‖ < R) :
    finiteGaussianDivergence (fun y => cutR R y • F y) x = finiteGaussianDivergence F x :=
  finiteGaussianDivergence_congr_of_eventuallyEq (cutR_smul_eventuallyEq hR F hx)

theorem fderiv_cutR_smul_eq {R : ℝ} (hR : 0 < R) (F : V → V) {x : V} (hx : ‖x‖ < R) :
    fderiv ℝ (fun y => cutR R y • F y) x = fderiv ℝ F x :=
  (cutR_smul_eventuallyEq hR F hx).fderiv_eq


/-! ### Main estimate -/

/-- **Finite-dimensional `L²` divergence estimate under polynomial growth.** For a `C²` field
`F` with `‖F x‖, ‖DF x‖ ≤ C (1 + ‖x‖)^k`, all of `(δF)²`, `‖F‖²`, `‖DF‖²_HS` are
`γ`-integrable and `∫ (δF)² dγ ≤ ∫ ‖F‖² dγ + ∫ ‖DF‖²_HS dγ`. -/
theorem integral_sq_finiteGaussianDivergence_le_of_growth {F : V → V} (hF : ContDiff ℝ 2 F)
    (C : ℝ) (k : ℕ) (hFg : ∀ x, ‖F x‖ ≤ C * (1 + ‖x‖) ^ k)
    (hDg : ∀ x, ‖fderiv ℝ F x‖ ≤ C * (1 + ‖x‖) ^ k) :
    Integrable (fun x => (finiteGaussianDivergence F x) ^ 2) (finiteStdGaussian V) ∧
    Integrable (fun x => ‖F x‖ ^ 2) (finiteStdGaussian V) ∧
    Integrable (fun x => hsNormSq (fderiv ℝ F x)) (finiteStdGaussian V) ∧
    ∫ x, (finiteGaussianDivergence F x) ^ 2 ∂(finiteStdGaussian V) ≤
      ∫ x, ‖F x‖ ^ 2 ∂(finiteStdGaussian V) +
        ∫ x, hsNormSq (fderiv ℝ F x) ∂(finiteStdGaussian V) := by
  set d : ℝ := (Module.finrank ℝ V : ℝ) with hd
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  have hC : 0 ≤ C := by simpa using (norm_nonneg (F 0)).trans (hFg 0)
  have hF1 : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  have hFdiff : Differentiable ℝ F := hF.differentiable (by norm_num)
  obtain ⟨M, hM0, hM⟩ := exists_norm_fderiv_cutR_le (V := V)
  -- continuity of the integrands
  have hcont_F : Continuous (fun x => ‖F x‖ ^ 2) := by
    have := hF.continuous; fun_prop
  have hcont_D : Continuous (fun x => hsNormSq (fderiv ℝ F x)) := continuous_hsNormSq_fderiv hF
  have hcont_δ : Continuous (fun x => (finiteGaussianDivergence F x) ^ 2) :=
    (continuous_finiteGaussianDivergence hF1).pow 2
  -- polynomial bounds for F itself
  have hδb : ∀ x, |finiteGaussianDivergence F x| ≤ (C + d * C) * (1 + ‖x‖) ^ (k + 1) :=
    fun x => abs_finiteGaussianDivergence_le_poly hC hC x (hFg x) (hDg x)
  have hI1 : Integrable (fun x => (finiteGaussianDivergence F x) ^ 2) (finiteStdGaussian V) :=
    integrable_of_le_poly hcont_δ.aestronglyMeasurable _ _
      (fun x => sq_norm_le_poly (k + 1) (hδb x))
  have hI2 : Integrable (fun x => ‖F x‖ ^ 2) (finiteStdGaussian V) :=
    integrable_of_le_poly hcont_F.aestronglyMeasurable (C ^ 2) (2 * k) (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact sq_le_poly_of_nonneg (norm_nonneg _) k (hFg x))
  have hI3 : Integrable (fun x => hsNormSq (fderiv ℝ F x)) (finiteStdGaussian V) :=
    integrable_of_le_poly hcont_D.aestronglyMeasurable (d ^ 2 * C ^ 2) (2 * k) (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hsNormSq_nonneg _)]
      have h1 := hsNormSq_le_finrank_sq_mul (fderiv ℝ F x)
      have h2 : ‖fderiv ℝ F x‖ ^ 2 ≤ C ^ 2 * (1 + ‖x‖) ^ (2 * k) := by
        exact sq_le_poly_of_nonneg (norm_nonneg _) k (hDg x)
      calc hsNormSq (fderiv ℝ F x) ≤ d ^ 2 * ‖fderiv ℝ F x‖ ^ 2 := h1
        _ ≤ d ^ 2 * (C ^ 2 * (1 + ‖x‖) ^ (2 * k)) := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = d ^ 2 * C ^ 2 * (1 + ‖x‖) ^ (2 * k) := by ring)
  refine ⟨hI1, hI2, hI3, ?_⟩
  -- the cut-off sequence
  let Rn : ℕ → ℝ := fun n => (n : ℝ) + 1
  have hRn0 : ∀ n, 0 < Rn n := fun n => by positivity
  have hRn1 : ∀ n, 1 ≤ Rn n := fun n => by simp [Rn]
  let G : ℕ → V → V := fun n y => cutR (Rn n) y • F y
  have hG2 : ∀ n, ContDiff ℝ 2 (G n) := fun n => (contDiff_cutR _ 2).smul hF
  have hGc : ∀ n, HasCompactSupport (G n) := fun n =>
    (hasCompactSupport_cutR (hRn0 n)).smul_right
  have hG1 : ∀ n, ContDiff ℝ 1 (G n) := fun n => (hG2 n).of_le (by norm_num)
  -- bounds uniform in `n`
  have hGb : ∀ n x, ‖G n x‖ ≤ C * (1 + ‖x‖) ^ k :=
    fun n x => (norm_cutR_smul_le _ F x).trans (hFg x)
  have hGDb : ∀ n x, ‖fderiv ℝ (G n) x‖ ≤ (C * (1 + M)) * (1 + ‖x‖) ^ k := by
    intro n x
    have := norm_fderiv_cutR_smul_le hFdiff (R := Rn n) (hM _ (hRn1 n)) x
    refine this.trans ?_
    calc ‖fderiv ℝ F x‖ + M * ‖F x‖ ≤ C * (1 + ‖x‖) ^ k + M * (C * (1 + ‖x‖) ^ k) :=
          add_le_add (hDg x) (mul_le_mul_of_nonneg_left (hFg x) hM0)
      _ = (C * (1 + M)) * (1 + ‖x‖) ^ k := by ring
  have hB0 : 0 ≤ C * (1 + M) := by positivity
  have hGδb : ∀ n x, |finiteGaussianDivergence (G n) x| ≤
      (C + d * (C * (1 + M))) * (1 + ‖x‖) ^ (k + 1) :=
    fun n x => abs_finiteGaussianDivergence_le_poly hC hB0 x (hGb n x) (hGDb n x)
  -- eventual equality with the uncut quantities
  have hev : ∀ x : V, ∃ N : ℕ, ∀ n ≥ N, ‖x‖ < Rn n := by
    intro x
    obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
    exact ⟨N, fun n hn => by
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      simp only [Rn]; linarith⟩
  -- convergence of the three integrals
  have hL : Tendsto (fun n => ∫ x, (finiteGaussianDivergence (G n) x) ^ 2 ∂(finiteStdGaussian V))
      atTop (𝓝 (∫ x, (finiteGaussianDivergence F x) ^ 2 ∂(finiteStdGaussian V))) := by
    refine tendsto_integral_of_poly_bound (fun n => ?_) ((C + d * (C * (1 + M))) ^ 2) (2 * (k + 1))
      (fun n x => sq_norm_le_poly (k + 1) (hGδb n x)) (fun x => ?_)
    · exact ((continuous_finiteGaussianDivergence (hG1 n)).pow 2).aestronglyMeasurable
    · obtain ⟨N, hN⟩ := hev x
      exact ⟨N, fun n hn => by
        rw [finiteGaussianDivergence_cutR_smul (hRn0 n) F (hN n hn)]⟩
  have hR1 : Tendsto (fun n => ∫ x, ‖G n x‖ ^ 2 ∂(finiteStdGaussian V)) atTop
      (𝓝 (∫ x, ‖F x‖ ^ 2 ∂(finiteStdGaussian V))) := by
    refine tendsto_integral_of_poly_bound (fun n => ?_) (C ^ 2) (2 * k) (fun n x => ?_)
      (fun x => ?_)
    · have := (hG2 n).continuous; exact (by fun_prop : Continuous fun x => ‖G n x‖ ^ 2).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact sq_le_poly_of_nonneg (norm_nonneg _) k (hGb n x)
    · obtain ⟨N, hN⟩ := hev x
      refine ⟨N, fun n hn => ?_⟩
      show ‖cutR (Rn n) x • F x‖ ^ 2 = _
      rw [cutR_eq_one (hRn0 n) (hN n hn), one_smul]
  have hR2 : Tendsto (fun n => ∫ x, hsNormSq (fderiv ℝ (G n) x) ∂(finiteStdGaussian V)) atTop
      (𝓝 (∫ x, hsNormSq (fderiv ℝ F x) ∂(finiteStdGaussian V))) := by
    refine tendsto_integral_of_poly_bound (fun n => ?_) (d ^ 2 * (C * (1 + M)) ^ 2) (2 * k)
      (fun n x => ?_) (fun x => ?_)
    · exact (continuous_hsNormSq_fderiv (hG2 n)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (hsNormSq_nonneg _)]
      have h1 := hsNormSq_le_finrank_sq_mul (fderiv ℝ (G n) x)
      have h2 : ‖fderiv ℝ (G n) x‖ ^ 2 ≤ (C * (1 + M)) ^ 2 * (1 + ‖x‖) ^ (2 * k) := by
        exact sq_le_poly_of_nonneg (norm_nonneg _) k (hGDb n x)
      calc hsNormSq (fderiv ℝ (G n) x) ≤ d ^ 2 * ‖fderiv ℝ (G n) x‖ ^ 2 := h1
        _ ≤ d ^ 2 * ((C * (1 + M)) ^ 2 * (1 + ‖x‖) ^ (2 * k)) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = d ^ 2 * (C * (1 + M)) ^ 2 * (1 + ‖x‖) ^ (2 * k) := by ring
    · obtain ⟨N, hN⟩ := hev x
      exact ⟨N, fun n hn => by
        rw [show fderiv ℝ (G n) x = fderiv ℝ F x from fderiv_cutR_smul_eq (hRn0 n) F (hN n hn)]⟩
  refine le_of_tendsto_of_tendsto' hL (hR1.add hR2) fun n => ?_
  exact integral_sq_finiteGaussianDivergence_le (hG2 n) (hGc n)


/-! ### Gaussian integration by parts with bounded test functions -/

theorem fderiv_cutR_mul {φ : V → ℝ} (hφ : Differentiable ℝ φ) (R : ℝ) (x : V) :
    fderiv ℝ (fun y => cutR R y * φ y) x =
      cutR R x • fderiv ℝ φ x + φ x • fderiv ℝ (cutR R) x := by
  have hc : DifferentiableAt ℝ (cutR (V := V) R) x :=
    ((contDiff_cutR (V := V) R 1).differentiable (by simp)) x
  exact (hc.hasFDerivAt.mul (hφ x).hasFDerivAt).fderiv

theorem cutR_mul_eventuallyEq {R : ℝ} (hR : 0 < R) (φ : V → ℝ) {x : V} (hx : ‖x‖ < R) :
    (fun y => cutR R y * φ y) =ᶠ[𝓝 x] φ := by
  have hU : Metric.ball (0 : V) R ∈ 𝓝 x := Metric.isOpen_ball.mem_nhds (by simpa using hx)
  filter_upwards [hU] with y hy
  rw [cutR_eq_one hR (by simpa using hy), one_mul]

/-- **Gaussian integration by parts under polynomial growth.** For `C¹` `F` with
`‖F x‖, ‖DF x‖ ≤ C (1 + ‖x‖)^k` and `C¹` `φ` with `φ`, `Dφ` bounded,
`∫ φ δF dγ = ∫ Dφ(x)(F x) dγ`, both integrands being `γ`-integrable. -/
theorem integral_mul_finiteGaussianDivergence_of_growth {F : V → V} (hF : ContDiff ℝ 1 F)
    (C : ℝ) (k : ℕ) (hFg : ∀ x, ‖F x‖ ≤ C * (1 + ‖x‖) ^ k)
    (hDg : ∀ x, ‖fderiv ℝ F x‖ ≤ C * (1 + ‖x‖) ^ k)
    {φ : V → ℝ} (hφ : ContDiff ℝ 1 φ) (Bφ Bφ' : ℝ) (hφb : ∀ x, ‖φ x‖ ≤ Bφ)
    (hφ'b : ∀ x, ‖fderiv ℝ φ x‖ ≤ Bφ') :
    Integrable (fun x => φ x * finiteGaussianDivergence F x) (finiteStdGaussian V) ∧
    Integrable (fun x => fderiv ℝ φ x (F x)) (finiteStdGaussian V) ∧
    ∫ x, φ x * finiteGaussianDivergence F x ∂(finiteStdGaussian V) =
      ∫ x, fderiv ℝ φ x (F x) ∂(finiteStdGaussian V) := by
  set d : ℝ := (Module.finrank ℝ V : ℝ) with hd
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  have hC : 0 ≤ C := by simpa using (norm_nonneg (F 0)).trans (hFg 0)
  have hBφ : 0 ≤ Bφ := (norm_nonneg _).trans (hφb 0)
  have hBφ' : 0 ≤ Bφ' := (norm_nonneg _).trans (hφ'b 0)
  have hφdiff : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hFcont := hF.continuous
  have hδc := continuous_finiteGaussianDivergence hF
  have hφ'c : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by norm_num)
  have hδb : ∀ x, |finiteGaussianDivergence F x| ≤ (C + d * C) * (1 + ‖x‖) ^ (k + 1) :=
    fun x => abs_finiteGaussianDivergence_le_poly hC hC x (hFg x) (hDg x)
  obtain ⟨M, hM0, hM⟩ := exists_norm_fderiv_cutR_le (V := V)
  have hI1 : Integrable (fun x => φ x * finiteGaussianDivergence F x) (finiteStdGaussian V) :=
    integrable_of_le_poly (hφ.continuous.mul hδc).aestronglyMeasurable (Bφ * (C + d * C)) (k + 1)
      (fun x => by
        rw [norm_mul]
        calc ‖φ x‖ * ‖finiteGaussianDivergence F x‖ ≤ Bφ * ((C + d * C) * (1 + ‖x‖) ^ (k + 1)) :=
              mul_le_mul (hφb x) (by simpa using hδb x) (norm_nonneg _) hBφ
          _ = _ := by ring)
  have hI2 : Integrable (fun x => fderiv ℝ φ x (F x)) (finiteStdGaussian V) :=
    integrable_of_le_poly (hφ'c.clm_apply hFcont).aestronglyMeasurable (Bφ' * C) k
      (fun x => by
        calc ‖fderiv ℝ φ x (F x)‖ ≤ ‖fderiv ℝ φ x‖ * ‖F x‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ Bφ' * (C * (1 + ‖x‖) ^ k) := mul_le_mul (hφ'b x) (hFg x) (norm_nonneg _) hBφ'
          _ = _ := by ring)
  refine ⟨hI1, hI2, ?_⟩
  let Rn : ℕ → ℝ := fun n => (n : ℝ) + 1
  have hRn0 : ∀ n, 0 < Rn n := fun n => by positivity
  have hRn1 : ∀ n, 1 ≤ Rn n := fun n => by simp [Rn]
  let ψ : ℕ → V → ℝ := fun n y => cutR (Rn n) y * φ y
  have hψ1 : ∀ n, ContDiff ℝ 1 (ψ n) := fun n => (contDiff_cutR _ 1).mul hφ
  have hψc : ∀ n, HasCompactSupport (ψ n) := fun n =>
    (hasCompactSupport_cutR (hRn0 n)).mul_right
  have hev : ∀ x : V, ∃ N : ℕ, ∀ n ≥ N, ‖x‖ < Rn n := by
    intro x
    obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
    exact ⟨N, fun n hn => by
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      simp only [Rn]; linarith⟩
  have hψb : ∀ n x, ‖ψ n x‖ ≤ Bφ := fun n x => by
    show ‖cutR (Rn n) x * φ x‖ ≤ Bφ
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (cutR_nonneg _ _)]
    calc cutR (Rn n) x * ‖φ x‖ ≤ 1 * Bφ :=
          mul_le_mul (cutR_le_one _ _) (hφb x) (norm_nonneg _) zero_le_one
      _ = Bφ := one_mul _
  have hψ'b : ∀ n x, ‖fderiv ℝ (ψ n) x‖ ≤ Bφ' + Bφ * M := by
    intro n x
    show ‖fderiv ℝ (fun y => cutR (Rn n) y * φ y) x‖ ≤ _
    rw [fderiv_cutR_mul hφdiff]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (cutR_nonneg _ _)]
      calc cutR (Rn n) x * ‖fderiv ℝ φ x‖ ≤ 1 * Bφ' :=
            mul_le_mul (cutR_le_one _ _) (hφ'b x) (norm_nonneg _) zero_le_one
        _ = Bφ' := one_mul _
    · rw [norm_smul]
      exact mul_le_mul (hφb x) (hM _ (hRn1 n) x) (norm_nonneg _) hBφ
  have hL : Tendsto (fun n => ∫ x, ψ n x * finiteGaussianDivergence F x ∂(finiteStdGaussian V))
      atTop (𝓝 (∫ x, φ x * finiteGaussianDivergence F x ∂(finiteStdGaussian V))) := by
    refine tendsto_integral_of_poly_bound (fun n => ?_) (Bφ * (C + d * C)) (k + 1)
      (fun n x => ?_) (fun x => ?_)
    · exact ((hψ1 n).continuous.mul hδc).aestronglyMeasurable
    · rw [norm_mul]
      calc ‖ψ n x‖ * ‖finiteGaussianDivergence F x‖ ≤ Bφ * ((C + d * C) * (1 + ‖x‖) ^ (k + 1)) :=
            mul_le_mul (hψb n x) (by simpa using hδb x) (norm_nonneg _) hBφ
        _ = _ := by ring
    · obtain ⟨N, hN⟩ := hev x
      exact ⟨N, fun n hn => by
        show cutR (Rn n) x * φ x * _ = _
        rw [cutR_eq_one (hRn0 n) (hN n hn), one_mul]⟩
  have hR : Tendsto (fun n => ∫ x, fderiv ℝ (ψ n) x (F x) ∂(finiteStdGaussian V))
      atTop (𝓝 (∫ x, fderiv ℝ φ x (F x) ∂(finiteStdGaussian V))) := by
    refine tendsto_integral_of_poly_bound (fun n => ?_) ((Bφ' + Bφ * M) * C) k
      (fun n x => ?_) (fun x => ?_)
    · exact (((hψ1 n).continuous_fderiv (by norm_num)).clm_apply hFcont).aestronglyMeasurable
    · calc ‖fderiv ℝ (ψ n) x (F x)‖ ≤ ‖fderiv ℝ (ψ n) x‖ * ‖F x‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ (Bφ' + Bφ * M) * (C * (1 + ‖x‖) ^ k) :=
            mul_le_mul (hψ'b n x) (hFg x) (norm_nonneg _) (by positivity)
        _ = _ := by ring
    · obtain ⟨N, hN⟩ := hev x
      exact ⟨N, fun n hn => by
        rw [show fderiv ℝ (ψ n) x = fderiv ℝ φ x from
          (cutR_mul_eventuallyEq (hRn0 n) φ (hN n hn)).fderiv_eq]⟩
  have hEq : ∀ n, ∫ x, ψ n x * finiteGaussianDivergence F x ∂(finiteStdGaussian V) =
      ∫ x, fderiv ℝ (ψ n) x (F x) ∂(finiteStdGaussian V) := fun n =>
    integral_mul_finiteGaussianDivergence (ψ n) F (hψ1 n) (hψc n) hF
  simp_rw [hEq] at hL
  exact tendsto_nhds_unique hL hR

end NlsGge.Ramer
