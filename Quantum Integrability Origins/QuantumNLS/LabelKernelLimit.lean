import QuantumNLS.LabelJointStructure

/-!
# PROP-002 `lem:B3-weak-joint-limit`, part (3): the kernel limit and the limiting weak identity

Source: `source/chapters/propagation/label_periods.tex:68-102`. For `f ∈ C_c^1(ℝ)` the finite identity
`eq:B3-weak-bethe-identity` (the auxiliary construction's `bethe_pairing_identity`, LabelJointLimit `4120590e…`) passes to
the limit: "These kernels are bounded by `‖f'‖∞`. Off any fixed diagonal strip they converge uniformly
to the bounded continuous divided difference `(f(t)−f(u))/(t−u)`, with value `f'(t)` on the
diagonal. The limiting product measure assigns vanishing mass to shrinking diagonal strips, because
`μ` is nonatomic. ... The first term on the right has compact support in `t`; the left term is
uniformly bounded on that same support by `QG:eq:B3-uniform-label-distance`." Result
`eq:B3-limit-weak-identity`:
`∫ n(t) f(t) dμ = (L/2π) ∫ t f(t) dμ − (κ/2π) ∬ (f(t)−f(u))/(t−u) dμ(t) dμ(u)`.

Imports JS1 `LabelJointStructure` (`eb12b8a8…`, own, frozen).

* `dd f t u` — the printed divided difference (`f'(t)` on the diagonal); `dq_eq_dd`,
  `continuous_dd` (integral representation `∫₀¹ f'(u + s(t−u)) ds`); `abs_arctan_le`,
  `abs_arctan_sub_le` (`|arctan y − y| ≤ |y|³`);
* `kernel_abs_le` (`|K_N| ≤ ‖f'‖∞`), `dd_abs_le`, `kernel_sub_dd_le` (off the strip
  `|t−u| ≥ δ`: `|K_N − dd| ≤ 2‖f‖∞ κ²/(N²δ³)`);
* `integral_emp_prod` (product empirical integrals are double averages), `prod_diagonal_null`,
  `tendsto_strip` (strips shrink to the null diagonal);
* **`kernel_limit`**: `(1/N²) Σ_{j,ℓ} K_N(q_j, q_ℓ) → ∬ dd f dμ dμ` along any subsequence with
  `N → ∞`;
* **`limit_identity`**: `eq:B3-limit-weak-identity` for `g` from JS1's `limit_graph`.
The source's sequence is indexed by the particle number `N → ∞`; here a general sequence `N k` with
`N k → ∞` is used (`hNtop`), which contains that case.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace QuantumNLS.LabelKernelLimit

open QuantumNLS.LabelJointLimit QuantumNLS.LabelTightness QuantumNLS.LabelJointWeak
  QuantumNLS.LabelJointStructure

/-! ## 1. Elementary analysis -/

/-- The printed divided difference, with value `f'(t)` on the diagonal. -/
def dd (f : ℝ → ℝ) (t u : ℝ) : ℝ := if t = u then deriv f t else (f t - f u) / (t - u)

/-- Integral representation of the divided difference. -/
def dq (f : ℝ → ℝ) (t u : ℝ) : ℝ := ∫ s in (0 : ℝ)..1, deriv f (u + s * (t - u))

lemma dq_eq_dd {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (t u : ℝ) : dq f t u = dd f t u := by
  unfold dq dd
  by_cases h : t = u
  · subst h; simp
  · simp only [h, ↓reduceIte]
    have hc : t - u ≠ 0 := sub_ne_zero.2 h
    have e : (fun s => deriv f (u + s * (t - u))) = fun s => deriv f ((t - u) * s + u) := by
      funext s; ring_nf
    rw [e, intervalIntegral.integral_comp_mul_add (fun x => deriv f x) hc u]
    simp only [mul_zero, zero_add, mul_one, sub_add_cancel]
    rw [intervalIntegral.integral_deriv_eq_sub (fun x _ => (hf.differentiable one_ne_zero) x)
      ((hf.continuous_deriv le_rfl).intervalIntegrable _ _), smul_eq_mul]
    field_simp

/-- The divided difference of a `C¹` function is continuous on `ℝ × ℝ`. -/
lemma continuous_dd {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) :
    Continuous fun p : ℝ × ℝ => dd f p.1 p.2 := by
  have h : Continuous fun p : ℝ × ℝ => dq f p.1 p.2 := by
    unfold dq
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (p : ℝ × ℝ) (s : ℝ) => deriv f (p.2 + s * (p.1 - p.2))) ?_ 0 1
    have := hf.continuous_deriv le_rfl
    fun_prop
  exact h.congr fun p => dq_eq_dd hf p.1 p.2

lemma abs_arctan_le (y : ℝ) : |Real.arctan y| ≤ |y| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := Real.arctan) (s := uIcc 0 y)
    (C := 1) (fun x _ => Real.differentiableAt_arctan x) (fun x _ => by
      rw [Real.deriv_arctan, Real.norm_eq_abs, abs_of_pos (by positivity)]
      rw [div_le_one (by positivity)]; nlinarith [sq_nonneg x]) (convex_uIcc 0 y)
    left_mem_uIcc right_mem_uIcc
  simpa using h

lemma deriv_arctan_sub (x : ℝ) : deriv (fun y => Real.arctan y - y) x = 1 / (1 + x ^ 2) - 1 :=
  ((Real.hasDerivAt_arctan x).sub (hasDerivAt_id x)).deriv

/-- `|arctan y − y| ≤ |y|³`. -/
lemma abs_arctan_sub_le (y : ℝ) : |Real.arctan y - y| ≤ |y| ^ 3 := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := fun y => Real.arctan y - y)
    (s := uIcc 0 y) (C := y ^ 2)
    (fun x _ => (Real.differentiableAt_arctan x).sub differentiableAt_id) (fun x hx => by
      rw [deriv_arctan_sub, Real.norm_eq_abs]
      have hx' : |x| ≤ |y| := by
        rcases le_total 0 y with h | h
        · rw [uIcc_of_le h] at hx; rw [abs_of_nonneg hx.1, abs_of_nonneg h]; exact hx.2
        · rw [uIcc_of_ge h] at hx; rw [abs_of_nonpos hx.2, abs_of_nonpos h]; linarith [hx.1]
      have hx2 : x ^ 2 ≤ y ^ 2 := by
        rw [← sq_abs x, ← sq_abs y]; exact pow_le_pow_left₀ (abs_nonneg _) hx' 2
      have e : 1 / (1 + x ^ 2) - 1 = -(x ^ 2 / (1 + x ^ 2)) := by field_simp; ring
      rw [e, abs_neg, abs_of_nonneg (by positivity)]
      calc x ^ 2 / (1 + x ^ 2) ≤ x ^ 2 := div_le_self (sq_nonneg x) (by nlinarith [sq_nonneg x])
        _ ≤ y ^ 2 := hx2) (convex_uIcc 0 y) left_mem_uIcc right_mem_uIcc
  simp only [Real.arctan_zero, sub_zero, Real.norm_eq_abs] at h
  calc |Real.arctan y - y| ≤ y ^ 2 * |y| := h
    _ = |y| ^ 3 := by rw [← sq_abs y]; ring

/-! ## 2. Kernel bounds -/

/-- `|K_N(t,u)| ≤ C₁` when `f` is `C₁`-Lipschitz. -/
lemma kernel_abs_le {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) {f : ℝ → ℝ} {C1 : ℝ}
    (hlip : ∀ t u, |f t - f u| ≤ C1 * |t - u|) (t u : ℝ) : |pairKernel κ N f t u| ≤ C1 := by
  have hC1 : 0 ≤ C1 := by
    have := hlip 1 0; norm_num at this; linarith [abs_nonneg (f 1 - f 0)]
  unfold pairKernel
  by_cases h : t = u
  · simp [h, hC1]
  · simp only [h, ↓reduceIte]
    have hx : t - u ≠ 0 := sub_ne_zero.2 h
    have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
    rw [abs_mul, abs_mul, abs_of_pos (div_pos hNr hκ)]
    have h1 := abs_arctan_le (κ / ((N : ℝ) * (t - u)))
    rw [abs_div, abs_mul, abs_of_pos hκ, abs_of_pos hNr] at h1
    have hpos : 0 < |t - u| := abs_pos.2 hx
    calc (N : ℝ) / κ * |f t - f u| * |Real.arctan (κ / ((N : ℝ) * (t - u)))|
        ≤ (N : ℝ) / κ * (C1 * |t - u|) * (κ / ((N : ℝ) * |t - u|)) := by gcongr; exact hlip t u
      _ = C1 := by field_simp

lemma dd_abs_le {f : ℝ → ℝ} {C1 : ℝ} (hd : ∀ x, |deriv f x| ≤ C1)
    (hlip : ∀ t u, |f t - f u| ≤ C1 * |t - u|) (t u : ℝ) : |dd f t u| ≤ C1 := by
  unfold dd
  by_cases h : t = u
  · simp only [h, ↓reduceIte]; exact hd u
  · simp only [h, ↓reduceIte]
    rw [abs_div, div_le_iff₀ (abs_pos.2 (sub_ne_zero.2 h))]
    exact hlip t u

/-- Off the diagonal strip `|t − u| ≥ δ`: `|K_N − dd| ≤ 2 C₀ κ² / (N² δ³)`. -/
lemma kernel_sub_dd_le {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) {f : ℝ → ℝ} {C0 : ℝ}
    (hC0 : ∀ x, |f x| ≤ C0) {δ t u : ℝ} (hδ : 0 < δ) (htu : δ ≤ |t - u|) :
    |pairKernel κ N f t u - dd f t u| ≤ 2 * C0 * κ ^ 2 / ((N : ℝ) ^ 2 * δ ^ 3) := by
  have hne : t ≠ u := by intro h; rw [h, sub_self, abs_zero] at htu; linarith
  have hx : t - u ≠ 0 := sub_ne_zero.2 hne
  have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hC0' : 0 ≤ C0 := (abs_nonneg _).trans (hC0 0)
  set y := κ / ((N : ℝ) * (t - u)) with hydef
  have e : pairKernel κ N f t u - dd f t u =
      (f t - f u) * ((N : ℝ) / κ) * (Real.arctan y - y) := by
    simp only [pairKernel, dd, hne, ↓reduceIte]
    rw [hydef]
    field_simp
  rw [e, abs_mul, abs_mul, abs_of_pos (div_pos hNr hκ)]
  have h1 : |f t - f u| ≤ 2 * C0 := (abs_sub _ _).trans (by linarith [hC0 t, hC0 u])
  have h2 := abs_arctan_sub_le y
  have hpos : 0 < |t - u| := abs_pos.2 hx
  have hy : |y| ^ 3 = κ ^ 3 / ((N : ℝ) ^ 3 * |t - u| ^ 3) := by
    rw [hydef, abs_div, abs_mul, abs_of_pos hκ, abs_of_pos hNr, div_pow, mul_pow]
  calc |f t - f u| * ((N : ℝ) / κ) * |Real.arctan y - y|
      ≤ 2 * C0 * ((N : ℝ) / κ) * (κ ^ 3 / ((N : ℝ) ^ 3 * |t - u| ^ 3)) := by
        rw [← hy]; gcongr
    _ = 2 * C0 * κ ^ 2 / ((N : ℝ) ^ 2 * |t - u| ^ 3) := by field_simp
    _ ≤ 2 * C0 * κ ^ 2 / ((N : ℝ) ^ 2 * δ ^ 3) := by gcongr

lemma measurable_kernel (κ : ℝ) (N : ℕ) {f : ℝ → ℝ} (hf : Continuous f) :
    Measurable fun p : ℝ × ℝ => pairKernel κ N f p.1 p.2 := by
  unfold pairKernel
  refine Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd) measurable_const ?_
  have := hf.measurable
  fun_prop

/-! ## 3. Product empirical measures and strips -/

/-- Integrals against `L_N ⊗ L_N` are double averages. -/
lemma integral_emp_prod {N : ℕ} (p : Fin N → ℝ) {F : ℝ × ℝ → ℝ} (hF : Measurable F) {C : ℝ}
    (hC : ∀ x, |F x| ≤ C) :
    ∫ x, F x ∂((emp p).prod (emp p)) = (N : ℝ)⁻¹ * ∑ j, ((N : ℝ)⁻¹ * ∑ l, F (p j, p l)) := by
  rw [integral_prod F (Integrable.of_bound hF.aestronglyMeasurable C
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hC x))]
  simp only [integral_emp]

/-- The diagonal is null for the product of a nonatomic measure. -/
lemma prod_diagonal_null (μ : Measure ℝ) [SFinite μ] [NullSingletonClass μ] :
    (μ.prod μ) (diagonal ℝ) = 0 := by
  rw [Measure.prod_apply measurableSet_diagonal]
  have : ∀ x : ℝ, Prod.mk x ⁻¹' diagonal ℝ = {x} := fun x => by ext y; simp [eq_comm]
  simp only [this, measure_singleton, lintegral_zero]

/-- The closed diagonal strip `|t − u| ≤ δ`. -/
def strip (δ : ℝ) : Set (ℝ × ℝ) := {p | |p.1 - p.2| ≤ δ}

lemma isClosed_strip (δ : ℝ) : IsClosed (strip δ) :=
  isClosed_le (by fun_prop) continuous_const

/-- Shrinking strips have vanishing product mass. -/
lemma tendsto_strip (μ : Measure ℝ) [IsFiniteMeasure μ] [NullSingletonClass μ] :
    Tendsto (fun m : ℕ => (μ.prod μ) (strip (1 / ((m : ℝ) + 1)))) atTop (𝓝 0) := by
  have hanti : Antitone fun m : ℕ => strip (1 / ((m : ℝ) + 1)) := by
    intro m n hmn p hp
    show |p.1 - p.2| ≤ 1 / ((m : ℝ) + 1)
    exact le_trans hp (by gcongr)
  have hI : (⋂ m : ℕ, strip (1 / ((m : ℝ) + 1))) = diagonal ℝ := by
    ext p
    simp only [mem_iInter, strip, Set.mem_ofPred_eq, mem_diagonal_iff]
    constructor
    · intro h
      have : p.1 - p.2 = 0 := by
        by_contra hx
        obtain ⟨m, hm⟩ := exists_nat_one_div_lt (abs_pos.2 hx)
        linarith [h m]
      linarith
    · intro h m
      rw [h, sub_self, abs_zero]
      positivity
  have := tendsto_measure_iInter_atTop (μ := μ.prod μ)
    (fun m => (isClosed_strip _).measurableSet.nullMeasurableSet) hanti
    ⟨0, measure_ne_top _ _⟩
  rw [hI, prod_diagonal_null] at this
  exact this

/-! ## 4. The kernel limit -/

section Seq

variable {L κ : ℝ} {N : ℕ → ℕ} {hN : ∀ k, 0 < N k} {B : ∀ k, OnShellBethe L κ (N k)}
  {μ : ProbabilityMeasure ℝ}

/-- Bounds for a `C¹_c` function: `|f| ≤ C₀`, `|f'| ≤ C₁`, `f` is `C₁`-Lipschitz, `C₁ > 0`. -/
lemma c1c_bounds {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hcs : HasCompactSupport f) :
    ∃ C0 C1 : ℝ, 0 < C1 ∧ (∀ x, |f x| ≤ C0) ∧ (∀ x, |deriv f x| ≤ C1) ∧
      ∀ t u, |f t - f u| ≤ C1 * |t - u| := by
  obtain ⟨C0, hC0⟩ := hf.continuous.bounded_above_of_compact_support hcs
  obtain ⟨C1, hC1⟩ := (hf.continuous_deriv le_rfl).bounded_above_of_compact_support hcs.deriv
  set C1' := max C1 0 + 1
  have hd : ∀ x, |deriv f x| ≤ C1' := fun x =>
    ((Real.norm_eq_abs _).symm.le.trans (hC1 x)).trans ((le_max_left _ _).trans (by linarith))
  have hC1'0 : 0 ≤ C1' := by positivity
  have hlipW : LipschitzWith (Real.toNNReal C1') f := lipschitzWith_of_nnnorm_deriv_le
    (hf.differentiable one_ne_zero) fun x => by
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hC1'0, Real.norm_eq_abs]; exact hd x
  refine ⟨C0, C1', by positivity, fun x => (Real.norm_eq_abs _).symm.le.trans (hC0 x), hd,
    fun t u => ?_⟩
  have := hlipW.dist_le_mul t u
  simpa [Real.dist_eq, Real.coe_toNNReal _ hC1'0] using this

/-- **The kernel limit**: along a subsequence of a sequence with `L_N ⇀ μ`, `μ` nonatomic and
`N → ∞`, `(1/N²) Σ_{j,ℓ} K_N(q_j, q_ℓ) → ∬ dd f dμ dμ` for `f ∈ C_c^1`. -/
theorem kernel_limit (hκ : 0 < κ) [NullSingletonClass (μ : Measure ℝ)]
    (hconv : Tendsto (fun k => rootP (B k) (hN k)) atTop (𝓝 μ))
    (hNtop : Tendsto N atTop atTop) {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hcs : HasCompactSupport f) :
    Tendsto (fun k => (1 / (N (φ k) : ℝ) ^ 2) *
        ∑ j, ∑ l, pairKernel κ (N (φ k)) f ((B (φ k)).q j) ((B (φ k)).q l)) atTop
      (𝓝 (∫ p, dd f p.1 p.2 ∂((μ : Measure ℝ).prod (μ : Measure ℝ)))) := by
  obtain ⟨C0, C1, hC1, hC0, hd, hlip⟩ := c1c_bounds hf hcs
  set P : ℕ → ProbabilityMeasure ℝ := fun k => rootP (B (φ k)) (hN (φ k))
  have hP : Tendsto P atTop (𝓝 μ) := hconv.comp hφ
  have hQ : Tendsto (fun k => (P k).prod (P k)) atTop (𝓝 (μ.prod μ)) :=
    (ProbabilityMeasure.continuous_prod.tendsto (μ, μ)).comp (hP.prodMk_nhds hP)
  have hQm : ∀ k, (((P k).prod (P k) : ProbabilityMeasure (ℝ × ℝ)) : Measure (ℝ × ℝ)) =
      (emp (B (φ k)).q).prod (emp (B (φ k)).q) := fun k => by
    rw [ProbabilityMeasure.toMeasure_prod]; rfl
  have hμm : ((μ.prod μ : ProbabilityMeasure (ℝ × ℝ)) : Measure (ℝ × ℝ)) =
      (μ : Measure ℝ).prod (μ : Measure ℝ) := ProbabilityMeasure.toMeasure_prod _ _
  -- the bounded continuous divided difference
  have hddc := continuous_dd hf
  set D : BoundedContinuousFunction (ℝ × ℝ) ℝ :=
    BoundedContinuousFunction.mkOfBound ⟨fun p => dd f p.1 p.2, hddc⟩ (2 * C1) (fun x y => by
      show |dd f x.1 x.2 - dd f y.1 y.2| ≤ 2 * C1
      exact (abs_sub _ _).trans (by
        linarith [dd_abs_le hd hlip x.1 x.2, dd_abs_le hd hlip y.1 y.2]))
  have hD := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hQ) D
  rw [hμm] at hD
  simp only [hQm] at hD
  -- `s k` and `d k`
  have hKm : ∀ k, Measurable fun p : ℝ × ℝ => pairKernel κ (N (φ k)) f p.1 p.2 :=
    fun k => measurable_kernel κ _ hf.continuous
  have hs : ∀ k, (1 / (N (φ k) : ℝ) ^ 2) *
      ∑ j, ∑ l, pairKernel κ (N (φ k)) f ((B (φ k)).q j) ((B (φ k)).q l) =
      ∫ p, pairKernel κ (N (φ k)) f p.1 p.2 ∂((emp (B (φ k)).q).prod (emp (B (φ k)).q)) := by
    intro k
    rw [integral_emp_prod _ (hKm k) (fun x => kernel_abs_le hκ (hN (φ k)) hlip x.1 x.2)]
    simp only [← Finset.mul_sum]
    ring
  simp only [hs]
  -- reduce to the difference
  have hdiff : Tendsto (fun k =>
      ∫ p, pairKernel κ (N (φ k)) f p.1 p.2 ∂((emp (B (φ k)).q).prod (emp (B (φ k)).q)) -
      ∫ p, D p ∂((emp (B (φ k)).q).prod (emp (B (φ k)).q))) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    -- choose the strip
    have hstrip := tendsto_strip (μ : Measure ℝ)
    have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / (8 * C1)) :=
      ENNReal.ofReal_pos.2 (by positivity)
    obtain ⟨m, hm⟩ := (hstrip.eventually (gt_mem_nhds hpos)).exists
    set δ : ℝ := 1 / ((m : ℝ) + 1)
    have hδ : 0 < δ := by positivity
    -- eventually small strip mass for `Q k`
    have hlimsup := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hQ (isClosed_strip δ)
    rw [hμm] at hlimsup
    have hev1 : ∀ᶠ k in atTop, (((P k).prod (P k) : ProbabilityMeasure (ℝ × ℝ)) :
        Measure (ℝ × ℝ)) (strip δ) < ENNReal.ofReal (ε / (8 * C1)) :=
      eventually_lt_of_limsup_lt (hlimsup.trans_lt hm)
    -- eventually small off-strip error
    have hη : Tendsto (fun k => 2 * C0 * κ ^ 2 / ((N (φ k) : ℝ) ^ 2 * δ ^ 3)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun k => ((N (φ k) : ℝ) ^ 2 * δ ^ 3)) atTop atTop :=
        Tendsto.atTop_mul_const (by positivity)
          ((tendsto_pow_atTop two_ne_zero).comp
            (tendsto_natCast_atTop_atTop.comp (hNtop.comp hφ)))
      exact h1.const_div_atTop _
    have hev2 : ∀ᶠ k in atTop, 2 * C0 * κ ^ 2 / ((N (φ k) : ℝ) ^ 2 * δ ^ 3) < ε / 4 :=
      hη.eventually (gt_mem_nhds (by positivity))
    obtain ⟨K, hK⟩ := eventually_atTop.1 (hev1.and hev2)
    refine ⟨K, fun k hk => ?_⟩
    obtain ⟨h1, h2⟩ := hK k hk
    rw [hQm] at h1
    set Qk := (emp (B (φ k)).q).prod (emp (B (φ k)).q)
    set η := 2 * C0 * κ ^ 2 / ((N (φ k) : ℝ) ^ 2 * δ ^ 3)
    have hη0 : 0 ≤ η := by
      have : 0 ≤ C0 := (abs_nonneg _).trans (hC0 0)
      positivity
    have hKint : Integrable (fun p : ℝ × ℝ => pairKernel κ (N (φ k)) f p.1 p.2) Qk :=
      Integrable.of_bound (hKm k).aestronglyMeasurable C1
        (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact kernel_abs_le hκ (hN (φ k)) hlip _ _)
    have hDint : Integrable (fun p => D p) Qk := D.integrable Qk
    set bnd : ℝ × ℝ → ℝ := fun p => (strip δ).indicator (fun _ => 2 * C1) p + η with hbnd
    have hI1 : Integrable (fun p => (strip δ).indicator (fun _ => 2 * C1) p) Qk :=
      (integrable_const (2 * C1)).indicator (isClosed_strip δ).measurableSet
    have hSint : Integrable bnd Qk := hI1.add (integrable_const η)
    have hbound : ∀ p : ℝ × ℝ, ‖pairKernel κ (N (φ k)) f p.1 p.2 - D p‖ ≤ bnd p := by
      intro p
      simp only [Real.norm_eq_abs, hbnd]
      have hDp : D p = dd f p.1 p.2 := rfl
      rw [hDp]
      by_cases hp : p ∈ strip δ
      · rw [indicator_of_mem hp]
        have := kernel_abs_le hκ (hN (φ k)) hlip p.1 p.2
        have := dd_abs_le hd hlip p.1 p.2
        have := abs_sub (pairKernel κ (N (φ k)) f p.1 p.2) (dd f p.1 p.2)
        linarith
      · rw [indicator_of_notMem hp, zero_add]
        simp only [strip, Set.mem_ofPred_eq, not_le] at hp
        exact kernel_sub_dd_le hκ (hN (φ k)) hC0 hδ hp.le
    have hQ1 : Qk.real univ = 1 := by
      have : Qk = (((P k).prod (P k) : ProbabilityMeasure (ℝ × ℝ)) : Measure (ℝ × ℝ)) :=
        (hQm k).symm
      rw [this]; exact probReal_univ
    have hle := norm_integral_le_of_norm_le hSint (ae_of_all _ hbound)
    rw [Real.dist_eq, sub_zero, ← integral_sub hKint hDint, ← Real.norm_eq_abs]
    refine (hle).trans_lt ?_
    rw [hbnd, integral_add hI1 (integrable_const η), integral_indicator (isClosed_strip δ).measurableSet,
      setIntegral_const, integral_const, hQ1, one_smul, smul_eq_mul]
    have hQS : Qk.real (strip δ) < ε / (8 * C1) := by
      rw [measureReal_def]
      exact (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).2 h1 |>.trans_le
        (ENNReal.toReal_ofReal (by positivity)).le
    have : Qk.real (strip δ) * (2 * C1) < ε / 4 := by
      calc Qk.real (strip δ) * (2 * C1) < ε / (8 * C1) * (2 * C1) := by gcongr
        _ = ε / 4 := by field_simp; ring
    linarith
  have := hdiff.add hD
  simp only [sub_add_cancel, zero_add] at this
  exact this

/-- **`eq:B3-limit-weak-identity`**: for a subsequential joint limit `γ = μ(dt) δ_{g(t)}` (JS1
`limit_graph`) and `f ∈ C_c^1`,
`∫ g f dμ = (L/2π) ∫ t f(t) dμ − (κ/2π) ∬ dd f dμ dμ`. -/
theorem limit_identity (hL : 0 < L) (hκ : 0 < κ) [NullSingletonClass (μ : Measure ℝ)]
    (hconv : Tendsto (fun k => rootP (B k) (hN k)) atTop (𝓝 μ))
    (hNtop : Tendsto N atTop atTop) {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop)
    {γ : ProbabilityMeasure (ℝ × ℤ)}
    (hγ : Tendsto (fun k => jointP (B (φ k)) (hN (φ k))) atTop (𝓝 γ))
    {g : ℝ → ℤ} (hg : Measurable g)
    (heq : (γ : Measure (ℝ × ℤ)) = (μ : Measure ℝ).map (fun t => (t, g t)))
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hcs : HasCompactSupport f) :
    ∫ t, (g t : ℝ) * f t ∂(μ : Measure ℝ) =
      (L / (2 * Real.pi)) * ∫ t, t * f t ∂(μ : Measure ℝ) -
        (κ / (2 * Real.pi)) * ∫ p, dd f p.1 p.2 ∂((μ : Measure ℝ).prod (μ : Measure ℝ)) := by
  obtain ⟨C0, C1, hC1, hC0, hd, hlip⟩ := c1c_bounds hf hcs
  have hC00 : 0 ≤ C0 := (abs_nonneg _).trans (hC0 0)
  obtain ⟨R, hR⟩ : ∃ R, ∀ t, f t ≠ 0 → |t| ≤ R := by
    obtain ⟨R, hR⟩ := hcs.isCompact.isBounded.subset_closedBall 0
    exact ⟨R, fun t ht => by
      have := hR (subset_tsupport f ht)
      rwa [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this⟩
  set C : ℝ := (L / (2 * Real.pi)) * (|R| + 3 * Real.sqrt (κ / L)) with hCdef
  have hC : 0 ≤ C := by positivity
  set cl : ℝ → ℝ := fun x => max (-C) (min C x) with hcldef
  have hcl : ∀ x, |x| ≤ C → cl x = x := fun x hx => by
    simp only [hcldef]
    rw [min_eq_right ((le_abs_self x).trans hx), max_eq_right (by linarith [neg_abs_le x])]
  have hclb : ∀ x, |cl x| ≤ C := fun x =>
    abs_le.2 ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have hbound : ∀ t, |t| ≤ R → (L / (2 * Real.pi)) * (|t| + 3 * Real.sqrt (κ / L)) ≤ C :=
    fun t ht => by
      rw [hCdef]
      have h1 := ht.trans (le_abs_self R)
      have h2 : (0 : ℝ) ≤ L / (2 * Real.pi) := by positivity
      exact mul_le_mul_of_nonneg_left (by linarith) h2
  -- bounded continuous test functions
  have hzc : Continuous fun z : ℤ => (z : ℝ) := continuous_of_discreteTopology
  have hFc : Continuous fun p : ℝ × ℤ => cl (p.2 : ℝ) * f p.1 :=
    (continuous_const.max (continuous_const.min (hzc.comp continuous_snd))).mul
      (hf.continuous.comp continuous_fst)
  have hFb : ∀ p : ℝ × ℤ, |cl (p.2 : ℝ) * f p.1| ≤ C * C0 := fun p => by
    rw [abs_mul]; exact mul_le_mul (hclb _) (hC0 _) (abs_nonneg _) hC
  set F : BoundedContinuousFunction (ℝ × ℤ) ℝ :=
    BoundedContinuousFunction.mkOfBound ⟨fun p => cl (p.2 : ℝ) * f p.1, hFc⟩ (2 * (C * C0))
      (fun x y => by
        show |cl (x.2 : ℝ) * f x.1 - cl (y.2 : ℝ) * f y.1| ≤ 2 * (C * C0)
        exact (abs_sub _ _).trans (by linarith [hFb x, hFb y]))
  have hGb : ∀ t : ℝ, |t * f t| ≤ |R| * C0 := fun t => by
    by_cases h0 : f t = 0
    · rw [h0, mul_zero, abs_zero]; positivity
    · rw [abs_mul]
      exact mul_le_mul ((hR t h0).trans (le_abs_self R)) (hC0 t) (abs_nonneg _) (abs_nonneg _)
  set G : BoundedContinuousFunction ℝ ℝ :=
    BoundedContinuousFunction.mkOfBound ⟨fun t => t * f t, continuous_id.mul hf.continuous⟩
      (2 * (|R| * C0)) (fun x y => by
        show |x * f x - y * f y| ≤ 2 * (|R| * C0)
        exact (abs_sub _ _).trans (by linarith [hGb x, hGb y]))
  -- finite identities as integrals
  have hleft : ∀ k, (1 / (N (φ k) : ℝ)) * ∑ j, ((B (φ k)).n j : ℝ) * f ((B (φ k)).q j) =
      ∫ p, F p ∂(jointP (B (φ k)) (hN (φ k)) : Measure (ℝ × ℤ)) := by
    intro k
    show _ = ∫ p, F p ∂(emp (pts (B (φ k))))
    rw [integral_emp, one_div]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    show _ = cl ((B (φ k)).n j : ℝ) * f ((B (φ k)).q j)
    by_cases h0 : f ((B (φ k)).q j) = 0
    · rw [h0]; simp
    · rw [hcl]
      exact (label_abs_le_bound hL hκ (hN (φ k)) (B (φ k)) j).trans (hbound _ (hR _ h0))
  have hmid : ∀ k, (1 / (N (φ k) : ℝ)) * ∑ j, (B (φ k)).q j * f ((B (φ k)).q j) =
      ∫ t, G t ∂(rootP (B (φ k)) (hN (φ k)) : Measure ℝ) := by
    intro k
    show _ = ∫ t, G t ∂(emp (B (φ k)).q)
    rw [integral_emp, one_div]
    rfl
  -- the limits
  have hG' : Measurable fun t => (t, g t) := measurable_id.prodMk hg
  have hFγ : ∫ p, F p ∂(γ : Measure (ℝ × ℤ)) = ∫ t, (g t : ℝ) * f t ∂(μ : Measure ℝ) := by
    rw [heq, integral_map hG'.aemeasurable F.continuous.aestronglyMeasurable]
    refine integral_congr_ae ((limit_label_bound hL hκ hγ hg heq).mono fun t ht => ?_)
    show cl (g t : ℝ) * f t = (g t : ℝ) * f t
    by_cases h0 : f t = 0
    · simp [h0]
    · rw [hcl]
      exact ht.trans (hbound t (hR t h0))
  have hlim1 : Tendsto (fun k => (1 / (N (φ k) : ℝ)) *
      ∑ j, ((B (φ k)).n j : ℝ) * f ((B (φ k)).q j)) atTop
      (𝓝 (∫ t, (g t : ℝ) * f t ∂(μ : Measure ℝ))) := by
    have := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hγ) F
    rw [hFγ] at this
    exact this.congr fun k => (hleft k).symm
  have hlim2 : Tendsto (fun k => (1 / (N (φ k) : ℝ)) *
      ∑ j, (B (φ k)).q j * f ((B (φ k)).q j)) atTop
      (𝓝 (∫ t, t * f t ∂(μ : Measure ℝ))) := by
    have := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 (hconv.comp hφ)) G
    exact this.congr fun k => (hmid k).symm
  have hlim3 := kernel_limit hκ hconv hNtop hφ hf hcs
  have hrhs := ((hlim2.const_mul (L / (2 * Real.pi))).sub (hlim3.const_mul (κ / (2 * Real.pi))))
  refine tendsto_nhds_unique hlim1 (hrhs.congr fun k => ?_)
  exact (bethe_pairing_identity hκ.ne' (hN (φ k)) (B (φ k)) f).symm

end Seq

#print axioms limit_identity
#print axioms dq_eq_dd
#print axioms continuous_dd
#print axioms abs_arctan_sub_le
#print axioms kernel_sub_dd_le
#print axioms tendsto_strip
#print axioms kernel_limit

end QuantumNLS.LabelKernelLimit
