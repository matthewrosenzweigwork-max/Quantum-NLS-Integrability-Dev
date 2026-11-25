import QuantumNLS.LabelKernelLimit
import QuantumNLS.IndexedScalarMeasureCuts

/-!
# PROP-002 `lem:B3-weak-joint-limit`, part (4): identification of the label function

Source: `source/chapters/propagation/label_periods.tex:104-117`. "The last identification uses only
the stated boundary-value hypothesis. Symmetrization gives
`∫ f(t) Re G_μ(t+iε) dμ(t) = ½ ∬ (f(t)−f(u)) (t−u)/((t−u)²+ε²) dμ(t)dμ(u)`. The right integrand is
bounded by `‖f'‖∞`. The boundary-value hypothesis gives a common local bound on the support of `f`
and pointwise convergence there. Dominated convergence as `ε ↓ 0` and `eq:B3-limit-weak-identity`
therefore identify `n(t) = Lt/(2π) − (κ/π) Re G_μ(t+i0)` for `μ`-almost every `t`."

Imports KL1 `LabelKernelLimit` (`62d37261…`, own, frozen) and DEF-043 `IndexedScalarMeasureCuts`
(`641aaaf7…`, read-only; through it `IndexedScalarMeasure` `bf40a2dd…`, whose `reCauchy`,
`LocallyUniformBoundary`, `BoundedAEBoundary`, `indexLabel` are used verbatim, and DEF-010
`EmpiricalRapidity.cauchyTransform`).

* `kε ε x = x/(x²+ε²)`; `reCauchy_eq` (`Re G_μ(t+iε) = ∫ kε(t−u) dμ(u)`), `abs_reCauchy_le`,
  `continuous_reCauchy`;
* **`symmetrization`** (`eq:B3-continuum-symmetrization`);
* `tendsto_symm` (dominated convergence of the right side to `∬ dd f`), `tendsto_lhs` (left side,
  bounded-a.e. alternative), `boundedAE_of_locallyUniform` (the locally uniform alternative implies the
  bounded-a.e. one), `aestronglyMeasurable_boundary`, `ae_bound_boundary`;
* **`integral_reG`**: `∫ f reG dμ = ½ ∬ dd f dμ dμ` for `f ∈ C_c^1`;
* **`ae_eq_indexLabel`**: a measurable integer label function satisfying the label bound and
  `eq:B3-limit-weak-identity` equals `indexLabel L κ reG` `μ`-a.e.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace QuantumNLS.LabelIdentification

open QuantumNLS.LabelKernelLimit QuantumNLS.IndexedScalarMeasure QuantumNLS.EmpiricalRapidity

/-! ## 1. The real part of the Cauchy kernel -/

/-- `Re ((x + iε)⁻¹) = x/(x²+ε²)`. -/
def kε (ε x : ℝ) : ℝ := x / (x ^ 2 + ε ^ 2)

lemma kε_neg (ε x : ℝ) : kε ε (-x) = -kε ε x := by
  unfold kε; rw [neg_sq, neg_div]

lemma abs_kε_le {ε : ℝ} (hε : 0 < ε) (x : ℝ) : |kε ε x| ≤ 1 / ε := by
  unfold kε
  rw [abs_div, abs_of_pos (by positivity : 0 < x ^ 2 + ε ^ 2), div_le_div_iff₀ (by positivity) hε]
  nlinarith [sq_nonneg (|x| - ε), sq_abs x, abs_nonneg x]

lemma measurable_kε : Measurable fun p : ℝ × ℝ => kε p.1 p.2 := by
  unfold kε; fun_prop

lemma continuous_kε {ε : ℝ} (hε : 0 < ε) : Continuous (kε ε) :=
  continuous_id.div (by fun_prop) (fun x => by positivity)

lemma inv_re_eq (ε x : ℝ) : (((x : ℂ) + (ε : ℂ) * Complex.I)⁻¹).re = kε ε x := by
  rw [Complex.inv_re, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.add_im, Complex.mul_im,
    zero_add, kε]
  ring_nf

/-- `Re G_μ(t + iε) = ∫ (t−u)/((t−u)²+ε²) dμ(u)` for `ε > 0`. -/
lemma reCauchy_eq (μ : Measure ℝ) [IsFiniteMeasure μ] {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    reCauchy μ t ε = ∫ u, kε ε (t - u) ∂μ := by
  unfold reCauchy cauchyTransform
  have hint : Integrable (fun u : ℝ => (((t : ℂ) + (ε : ℂ) * Complex.I) - (u : ℂ))⁻¹) μ := by
    refine Integrable.of_bound
      ((measurable_const.sub Complex.measurable_ofReal).inv.aestronglyMeasurable) (1 / ε)
      (ae_of_all _ fun u => ?_)
    have him : (((t : ℂ) + (ε : ℂ) * Complex.I) - (u : ℂ)).im = ε := by simp
    have h1 : ε ≤ ‖((t : ℂ) + (ε : ℂ) * Complex.I) - (u : ℂ)‖ := by
      have := Complex.abs_im_le_norm (((t : ℂ) + (ε : ℂ) * Complex.I) - (u : ℂ))
      rw [him, abs_of_pos hε] at this
      exact this
    rw [norm_inv, one_div]
    exact inv_anti₀ hε h1
  have h := integral_re hint
  simp only [RCLike.re_to_complex] at h
  rw [← h]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  show (((t : ℂ) + (ε : ℂ) * Complex.I - (u : ℂ))⁻¹).re = kε ε (t - u)
  rw [← inv_re_eq ε (t - u)]
  congr 2
  push_cast
  ring

lemma abs_reCauchy_le (μ : Measure ℝ) [IsProbabilityMeasure μ] {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    |reCauchy μ t ε| ≤ 1 / ε := by
  rw [reCauchy_eq μ hε t, ← Real.norm_eq_abs]
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun u => kε ε (t - u))
    (ae_of_all _ fun u => by rw [Real.norm_eq_abs]; exact abs_kε_le hε (t - u))
  rwa [probReal_univ, mul_one] at this

lemma continuous_reCauchy (μ : Measure ℝ) [IsProbabilityMeasure μ] {ε : ℝ} (hε : 0 < ε) :
    Continuous fun t => reCauchy μ t ε := by
  have hk := continuous_kε hε
  have : Continuous fun t => ∫ u, kε ε (t - u) ∂μ := by
    refine continuous_of_dominated (bound := fun _ => 1 / ε)
      (fun t => (hk.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
      (fun t => ae_of_all _ fun u => by rw [Real.norm_eq_abs]; exact abs_kε_le hε _)
      (integrable_const _) (ae_of_all _ fun u => hk.comp (continuous_id.sub continuous_const))
  exact this.congr fun t => (reCauchy_eq μ hε t).symm

/-! ## 2. Symmetrization -/

/-- **`eq:B3-continuum-symmetrization`**. -/
theorem symmetrization (μ : Measure ℝ) [IsProbabilityMeasure μ] {ε : ℝ} (hε : 0 < ε)
    {f : ℝ → ℝ} (hfc : Continuous f) {C0 : ℝ} (hC0 : ∀ x, |f x| ≤ C0) :
    ∫ t, f t * reCauchy μ t ε ∂μ =
      (1 / 2) * ∫ p, (f p.1 - f p.2) * kε ε (p.1 - p.2) ∂(μ.prod μ) := by
  have hk := continuous_kε hε
  have hC00 : 0 ≤ C0 := (abs_nonneg _).trans (hC0 0)
  set F : ℝ × ℝ → ℝ := fun p => f p.1 * kε ε (p.1 - p.2) with hFdef
  set F' : ℝ × ℝ → ℝ := fun p => f p.2 * kε ε (p.1 - p.2) with hF'def
  have hFm : Measurable F := by
    have := hfc.measurable; have := hk.measurable; rw [hFdef]; fun_prop
  have hF'm : Measurable F' := by
    have := hfc.measurable; have := hk.measurable; rw [hF'def]; fun_prop
  have hbd : ∀ a b : ℝ, |f a * kε ε b| ≤ C0 * (1 / ε) := fun a b => by
    rw [abs_mul]; exact mul_le_mul (hC0 _) (abs_kε_le hε _) (abs_nonneg _) hC00
  have hFint : Integrable F (μ.prod μ) := Integrable.of_bound hFm.aestronglyMeasurable
    (C0 * (1 / ε)) (ae_of_all _ fun p => by rw [Real.norm_eq_abs]; exact hbd _ _)
  have hF'int : Integrable F' (μ.prod μ) := Integrable.of_bound hF'm.aestronglyMeasurable
    (C0 * (1 / ε)) (ae_of_all _ fun p => by rw [Real.norm_eq_abs]; exact hbd _ _)
  have h1 : ∫ t, f t * reCauchy μ t ε ∂μ = ∫ p, F p ∂(μ.prod μ) := by
    rw [integral_prod F hFint]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    show f t * reCauchy μ t ε = ∫ y, F (t, y) ∂μ
    rw [reCauchy_eq μ hε t, ← integral_const_mul]
  have h2 : ∫ p, F p ∂(μ.prod μ) = -∫ p, F' p ∂(μ.prod μ) := by
    rw [← integral_prod_swap F, ← integral_neg]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    simp only [hFdef, hF'def, Prod.fst_swap, Prod.snd_swap]
    rw [show p.2 - p.1 = -(p.1 - p.2) by ring, kε_neg]
    ring
  have h3 : ∫ p, (f p.1 - f p.2) * kε ε (p.1 - p.2) ∂(μ.prod μ) =
      ∫ p, F p ∂(μ.prod μ) - ∫ p, F' p ∂(μ.prod μ) := by
    rw [← integral_sub hFint hF'int]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    simp only [hFdef, hF'def]
    ring
  rw [h1, h3, h2]
  ring

/-! ## 3. The limits `ε ↓ 0` -/

lemma abs_mul_kε_le {C1 a x ε : ℝ} (hC1 : 0 ≤ C1) (ha : |a| ≤ C1 * |x|) :
    |a * kε ε x| ≤ C1 := by
  unfold kε
  rw [abs_mul, abs_div, abs_of_nonneg (by positivity : 0 ≤ x ^ 2 + ε ^ 2)]
  rcases (by positivity : (0 : ℝ) ≤ x ^ 2 + ε ^ 2).eq_or_lt with h | h
  · rw [← h, div_zero, mul_zero]; exact hC1
  · rw [← mul_div_assoc, div_le_iff₀ h]
    calc |a| * |x| ≤ C1 * |x| * |x| := by gcongr
      _ = C1 * x ^ 2 := by rw [mul_assoc, ← sq, sq_abs]
      _ ≤ C1 * (x ^ 2 + ε ^ 2) := by gcongr; nlinarith [sq_nonneg ε]

/-- The symmetrized right side converges to `∬ dd f` as `ε ↓ 0` (nonatomic `μ`). -/
theorem tendsto_symm (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hcs : HasCompactSupport f) :
    Tendsto (fun ε => ∫ p, (f p.1 - f p.2) * kε ε (p.1 - p.2) ∂(μ.prod μ)) (𝓝[>] 0)
      (𝓝 (∫ p, dd f p.1 p.2 ∂(μ.prod μ))) := by
  obtain ⟨C0, C1, hC1, hC0, hd, hlip⟩ := c1c_bounds hf hcs
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => C1) ?_ ?_
    (integrable_const _) ?_
  · refine Eventually.of_forall fun ε => ?_
    have := hf.continuous.measurable
    have hk : Measurable fun x : ℝ => kε ε x := by unfold kε; fun_prop
    exact (by fun_prop : Measurable fun p : ℝ × ℝ => (f p.1 - f p.2) * kε ε (p.1 - p.2)).aestronglyMeasurable
  · exact Eventually.of_forall fun ε => ae_of_all _ fun p => by
      rw [Real.norm_eq_abs]; exact abs_mul_kε_le hC1.le (hlip p.1 p.2)
  · refine (measure_eq_zero_iff_ae_notMem.1 (prod_diagonal_null μ)).mono fun p hp => ?_
    have hne : p.1 - p.2 ≠ 0 := sub_ne_zero.2 hp
    have hc : Continuous fun ε : ℝ => (f p.1 - f p.2) * kε ε (p.1 - p.2) := by
      unfold kε
      exact continuous_const.mul (continuous_const.div (by fun_prop) fun ε => by positivity)
    have h0 : (f p.1 - f p.2) * kε 0 (p.1 - p.2) = dd f p.1 p.2 := by
      have hne' : p.1 ≠ p.2 := hp
      simp only [kε, dd, hne', ↓reduceIte]
      field_simp
      ring
    rw [← h0]
    exact (hc.tendsto 0).mono_left nhdsWithin_le_nhds

/-- The locally uniform boundary alternative implies the bounded-a.e. one. -/
theorem boundedAE_of_locallyUniform (μ : Measure ℝ) [IsProbabilityMeasure μ] {g : ℝ → ℝ}
    (hU : LocallyUniformBoundary μ g) : BoundedAEBoundary μ g := by
  refine ⟨fun K hK => ?_, ae_of_all _ fun t => (hU {t} isCompact_singleton).tendsto_at rfl⟩
  have h1 := Metric.tendstoUniformlyOn_iff.1 (hU K hK) 1 one_pos
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h1
  have hu0 : (0 : ℝ) < u := hu
  have hε0 : u / 2 ∈ Ioo 0 u := ⟨by positivity, by linarith⟩
  refine ⟨1 / (u / 2) + 2, u, hu0, fun ε hε t ht => ?_⟩
  have a1 : dist (g t) (reCauchy μ t ε) < 1 := hsub hε t ht
  have a2 : dist (g t) (reCauchy μ t (u / 2)) < 1 := hsub hε0 t ht
  have a3 := abs_reCauchy_le μ hε0.1 t
  rw [Real.dist_eq] at a1 a2
  have b1 := abs_sub_abs_le_abs_sub (reCauchy μ t ε) (g t)
  have b2 := abs_sub_abs_le_abs_sub (g t) (reCauchy μ t (u / 2))
  rw [abs_sub_comm] at b1
  linarith

/-- Under the bounded-a.e. alternative, the boundary function is a.e. strongly measurable. -/
lemma aestronglyMeasurable_boundary (μ : Measure ℝ) [IsProbabilityMeasure μ] {g : ℝ → ℝ}
    (hB : BoundedAEBoundary μ g) : AEStronglyMeasurable g μ := by
  have hseq : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun n => by simp only [mem_Ioi]; positivity⟩
  refine aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun (n : ℕ) (t : ℝ) => reCauchy μ t (1 / ((n : ℝ) + 1))) (fun n => ?_)
    (hB.2.mono fun t ht => ht.comp hseq)
  exact (continuous_reCauchy μ (by positivity)).aestronglyMeasurable

/-- Under the bounded-a.e. alternative, the boundary function is a.e. bounded on compacts. -/
lemma ae_bound_boundary (μ : Measure ℝ) [IsProbabilityMeasure μ] {g : ℝ → ℝ}
    (hB : BoundedAEBoundary μ g) {K : Set ℝ} (hK : IsCompact K) :
    ∃ C : ℝ, ∀ᵐ t ∂μ, t ∈ K → |g t| ≤ C := by
  obtain ⟨C, δ, hδ, hb⟩ := hB.1 K hK
  refine ⟨C, hB.2.mono fun t ht htK => ?_⟩
  exact le_of_tendsto (continuous_abs.tendsto _ |>.comp ht)
    (Filter.mem_of_superset (Ioo_mem_nhdsGT hδ) fun ε hε => hb ε hε t htK)

/-- The left side converges to `∫ f g dμ` (bounded-a.e. alternative). -/
theorem tendsto_lhs (μ : Measure ℝ) [IsProbabilityMeasure μ] {g : ℝ → ℝ}
    (hB : BoundedAEBoundary μ g) {f : ℝ → ℝ} (hfc : Continuous f) (hcs : HasCompactSupport f) :
    Tendsto (fun ε => ∫ t, f t * reCauchy μ t ε ∂μ) (𝓝[>] 0) (𝓝 (∫ t, f t * g t ∂μ)) := by
  obtain ⟨C0, hC0⟩ := hfc.bounded_above_of_compact_support hcs
  obtain ⟨Cb, δ, hδ, hb⟩ := hB.1 (tsupport f) hcs.isCompact
  have hC00 : 0 ≤ C0 := (norm_nonneg _).trans (hC0 0)
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => C0 * |Cb|) ?_ ?_
    (integrable_const _) ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (hfc.mul (continuous_reCauchy μ hε)).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
    refine ae_of_all _ fun t => ?_
    rw [Real.norm_eq_abs, abs_mul]
    by_cases ht : t ∈ tsupport f
    · exact mul_le_mul (by simpa using hC0 t) ((hb ε hε t ht).trans (le_abs_self Cb))
        (abs_nonneg _) hC00
    · rw [image_eq_zero_of_notMem_tsupport ht, abs_zero, zero_mul]; positivity
  · exact hB.2.mono fun t ht => ht.const_mul (f t)

/-- **`∫ f · Re G_μ(· + i0) dμ = ½ ∬ dd f dμ dμ`** for `f ∈ C_c^1`, under either boundary
alternative of DEF-043 and nonatomic `μ`. -/
theorem integral_reG (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    {g : ℝ → ℝ} (hbd : LocallyUniformBoundary μ g ∨ BoundedAEBoundary μ g)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hcs : HasCompactSupport f) :
    ∫ t, f t * g t ∂μ = (1 / 2) * ∫ p, dd f p.1 p.2 ∂(μ.prod μ) := by
  have hB : BoundedAEBoundary μ g := hbd.elim (boundedAE_of_locallyUniform μ) id
  obtain ⟨C0, C1, -, hC0, -, -⟩ := c1c_bounds hf hcs
  have hl := tendsto_lhs μ hB hf.continuous hcs
  have hr := (tendsto_symm μ hf hcs).const_mul (1 / 2)
  refine tendsto_nhds_unique hl (hr.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (symmetrization μ hε hf.continuous hC0).symm

/-! ## 4. Identification -/

/-- **Identification** (`eq:B3-limit-label-function`): a measurable integer label function obeying
the uniform label bound and `eq:B3-limit-weak-identity` for every `f ∈ C_c^1` equals
`n(t) = Lt/(2π) − κ Re G_μ(t+i0)/π` `μ`-a.e. -/
theorem ae_eq_indexLabel {L κ : ℝ} (hL : 0 < L) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] {reG : ℝ → ℝ}
    (hbd : LocallyUniformBoundary μ reG ∨ BoundedAEBoundary μ reG)
    {g : ℝ → ℤ} (hg : Measurable g)
    (hgb : ∀ᵐ t ∂μ, |(g t : ℝ)| ≤ (L / (2 * Real.pi)) * (|t| + 3 * Real.sqrt (κ / L)))
    (hid : ∀ f : ℝ → ℝ, ContDiff ℝ 1 f → HasCompactSupport f →
      ∫ t, (g t : ℝ) * f t ∂μ = (L / (2 * Real.pi)) * ∫ t, t * f t ∂μ -
        (κ / (2 * Real.pi)) * ∫ p, dd f p.1 p.2 ∂(μ.prod μ)) :
    ∀ᵐ t ∂μ, (g t : ℝ) = indexLabel L κ reG t := by
  have hB : BoundedAEBoundary μ reG := hbd.elim (boundedAE_of_locallyUniform μ) id
  have hreGm := aestronglyMeasurable_boundary μ hB
  have hgm : Measurable fun t => (g t : ℝ) := measurable_from_top.comp hg
  have hIm : AEStronglyMeasurable (indexLabel L κ reG) μ := by
    unfold indexLabel
    exact (((continuous_const.mul continuous_id).div_const _).aemeasurable.sub
      ((hreGm.aemeasurable.const_mul κ).div_const _)).aestronglyMeasurable
  -- local integrability
  have hloc_g : LocallyIntegrable (fun t => (g t : ℝ)) μ := by
    rw [locallyIntegrable_iff]
    intro K hK
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
    refine Measure.integrableOn_of_bounded (measure_ne_top _ _) hgm.aestronglyMeasurable
      (M := (L / (2 * Real.pi)) * (|R| + 3 * Real.sqrt (κ / L))) ?_
    refine (ae_restrict_iff' hK.measurableSet).2 (hgb.mono fun t ht htK => ?_)
    have h1 : |t| ≤ |R| := by
      have := hR htK
      rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
      exact this.trans (le_abs_self R)
    rw [Real.norm_eq_abs]
    refine ht.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
  have hloc_I : LocallyIntegrable (indexLabel L κ reG) μ := by
    rw [locallyIntegrable_iff]
    intro K hK
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
    obtain ⟨C, hC⟩ := ae_bound_boundary μ hB hK
    refine Measure.integrableOn_of_bounded (measure_ne_top _ _) hIm
      (M := L * |R| / (2 * Real.pi) + |κ| * |C| / Real.pi) ?_
    refine (ae_restrict_iff' hK.measurableSet).2 (hC.mono fun t ht htK => ?_)
    have h1 : |t| ≤ |R| := by
      have := hR htK
      rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
      exact this.trans (le_abs_self R)
    have h2 := (ht htK).trans (le_abs_self C)
    rw [Real.norm_eq_abs]
    unfold indexLabel
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · rw [abs_div, abs_mul, abs_of_pos hL, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
      gcongr
    · rw [abs_div, abs_mul, abs_of_pos Real.pi_pos]
      gcongr
  refine ae_eq_of_integral_contDiff_smul_eq hloc_g hloc_I fun φ hφ hcs => ?_
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by exact_mod_cast le_top)
  obtain ⟨C0, C1, -, hC0, -, -⟩ := c1c_bounds hφ1 hcs
  have hC00 : 0 ≤ C0 := (abs_nonneg _).trans (hC0 0)
  have hreg := integral_reG μ hbd hφ1 hcs
  have hint1 : Integrable (fun t => t * φ t) μ :=
    (continuous_id.mul hφ1.continuous).integrable_of_hasCompactSupport hcs.mul_left
  obtain ⟨Cb, hCb⟩ := ae_bound_boundary μ hB hcs.isCompact
  have hint2 : Integrable (fun t => φ t * reG t) μ := by
    refine Integrable.of_bound (hφ1.continuous.aestronglyMeasurable.mul hreGm) (C0 * |Cb|)
      (hCb.mono fun t ht => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    by_cases htK : t ∈ tsupport φ
    · exact mul_le_mul (hC0 t) ((ht htK).trans (le_abs_self Cb)) (abs_nonneg _) hC00
    · rw [image_eq_zero_of_notMem_tsupport htK, abs_zero, zero_mul]; positivity
  have e1 : ∫ t, φ t • (g t : ℝ) ∂μ = ∫ t, (g t : ℝ) * φ t ∂μ :=
    integral_congr_ae (ae_of_all _ fun t => by
      show φ t • (g t : ℝ) = (g t : ℝ) * φ t
      rw [smul_eq_mul, mul_comm])
  have e2 : ∫ t, φ t • indexLabel L κ reG t ∂μ =
      ∫ t, ((L / (2 * Real.pi)) * (t * φ t) - (κ / Real.pi) * (φ t * reG t)) ∂μ :=
    integral_congr_ae (ae_of_all _ fun t => by
      simp only [smul_eq_mul, indexLabel]; ring)
  rw [e1, e2, integral_sub (hint1.const_mul _) (hint2.const_mul _), integral_const_mul,
    integral_const_mul, hid φ hφ1 hcs, hreg]
  ring

end QuantumNLS.LabelIdentification

#print axioms QuantumNLS.LabelIdentification.reCauchy_eq
#print axioms QuantumNLS.LabelIdentification.symmetrization
#print axioms QuantumNLS.LabelIdentification.tendsto_symm
#print axioms QuantumNLS.LabelIdentification.boundedAE_of_locallyUniform
#print axioms QuantumNLS.LabelIdentification.integral_reG
#print axioms QuantumNLS.LabelIdentification.ae_eq_indexLabel
