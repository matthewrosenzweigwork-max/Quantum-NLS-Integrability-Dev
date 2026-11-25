import Mathlib

/-!
# F05:transport (R-7CAE5993): quantiles and convergence in quadratic transport

Source: `source/chapters/foundations/F05.tex` (sha256 `555689b4…`): the definitions of `W_2` and
`Q_σ` (lines 224-234), Lemma `F05:transport` (lines 236-259, equations `F05:quantile-formula`,
`F05:expected-tail-assumption`, `F05:expected-transport`) and its proof (lines 261-360).

## Literal definitions
* `IsCoupling σ τ π`: `π` is a probability measure on `ℝ × ℝ` with first marginal `σ` and second
  marginal `τ`.
* `cost π = ∫ |x - y|^2 dπ` (in `ℝ≥0∞`), and
  `W2 σ τ = inf_{π coupling} (∫ |x - y|^2 dπ)^{1/2}` (in `ℝ≥0∞`).
* `quantile σ s = inf {x : σ((-∞, x]) ≥ s}` (used for `0 < s < 1`).
* `HasFiniteSecondMoment σ`: `x ↦ x^2` is `σ`-integrable.

## Statements (see the final section)
* `W2_eq_eLpNorm_quantile` (`F05:quantile-formula`).
* `W2_empirical_sq` (ordered `N`-point uniform empirical measures).
* `tendsto_W2_of_weak_of_moment` (weak convergence plus second moments).
* `tendsto_expected_W2_sq` (`F05:expected-transport` under `F05:expected-tail-assumption`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal BoundedContinuousFunction

namespace QuantumNLS.QuantileTransport

/-! ## Definitions -/

/-- `π` is a probability measure on `ℝ²` with first marginal `σ` and second marginal `τ`. -/
def IsCoupling (σ τ : Measure ℝ) (π : Measure (ℝ × ℝ)) : Prop :=
  IsProbabilityMeasure π ∧ π.map Prod.fst = σ ∧ π.map Prod.snd = τ

/-- The quadratic cost `∫ |x - y|^2 dπ(x, y)`. -/
def cost (π : Measure (ℝ × ℝ)) : ℝ≥0∞ :=
  ∫⁻ p, ENNReal.ofReal (|p.1 - p.2| ^ 2) ∂π

/-- The quadratic Wasserstein distance: the infimum over couplings of `(∫ |x-y|^2 dπ)^{1/2}`. -/
def W2 (σ τ : Measure ℝ) : ℝ≥0∞ :=
  ⨅ (π : Measure (ℝ × ℝ)) (_ : IsCoupling σ τ π), cost π ^ (1 / 2 : ℝ)

/-- The quantile function `Q_σ(s) = inf {x : σ((-∞, x]) ≥ s}` (meaningful for `0 < s < 1`). -/
def quantile (σ : Measure ℝ) (s : ℝ) : ℝ :=
  sInf {x : ℝ | s ≤ (σ (Iic x)).toReal}

/-- Finite second moment: `∫ x^2 dσ < ∞`. -/
def HasFiniteSecondMoment (σ : Measure ℝ) : Prop :=
  Integrable (fun x : ℝ => x ^ 2) σ

/-- Lebesgue measure on `(0,1)`. -/
abbrev leb01 : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)

/-! ## The distribution function and the quantile -/

lemma toReal_Iic_eq_cdf (σ : Measure ℝ) [IsProbabilityMeasure σ] (x : ℝ) :
    (σ (Iic x)).toReal = cdf σ x := by
  rw [cdf_eq_real]; rfl

lemma quantile_set_nonempty (σ : Measure ℝ) [IsProbabilityMeasure σ] {s : ℝ} (hs : s < 1) :
    {x : ℝ | s ≤ (σ (Iic x)).toReal}.Nonempty := by
  obtain ⟨x, hx⟩ := ((tendsto_cdf_atTop (μ := σ)).eventually (eventually_gt_nhds hs)).exists
  exact ⟨x, by simp only [mem_ofPred_eq, toReal_Iic_eq_cdf]; exact hx.le⟩

lemma quantile_set_bddBelow (σ : Measure ℝ) [IsProbabilityMeasure σ] {s : ℝ} (hs : 0 < s) :
    BddBelow {x : ℝ | s ≤ (σ (Iic x)).toReal} := by
  obtain ⟨a, ha⟩ := Filter.eventually_atBot.1
    ((tendsto_cdf_atBot (μ := σ)).eventually (eventually_lt_nhds hs))
  refine ⟨a, fun y hy => ?_⟩
  simp only [mem_ofPred_eq, toReal_Iic_eq_cdf] at hy
  by_contra h
  exact absurd hy (not_le.2 (ha y (not_le.1 h).le))

/-- Right-continuity: the distribution function at `Q_σ(s)` is at least `s`. -/
lemma le_cdf_quantile (σ : Measure ℝ) [IsProbabilityMeasure σ] {s : ℝ} (hs : s ∈ Ioo 0 1) :
    s ≤ cdf σ (quantile σ s) := by
  set S := {x : ℝ | s ≤ (σ (Iic x)).toReal}
  have hne := quantile_set_nonempty σ hs.2
  have hrc : Tendsto (cdf σ) (𝓝[>] (quantile σ s)) (𝓝 (cdf σ (quantile σ s))) :=
    ((cdf σ).right_continuous _).mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
  refine ge_of_tendsto hrc (eventually_nhdsWithin_of_forall fun y hy => ?_)
  obtain ⟨z, hzS, hzy⟩ := exists_lt_of_csInf_lt hne (show sInf S < y from hy)
  have : s ≤ cdf σ z := by simpa [S, toReal_Iic_eq_cdf] using hzS
  exact this.trans (monotone_cdf σ hzy.le)

/-- The Galois connection: `Q_σ(s) ≤ x ↔ s ≤ σ((-∞, x])` for `0 < s < 1`. -/
lemma quantile_le_iff (σ : Measure ℝ) [IsProbabilityMeasure σ] {s : ℝ} (hs : s ∈ Ioo 0 1)
    (x : ℝ) : quantile σ s ≤ x ↔ s ≤ (σ (Iic x)).toReal := by
  constructor
  · intro h
    rw [toReal_Iic_eq_cdf]
    exact (le_cdf_quantile σ hs).trans (monotone_cdf σ h)
  · intro h
    exact csInf_le (quantile_set_bddBelow σ hs.1) h

lemma lt_quantile_iff (σ : Measure ℝ) [IsProbabilityMeasure σ] {s : ℝ} (hs : s ∈ Ioo 0 1)
    (x : ℝ) : x < quantile σ s ↔ (σ (Iic x)).toReal < s := by
  rw [← not_le, quantile_le_iff σ hs, not_le]

lemma quantile_monotoneOn (σ : Measure ℝ) [IsProbabilityMeasure σ] :
    MonotoneOn (quantile σ) (Ioo 0 1) := by
  intro s hs t ht hst
  rw [quantile_le_iff σ hs]
  exact hst.trans ((quantile_le_iff σ ht _).1 le_rfl)

/-- The measurable modification of the quantile: `Q_σ` on `(0,1)`, zero outside. -/
def qm (σ : Measure ℝ) : ℝ → ℝ := (Ioo (0 : ℝ) 1).indicator (quantile σ)

lemma qm_of_mem (σ : Measure ℝ) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) : qm σ s = quantile σ s :=
  indicator_of_mem hs _

lemma qm_monotoneOn (σ : Measure ℝ) [IsProbabilityMeasure σ] :
    MonotoneOn (qm σ) (Ioo 0 1) := by
  intro s hs t ht hst
  rw [qm_of_mem σ hs, qm_of_mem σ ht]
  exact quantile_monotoneOn σ hs ht hst

lemma measurable_qm (σ : Measure ℝ) [IsProbabilityMeasure σ] : Measurable (qm σ) := by
  refine measurable_of_restrict_of_restrict_compl (measurableSet_Ioo (a := (0:ℝ)) (b := 1)) ?_ ?_
  · have : Monotone ((Ioo (0 : ℝ) 1).domRestrict (qm σ)) := by
      intro a b hab
      exact qm_monotoneOn σ a.2 b.2 hab
    exact this.measurable
  · have : ((Ioo (0 : ℝ) 1)ᶜ.domRestrict (qm σ)) = fun _ => 0 := by
      funext a
      exact indicator_of_notMem a.2 _
    rw [this]; exact measurable_const

lemma qm_le_iff (σ : Measure ℝ) [IsProbabilityMeasure σ] {s : ℝ} (hs : s ∈ Ioo 0 1)
    (x : ℝ) : qm σ s ≤ x ↔ s ≤ (σ (Iic x)).toReal := by
  rw [qm_of_mem σ hs]; exact quantile_le_iff σ hs x

instance : IsProbabilityMeasure leb01 :=
  ⟨by simp [Measure.restrict_apply MeasurableSet.univ, Real.volume_Ioo]⟩

lemma leb01_Iic_inter (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    volume (Ioo (0 : ℝ) 1 ∩ Iic c) = ENNReal.ofReal c := by
  rcases hc1.lt_or_eq with hc | hc
  · have : Ioo (0 : ℝ) 1 ∩ Iic c = Ioc 0 c := by
      ext s; simp only [mem_inter_iff, mem_Ioo, mem_Iic, mem_Ioc]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨⟨h1, lt_of_le_of_lt h3 hc⟩, h3⟩
    rw [this, Real.volume_Ioc, sub_zero]
  · subst hc
    have : Ioo (0 : ℝ) 1 ∩ Iic 1 = Ioo 0 1 := inter_eq_left.2 fun s hs => le_of_lt hs.2
    rw [this, Real.volume_Ioo, sub_zero]

/-- The push-forward of Lebesgue measure on `(0,1)` by `Q_σ` is `σ`. -/
lemma map_qm (σ : Measure ℝ) [IsProbabilityMeasure σ] : leb01.map (qm σ) = σ := by
  refine Measure.ext_of_Iic _ _ fun x => ?_
  rw [Measure.map_apply (measurable_qm σ) measurableSet_Iic,
    Measure.restrict_apply (measurable_qm σ measurableSet_Iic)]
  have hset : qm σ ⁻¹' Iic x ∩ Ioo 0 1 = Ioo 0 1 ∩ Iic (σ (Iic x)).toReal := by
    ext s
    simp only [mem_inter_iff, mem_preimage, mem_Iic]
    constructor
    · rintro ⟨h, hs⟩; exact ⟨hs, (qm_le_iff σ hs x).1 h⟩
    · rintro ⟨hs, h⟩; exact ⟨(qm_le_iff σ hs x).2 h, hs⟩
  rw [hset, leb01_Iic_inter _ ENNReal.toReal_nonneg
    (ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)),
    ENNReal.ofReal_toReal (measure_ne_top _ _)]

lemma map_quantile (σ : Measure ℝ) [IsProbabilityMeasure σ] :
    leb01.map (quantile σ) = σ := by
  have : quantile σ =ᵐ[leb01] qm σ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact (qm_of_mem σ hs).symm
  rw [Measure.map_congr this, map_qm]

/-! ## Monotone coupling optimality (bounded part, via Tonelli) -/

lemma lintegral_ofReal_mul_eq {X : Type*} [MeasurableSpace X] (ρ : Measure X) [SFinite ρ]
    {F G : X → ℝ} (hF : Measurable F) (hG : Measurable G) :
    ∫⁻ x, ENNReal.ofReal (F x) * ENNReal.ofReal (G x) ∂ρ =
      ∫⁻ ab, (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)).indicator
        (fun ab => ρ {x | ab.1 < F x ∧ ab.2 < G x}) ab ∂(volume : Measure (ℝ × ℝ)) := by
  set E : Set (X × (ℝ × ℝ)) :=
    {q | 0 < q.2.1 ∧ q.2.1 < F q.1 ∧ 0 < q.2.2 ∧ q.2.2 < G q.1} with hEdef
  have hE : MeasurableSet E := by
    refine (measurableSet_lt measurable_const (measurable_fst.comp measurable_snd)).inter
      ((measurableSet_lt (measurable_fst.comp measurable_snd) (hF.comp measurable_fst)).inter
      ((measurableSet_lt measurable_const (measurable_snd.comp measurable_snd)).inter
        (measurableSet_lt (measurable_snd.comp measurable_snd) (hG.comp measurable_fst))))
  have h1 : ∀ x, ENNReal.ofReal (F x) * ENNReal.ofReal (G x) =
      ∫⁻ ab, E.indicator 1 (x, ab) ∂(volume : Measure (ℝ × ℝ)) := by
    intro x
    have : (fun ab => E.indicator (1 : X × (ℝ × ℝ) → ℝ≥0∞) (x, ab)) =
        (Ioo 0 (F x) ×ˢ Ioo 0 (G x)).indicator 1 := by
      funext ab
      by_cases h : (x, ab) ∈ E
      · have h' : ab ∈ Ioo 0 (F x) ×ˢ Ioo 0 (G x) := ⟨⟨h.1, h.2.1⟩, ⟨h.2.2.1, h.2.2.2⟩⟩
        rw [indicator_of_mem h, indicator_of_mem h']; rfl
      · have h' : ab ∉ Ioo 0 (F x) ×ˢ Ioo 0 (G x) := by
          rintro ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩; exact h ⟨a1, a2, b1, b2⟩
        rw [indicator_of_notMem h, indicator_of_notMem h']
    rw [this, lintegral_indicator_one (measurableSet_Ioo.prod measurableSet_Ioo),
      Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo, sub_zero,
      sub_zero]
  simp_rw [h1]
  have hmeas : AEMeasurable (Function.uncurry fun x ab => E.indicator (1 : X × (ℝ × ℝ) → ℝ≥0∞)
      (x, ab)) (ρ.prod (volume : Measure (ℝ × ℝ))) :=
    (measurable_one.indicator hE).aemeasurable
  rw [lintegral_lintegral_swap hmeas]
  refine lintegral_congr fun ab => ?_
  by_cases hab : ab ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)
  · rw [indicator_of_mem hab]
    have : (fun x => E.indicator (1 : X × (ℝ × ℝ) → ℝ≥0∞) (x, ab)) =
        {x | ab.1 < F x ∧ ab.2 < G x}.indicator 1 := by
      funext x
      by_cases h : ab.1 < F x ∧ ab.2 < G x
      · rw [indicator_of_mem (show x ∈ {x | ab.1 < F x ∧ ab.2 < G x} from h),
          indicator_of_mem (show (x, ab) ∈ E from ⟨hab.1, h.1, hab.2, h.2⟩)]; rfl
      · rw [indicator_of_notMem (show x ∉ {x | ab.1 < F x ∧ ab.2 < G x} from h),
          indicator_of_notMem (show (x, ab) ∉ E from fun h' => h ⟨h'.2.1, h'.2.2.2⟩)]
    rw [this, lintegral_indicator_one (s := {x | ab.1 < F x ∧ ab.2 < G x})
      ((measurableSet_lt measurable_const hF).inter
      (measurableSet_lt measurable_const hG))]
  · rw [indicator_of_notMem hab]
    have : (fun x => E.indicator (1 : X × (ℝ × ℝ) → ℝ≥0∞) (x, ab)) = fun _ => 0 := by
      funext x
      exact indicator_of_notMem (fun h => hab ⟨h.1, h.2.2.1⟩) _
    rw [this, lintegral_zero]

/-- Upper level sets of two nondecreasing functions on `(0,1)` are nested. -/
lemma leb01_upper_inter (f g : ℝ → ℝ) (hf : MonotoneOn f (Ioo 0 1))
    (hg : MonotoneOn g (Ioo 0 1)) (a b : ℝ) :
    leb01 {s | a < f s ∧ b < g s} = min (leb01 {s | a < f s}) (leb01 {s | b < g s}) := by
  simp only [Measure.restrict_apply' measurableSet_Ioo]
  set A := {s | a < f s} ∩ Ioo 0 1
  set B := {s | b < g s} ∩ Ioo 0 1
  have hAB : {s | a < f s ∧ b < g s} ∩ Ioo 0 1 = A ∩ B := by
    ext s; simp only [A, B, mem_inter_iff, mem_ofPred_eq]; tauto
  rw [hAB]
  have hnest : A ⊆ B ∨ B ⊆ A := by
    by_contra h
    push Not at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨s, hsA, hsB⟩ := Set.not_subset.1 h1
    obtain ⟨t, htB, htA⟩ := Set.not_subset.1 h2
    rcases le_total s t with hst | hts
    · exact htA ⟨lt_of_lt_of_le hsA.1 (hf hsA.2 htB.2 hst), htB.2⟩
    · exact hsB ⟨lt_of_lt_of_le htB.1 (hg htB.2 hsA.2 hts), hsA.2⟩
  rcases hnest with h | h
  · rw [inter_eq_left.2 h, min_eq_left (measure_mono h)]
  · rw [inter_eq_right.2 h, min_eq_right (measure_mono h)]

lemma coupling_fst_apply {σ τ : Measure ℝ} {π : Measure (ℝ × ℝ)} (hπ : IsCoupling σ τ π)
    {S : Set ℝ} (hS : MeasurableSet S) : π {p | p.1 ∈ S} = σ S := by
  rw [← hπ.2.1, Measure.map_apply measurable_fst hS]; rfl

lemma coupling_snd_apply {σ τ : Measure ℝ} {π : Measure (ℝ × ℝ)} (hπ : IsCoupling σ τ π)
    {S : Set ℝ} (hS : MeasurableSet S) : π {p | p.2 ∈ S} = τ S := by
  rw [← hπ.2.2, Measure.map_apply measurable_snd hS]; rfl

lemma leb01_qm_apply (σ : Measure ℝ) [IsProbabilityMeasure σ] {S : Set ℝ}
    (hS : MeasurableSet S) : leb01 {s | qm σ s ∈ S} = σ S := by
  conv_rhs => rw [← map_qm σ]
  rw [Measure.map_apply (measurable_qm σ) hS]; rfl

/-- The monotone rearrangement inequality: for nondecreasing `φ, ψ`, the quantile coupling
maximizes `E[φ(X)⁺ ψ(Y)⁺]` among all couplings. -/
theorem lintegral_coupling_le (σ τ : Measure ℝ) [IsProbabilityMeasure σ] [IsProbabilityMeasure τ]
    {π : Measure (ℝ × ℝ)} (hπ : IsCoupling σ τ π) {φ ψ : ℝ → ℝ} (hφ : Monotone φ)
    (hψ : Monotone ψ) :
    ∫⁻ p, ENNReal.ofReal (φ p.1) * ENNReal.ofReal (ψ p.2) ∂π ≤
      ∫⁻ s, ENNReal.ofReal (φ (qm σ s)) * ENNReal.ofReal (ψ (qm τ s)) ∂leb01 := by
  have := hπ.1
  rw [lintegral_ofReal_mul_eq π (F := fun p => φ p.1) (G := fun p => ψ p.2)
      (hφ.measurable.comp measurable_fst) (hψ.measurable.comp measurable_snd),
    lintegral_ofReal_mul_eq leb01 (F := fun s => φ (qm σ s)) (G := fun s => ψ (qm τ s))
      (hφ.measurable.comp (measurable_qm σ)) (hψ.measurable.comp (measurable_qm τ))]
  refine lintegral_mono fun ab => indicator_le_indicator ?_
  have hfm : MonotoneOn (fun s => φ (qm σ s)) (Ioo 0 1) :=
    fun s hs t ht hst => hφ (qm_monotoneOn σ hs ht hst)
  have hgm : MonotoneOn (fun s => ψ (qm τ s)) (Ioo 0 1) :=
    fun s hs t ht hst => hψ (qm_monotoneOn τ hs ht hst)
  rw [leb01_upper_inter _ _ hfm hgm]
  have hS1 : MeasurableSet {x : ℝ | ab.1 < φ x} := measurableSet_lt measurable_const hφ.measurable
  have hS2 : MeasurableSet {x : ℝ | ab.2 < ψ x} := measurableSet_lt measurable_const hψ.measurable
  have e1 : leb01 {s | ab.1 < φ (qm σ s)} = π {p | p.1 ∈ {x : ℝ | ab.1 < φ x}} := by
    rw [coupling_fst_apply hπ hS1, ← leb01_qm_apply σ hS1]; rfl
  have e2 : leb01 {s | ab.2 < ψ (qm τ s)} = π {p | p.2 ∈ {x : ℝ | ab.2 < ψ x}} := by
    rw [coupling_snd_apply hπ hS2, ← leb01_qm_apply τ hS2]; rfl
  rw [e1, e2]
  exact le_min (measure_mono fun p hp => hp.1) (measure_mono fun p hp => hp.2)

/-! ## Clipping -/

/-- The clipping `χ_R(x) = max(-R, min(x, R))`. -/
def clip (R x : ℝ) : ℝ := max (-R) (min x R)

lemma clip_monotone (R : ℝ) : Monotone (clip R) :=
  fun _ _ h => max_le_max le_rfl (min_le_min h le_rfl)

lemma continuous_clip (R : ℝ) : Continuous (clip R) :=
  continuous_const.max (continuous_id.min continuous_const)

lemma abs_clip_sub_clip_le (R x y : ℝ) : |clip R x - clip R y| ≤ |x - y| := by
  unfold clip
  rw [max_comm (-R), max_comm (-R)]
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  simp

lemma clip_of_abs_le {R x : ℝ} (h : |x| ≤ R) : clip R x = x := by
  unfold clip
  rw [min_eq_left (abs_le.1 h).2, max_eq_right (abs_le.1 h).1]

lemma abs_clip_le {R : ℝ} (hR : 0 ≤ R) (x : ℝ) : |clip R x| ≤ R := by
  unfold clip
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_right _ _)

lemma clip_clip (R x : ℝ) (hR : 0 ≤ R) : clip R (clip R x) = clip R x :=
  clip_of_abs_le (abs_clip_le hR x)

lemma sq_clip_sub_clip_le (R x y : ℝ) : (clip R x - clip R y) ^ 2 ≤ (x - y) ^ 2 := by
  rw [← sq_abs, ← sq_abs (x - y)]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_clip_sub_clip_le R x y) 2

/-- The shifted clipping `χ_R + R`, with values in `[0, 2R]`. -/
def clipS (R x : ℝ) : ℝ := clip R x + R

lemma clipS_monotone (R : ℝ) : Monotone (clipS R) :=
  fun _ _ h => by unfold clipS; linarith [clip_monotone R h]

lemma clipS_nonneg {R : ℝ} (hR : 0 ≤ R) (x : ℝ) : 0 ≤ clipS R x := by
  have := abs_le.1 (abs_clip_le hR x); unfold clipS; linarith

lemma clipS_le {R : ℝ} (hR : 0 ≤ R) (x : ℝ) : clipS R x ≤ 2 * R := by
  have := abs_le.1 (abs_clip_le hR x); unfold clipS; linarith

lemma ofReal_sq_identity {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    ENNReal.ofReal ((u - v) ^ 2) + 2 * (ENNReal.ofReal u * ENNReal.ofReal v) =
      ENNReal.ofReal (u ^ 2) + ENNReal.ofReal (v ^ 2) := by
  rw [← ENNReal.ofReal_mul hu, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (sq_nonneg _) (by positivity),
    ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
  congr 1; ring

lemma lintegral_marg_fst {σ τ : Measure ℝ} {π : Measure (ℝ × ℝ)} (hπ : IsCoupling σ τ π)
    {g : ℝ → ℝ≥0∞} (hg : Measurable g) : ∫⁻ p, g p.1 ∂π = ∫⁻ x, g x ∂σ := by
  rw [← hπ.2.1, lintegral_map hg measurable_fst]

lemma lintegral_marg_snd {σ τ : Measure ℝ} {π : Measure (ℝ × ℝ)} (hπ : IsCoupling σ τ π)
    {g : ℝ → ℝ≥0∞} (hg : Measurable g) : ∫⁻ p, g p.2 ∂π = ∫⁻ x, g x ∂τ := by
  rw [← hπ.2.2, lintegral_map hg measurable_snd]

lemma lintegral_qm (σ : Measure ℝ) [IsProbabilityMeasure σ] {g : ℝ → ℝ≥0∞}
    (hg : Measurable g) : ∫⁻ s, g (qm σ s) ∂leb01 = ∫⁻ x, g x ∂σ := by
  conv_rhs => rw [← map_qm σ]
  rw [lintegral_map hg (measurable_qm σ)]

lemma measurable_clipS (R : ℝ) : Measurable (clipS R) :=
  ((continuous_clip R).add continuous_const).measurable

/-- The bounded step: for the clipped variables the quantile coupling has smaller cost. -/
theorem lintegral_clipS_le (σ τ : Measure ℝ) [IsProbabilityMeasure σ] [IsProbabilityMeasure τ]
    {π : Measure (ℝ × ℝ)} (hπ : IsCoupling σ τ π) {R : ℝ} (hR : 0 ≤ R) :
    ∫⁻ s, ENNReal.ofReal ((clipS R (qm σ s) - clipS R (qm τ s)) ^ 2) ∂leb01 ≤
      ∫⁻ p, ENNReal.ofReal ((clipS R p.1 - clipS R p.2) ^ 2) ∂π := by
  have := hπ.1
  set T := clipS R
  have hT := measurable_clipS R
  have hTsq : Measurable fun x => ENNReal.ofReal (T x ^ 2) :=
    ENNReal.measurable_ofReal.comp (hT.pow_const 2)
  -- the identity `X + 2Y = ∫ T(x)^2 + ∫ T(y)^2` for a general coupling
  have key : ∀ {X : Type} [MeasurableSpace X] (ρ : Measure X) (F G : X → ℝ), Measurable F →
      Measurable G →
      ∫⁻ x, ENNReal.ofReal ((T (F x) - T (G x)) ^ 2) ∂ρ +
        2 * ∫⁻ x, ENNReal.ofReal (T (F x)) * ENNReal.ofReal (T (G x)) ∂ρ =
      ∫⁻ x, ENNReal.ofReal (T (F x) ^ 2) ∂ρ + ∫⁻ x, ENNReal.ofReal (T (G x) ^ 2) ∂ρ := by
    intro X _ ρ F G hF hG
    have m0 : Measurable fun x => ENNReal.ofReal ((T (F x) - T (G x)) ^ 2) :=
      ENNReal.measurable_ofReal.comp (((hT.comp hF).sub (hT.comp hG)).pow_const 2)
    have m1 : Measurable fun x => ENNReal.ofReal (T (F x)) * ENNReal.ofReal (T (G x)) :=
      (ENNReal.measurable_ofReal.comp (hT.comp hF)).mul
        (ENNReal.measurable_ofReal.comp (hT.comp hG))
    calc _ = ∫⁻ x, (ENNReal.ofReal ((T (F x) - T (G x)) ^ 2) +
          2 * (ENNReal.ofReal (T (F x)) * ENNReal.ofReal (T (G x)))) ∂ρ := by
          rw [lintegral_add_left m0, lintegral_const_mul 2 m1]
      _ = ∫⁻ x, (ENNReal.ofReal (T (F x) ^ 2) + ENNReal.ofReal (T (G x) ^ 2)) ∂ρ := by
          refine lintegral_congr fun x => ?_
          exact ofReal_sq_identity (clipS_nonneg hR _) (clipS_nonneg hR _)
      _ = _ := lintegral_add_left (hTsq.comp hF) _
  have hπid := key π Prod.fst Prod.snd measurable_fst measurable_snd
  have hLid := key leb01 (qm σ) (qm τ) (measurable_qm σ) (measurable_qm τ)
  have hmarg : ∫⁻ x, ENNReal.ofReal (T x.1 ^ 2) ∂π + ∫⁻ x, ENNReal.ofReal (T x.2 ^ 2) ∂π =
      ∫⁻ s, ENNReal.ofReal (T (qm σ s) ^ 2) ∂leb01 +
        ∫⁻ s, ENNReal.ofReal (T (qm τ s) ^ 2) ∂leb01 := by
    rw [lintegral_marg_fst hπ hTsq, lintegral_marg_snd hπ hTsq, lintegral_qm σ hTsq,
      lintegral_qm τ hTsq]
  have hY : ∫⁻ x, ENNReal.ofReal (T x.1) * ENNReal.ofReal (T x.2) ∂π ≤
      ∫⁻ s, ENNReal.ofReal (T (qm σ s)) * ENNReal.ofReal (T (qm τ s)) ∂leb01 :=
    lintegral_coupling_le σ τ hπ (clipS_monotone R) (clipS_monotone R)
  have hYfin : 2 * ∫⁻ s, ENNReal.ofReal (T (qm σ s)) * ENNReal.ofReal (T (qm τ s)) ∂leb01
      ≠ ∞ := by
    refine ENNReal.mul_ne_top (by norm_num) (ne_top_of_le_ne_top (b := ∫⁻ _, ENNReal.ofReal
      (2 * R) * ENNReal.ofReal (2 * R) ∂leb01) ?_ (lintegral_mono fun s => ?_))
    · rw [lintegral_const]; simp [ENNReal.mul_eq_top]
    · exact mul_le_mul' (ENNReal.ofReal_le_ofReal (clipS_le hR _))
        (ENNReal.ofReal_le_ofReal (clipS_le hR _))
  refine ENNReal.le_of_add_le_add_right hYfin ?_
  rw [hLid, ← hmarg, ← hπid]
  gcongr

/-- Every coupling costs at least the quantile `L²` distance (all probability measures). -/
theorem lintegral_qm_le_cost (σ τ : Measure ℝ) [IsProbabilityMeasure σ] [IsProbabilityMeasure τ]
    {π : Measure (ℝ × ℝ)} (hπ : IsCoupling σ τ π) :
    ∫⁻ s, ENNReal.ofReal (|qm σ s - qm τ s| ^ 2) ∂leb01 ≤ cost π := by
  set f : ℕ → ℝ → ℝ≥0∞ := fun n s =>
    ENNReal.ofReal ((clipS n (qm σ s) - clipS n (qm τ s)) ^ 2) with hf
  have hfm : ∀ n, Measurable (f n) := fun n =>
    ENNReal.measurable_ofReal.comp ((((measurable_clipS _).comp (measurable_qm σ)).sub
      ((measurable_clipS _).comp (measurable_qm τ))).pow_const 2)
  have hlim : ∀ s, liminf (fun n => f n s) atTop = ENNReal.ofReal (|qm σ s - qm τ s| ^ 2) := by
    intro s
    refine Tendsto.liminf_eq (tendsto_atTop_of_eventually_const (i₀ := ⌈max |qm σ s| |qm τ s|⌉₊)
      fun n hn => ?_)
    have hn' : max |qm σ s| |qm τ s| ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
    simp only [hf, clipS, clip_of_abs_le ((le_max_left _ _).trans hn'),
      clip_of_abs_le ((le_max_right _ _).trans hn'), sq_abs]
    congr 1; ring
  calc ∫⁻ s, ENNReal.ofReal (|qm σ s - qm τ s| ^ 2) ∂leb01
      = ∫⁻ s, liminf (fun n => f n s) atTop ∂leb01 := by simp_rw [hlim]
    _ ≤ liminf (fun n => ∫⁻ s, f n s ∂leb01) atTop := lintegral_liminf_le hfm
    _ ≤ cost π := by
        refine liminf_le_of_frequently_le' (Frequently.of_forall fun n => ?_)
        refine (lintegral_clipS_le σ τ hπ (Nat.cast_nonneg n)).trans (lintegral_mono fun p => ?_)
        refine ENNReal.ofReal_le_ofReal ?_
        rw [sq_abs]
        have : clipS n p.1 - clipS n p.2 = clip n p.1 - clip n p.2 := by unfold clipS; ring
        rw [this]
        exact sq_clip_sub_clip_le _ _ _

/-- The common-quantile coupling `s ↦ (Q_σ(s), Q_τ(s))`, `s` uniform on `(0,1)`. -/
def quantileCoupling (σ τ : Measure ℝ) : Measure (ℝ × ℝ) :=
  leb01.map fun s => (qm σ s, qm τ s)

lemma measurable_qm_pair (σ τ : Measure ℝ) [IsProbabilityMeasure σ] [IsProbabilityMeasure τ] :
    Measurable fun s => (qm σ s, qm τ s) :=
  (measurable_qm σ).prodMk (measurable_qm τ)

lemma isCoupling_quantileCoupling (σ τ : Measure ℝ) [IsProbabilityMeasure σ]
    [IsProbabilityMeasure τ] : IsCoupling σ τ (quantileCoupling σ τ) := by
  refine ⟨by rw [quantileCoupling]; infer_instance, ?_, ?_⟩
  · rw [quantileCoupling, Measure.map_map measurable_fst (measurable_qm_pair σ τ)]
    exact map_qm σ
  · rw [quantileCoupling, Measure.map_map measurable_snd (measurable_qm_pair σ τ)]
    exact map_qm τ

lemma cost_quantileCoupling (σ τ : Measure ℝ) [IsProbabilityMeasure σ]
    [IsProbabilityMeasure τ] :
    cost (quantileCoupling σ τ) = ∫⁻ s, ENNReal.ofReal (|qm σ s - qm τ s| ^ 2) ∂leb01 := by
  rw [cost, quantileCoupling, lintegral_map _ (measurable_qm_pair σ τ)]
  exact ENNReal.measurable_ofReal.comp ((measurable_fst.sub measurable_snd).abs.pow_const 2)

/-- `W₂ σ τ ^ 2` is the quantile `L²` distance squared (with `qm`). -/
theorem W2_eq_qm (σ τ : Measure ℝ) [IsProbabilityMeasure σ] [IsProbabilityMeasure τ] :
    W2 σ τ = (∫⁻ s, ENNReal.ofReal (|qm σ s - qm τ s| ^ 2) ∂leb01) ^ (1 / 2 : ℝ) := by
  refine le_antisymm ?_ ?_
  · rw [← cost_quantileCoupling]
    exact iInf₂_le _ (isCoupling_quantileCoupling σ τ)
  · exact le_iInf₂ fun π hπ =>
      ENNReal.rpow_le_rpow (lintegral_qm_le_cost σ τ hπ) (by norm_num)

/-- The infimum of the quadratic cost over couplings is attained by the quantile coupling. -/
theorem iInf_cost_eq (σ τ : Measure ℝ) [IsProbabilityMeasure σ] [IsProbabilityMeasure τ] :
    ⨅ (π : Measure (ℝ × ℝ)) (_ : IsCoupling σ τ π), cost π =
      ∫⁻ s, ENNReal.ofReal (|qm σ s - qm τ s| ^ 2) ∂leb01 := by
  refine le_antisymm ?_ (le_iInf₂ fun π hπ => lintegral_qm_le_cost σ τ hπ)
  rw [← cost_quantileCoupling]
  exact iInf₂_le _ (isCoupling_quantileCoupling σ τ)

/-! ## Clause 1: `F05:quantile-formula` -/

lemma lintegral_qm_eq_quantile (σ τ : Measure ℝ) :
    ∫⁻ s, ENNReal.ofReal (|qm σ s - qm τ s| ^ 2) ∂leb01 =
      ∫⁻ s in Ioo 0 1, ENNReal.ofReal (|quantile σ s - quantile τ s| ^ 2) := by
  refine setLIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
  simp only [qm_of_mem σ hs, qm_of_mem τ hs]

lemma enorm_rpow_two (a : ℝ) : ‖a‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (|a| ^ 2) := by
  rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg a) (by norm_num),
    Real.rpow_two]

lemma eLpNorm_two_eq (f : ℝ → ℝ) (hf : AEStronglyMeasurable f leb01) :
    eLpNorm f 2 leb01 = (∫⁻ s, ENNReal.ofReal (|f s| ^ 2) ∂leb01) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf]
  simp only [ENNReal.toReal_ofNat, enorm_rpow_two]

lemma aestronglyMeasurable_quantile (σ : Measure ℝ) [IsProbabilityMeasure σ] :
    AEStronglyMeasurable (quantile σ) leb01 :=
  (aemeasurable_restrict_of_monotoneOn measurableSet_Ioo
    (quantile_monotoneOn σ)).aestronglyMeasurable

lemma W2_eq_eLpNorm_qm (σ τ : Measure ℝ) [IsProbabilityMeasure σ] [IsProbabilityMeasure τ] :
    W2 σ τ = eLpNorm (fun s => qm σ s - qm τ s) 2 leb01 := by
  rw [W2_eq_qm, eLpNorm_two_eq (fun s => qm σ s - qm τ s)
    ((measurable_qm σ).sub (measurable_qm τ)).aestronglyMeasurable]

/-- **`F05:quantile-formula`** for all probability measures on `ℝ`:
`W₂(σ, τ) = ‖Q_σ - Q_τ‖_{L²(0,1)}` (in `ℝ≥0∞`). -/
theorem W2_eq_eLpNorm_quantile_of_prob (σ τ : Measure ℝ) [IsProbabilityMeasure σ]
    [IsProbabilityMeasure τ] :
    W2 σ τ = eLpNorm (fun s => quantile σ s - quantile τ s) 2 (volume.restrict (Ioo 0 1)) := by
  rw [W2_eq_qm, eLpNorm_two_eq (fun s => quantile σ s - quantile τ s)
    ((aestronglyMeasurable_quantile σ).sub (aestronglyMeasurable_quantile τ)),
    lintegral_qm_eq_quantile]

/-- **`F05:quantile-formula`**, stated with the source hypotheses (finite second moments). -/
theorem W2_eq_eLpNorm_quantile (σ τ : Measure ℝ) [IsProbabilityMeasure σ]
    [IsProbabilityMeasure τ] (_hσ : HasFiniteSecondMoment σ) (_hτ : HasFiniteSecondMoment τ) :
    W2 σ τ = eLpNorm (fun s => quantile σ s - quantile τ s) 2 (volume.restrict (Ioo 0 1)) :=
  W2_eq_eLpNorm_quantile_of_prob σ τ

lemma integrable_qm_sq (σ : Measure ℝ) [IsProbabilityMeasure σ] (hσ : HasFiniteSecondMoment σ) :
    Integrable (fun s => qm σ s ^ 2) leb01 := by
  have h := hσ
  rw [HasFiniteSecondMoment, ← map_qm σ] at h
  exact (integrable_map_measure (continuous_pow 2).aestronglyMeasurable
    (measurable_qm σ).aemeasurable).1 h

lemma memLp_qm (σ : Measure ℝ) [IsProbabilityMeasure σ] (hσ : HasFiniteSecondMoment σ) :
    MemLp (qm σ) 2 leb01 :=
  (memLp_two_iff_integrable_sq (measurable_qm σ).aestronglyMeasurable).2 (integrable_qm_sq σ hσ)

lemma integral_qm_sq (σ : Measure ℝ) [IsProbabilityMeasure σ] :
    ∫ s, qm σ s ^ 2 ∂leb01 = ∫ x, x ^ 2 ∂σ := by
  conv_rhs => rw [← map_qm σ]
  rw [integral_map (measurable_qm σ).aemeasurable (continuous_pow 2).aestronglyMeasurable]

lemma integrable_sq_sub_qm (σ τ : Measure ℝ) [IsProbabilityMeasure σ] [IsProbabilityMeasure τ]
    (hσ : HasFiniteSecondMoment σ) (hτ : HasFiniteSecondMoment τ) :
    Integrable (fun s => (qm σ s - qm τ s) ^ 2) leb01 :=
  ((memLp_two_iff_integrable_sq ((measurable_qm σ).sub (measurable_qm τ)).aestronglyMeasurable).1
    ((memLp_qm σ hσ).sub (memLp_qm τ hτ)))

lemma W2_sq_eq_ofReal (σ τ : Measure ℝ) [IsProbabilityMeasure σ] [IsProbabilityMeasure τ]
    (hσ : HasFiniteSecondMoment σ) (hτ : HasFiniteSecondMoment τ) :
    W2 σ τ ^ (2 : ℝ) = ENNReal.ofReal (∫ s, (qm σ s - qm τ s) ^ 2 ∂leb01) := by
  rw [W2_eq_qm, ← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one,
    ofReal_integral_eq_lintegral_ofReal (integrable_sq_sub_qm σ τ hσ hτ)
      (Eventually.of_forall fun s => sq_nonneg _)]
  simp only [sq_abs]

/-- Real form of `F05:quantile-formula`: under finite second moments `W₂ < ∞` and
`W₂(σ,τ) = (∫_0^1 |Q_σ - Q_τ|^2)^{1/2}`. -/
theorem W2_toReal_eq_sqrt (σ τ : Measure ℝ) [IsProbabilityMeasure σ] [IsProbabilityMeasure τ]
    (hσ : HasFiniteSecondMoment σ) (hτ : HasFiniteSecondMoment τ) :
    W2 σ τ < ∞ ∧
      (W2 σ τ).toReal = Real.sqrt (∫ s in Ioo 0 1, (quantile σ s - quantile τ s) ^ 2) := by
  have hint : ∫ s in Ioo 0 1, (quantile σ s - quantile τ s) ^ 2 =
      ∫ s, (qm σ s - qm τ s) ^ 2 ∂leb01 := by
    refine setIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
    simp only [qm_of_mem σ hs, qm_of_mem τ hs]
  have hI : 0 ≤ ∫ s, (qm σ s - qm τ s) ^ 2 ∂leb01 := integral_nonneg fun s => sq_nonneg _
  have hW : W2 σ τ = ENNReal.ofReal (∫ s, (qm σ s - qm τ s) ^ 2 ∂leb01) ^ (1 / 2 : ℝ) := by
    rw [← W2_sq_eq_ofReal σ τ hσ hτ, ← ENNReal.rpow_mul]; norm_num
  rw [hint, hW, ENNReal.ofReal_rpow_of_nonneg hI (by norm_num)]
  refine ⟨ENNReal.ofReal_lt_top, ?_⟩
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hI _), Real.sqrt_eq_rpow]

/-- Minkowski: the triangle inequality for `W₂`. -/
theorem W2_triangle (σ τ ρ : Measure ℝ) [IsProbabilityMeasure σ] [IsProbabilityMeasure τ]
    [IsProbabilityMeasure ρ] : W2 σ ρ ≤ W2 σ τ + W2 τ ρ := by
  rw [W2_eq_eLpNorm_qm, W2_eq_eLpNorm_qm, W2_eq_eLpNorm_qm]
  have : (fun s => qm σ s - qm ρ s) = (fun s => qm σ s - qm τ s) + fun s => qm τ s - qm ρ s := by
    funext s; simp
  rw [this]
  exact eLpNorm_add_le (by norm_num)

/-- `W₂(σ, τ) = 0` forces `σ = τ` (the quantiles agree a.e., hence have the same push-forward). -/
theorem eq_of_W2_eq_zero (σ τ : Measure ℝ) [IsProbabilityMeasure σ] [IsProbabilityMeasure τ]
    (h : W2 σ τ = 0) : σ = τ := by
  rw [W2_eq_eLpNorm_qm, eLpNorm_eq_zero_iff (by norm_num)] at h
  have hae : qm σ =ᵐ[leb01] qm τ := by
    filter_upwards [h] with s hs
    exact sub_eq_zero.1 hs
  rw [← map_qm σ, ← map_qm τ, Measure.map_congr hae]

lemma W2_le_cost {σ τ : Measure ℝ} {π : Measure (ℝ × ℝ)} (hπ : IsCoupling σ τ π) :
    W2 σ τ ≤ cost π ^ (1 / 2 : ℝ) :=
  iInf₂_le π hπ

lemma W2_sq_le_cost {σ τ : Measure ℝ} {π : Measure (ℝ × ℝ)} (hπ : IsCoupling σ τ π) :
    W2 σ τ ^ (2 : ℝ) ≤ cost π := by
  calc W2 σ τ ^ (2 : ℝ) ≤ (cost π ^ (1 / 2 : ℝ)) ^ (2 : ℝ) :=
        ENNReal.rpow_le_rpow (W2_le_cost hπ) (by norm_num)
    _ = cost π := by rw [← ENNReal.rpow_mul]; norm_num

/-! ## Clause 2: ordered `N`-point uniform empirical measures -/

/-- The measure giving mass `1/N` to each of the points `x 0, …, x (N-1)`. -/
def empirical (N : ℕ) (x : Fin N → ℝ) : Measure ℝ :=
  ∑ j, (N : ℝ≥0∞)⁻¹ • Measure.dirac (x j)

open Classical in
lemma empirical_apply (N : ℕ) (x : Fin N → ℝ) {S : Set ℝ} (hS : MeasurableSet S) :
    empirical N x S = (N : ℝ≥0∞)⁻¹ * ((Finset.univ.filter fun j => x j ∈ S).card : ℝ≥0∞) := by
  rw [empirical, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hS]
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : x j ∈ S <;> simp [h]

lemma isProbabilityMeasure_empirical {N : ℕ} (hN : 0 < N) (x : Fin N → ℝ) :
    IsProbabilityMeasure (empirical N x) := by
  constructor
  rw [empirical_apply N x MeasurableSet.univ]
  simp only [mem_univ, Finset.filter_true, Finset.card_univ, Fintype.card_fin]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hN.ne') (ENNReal.natCast_ne_top N)

open Classical in
lemma empirical_Iic_toReal (N : ℕ) (x : Fin N → ℝ) (y : ℝ) :
    (empirical N x (Iic y)).toReal =
      ((Finset.univ.filter fun j => x j ≤ y).card : ℝ) / N := by
  rw [empirical_apply N x measurableSet_Iic, ENNReal.toReal_mul, ENNReal.toReal_inv]
  simp only [ENNReal.toReal_natCast, mem_Iic]
  ring

open Classical in
lemma quantile_empirical {N : ℕ} (hN : 0 < N) {x : Fin N → ℝ} (hx : Monotone x) (j : Fin N)
    {s : ℝ} (hs : s ∈ Ioo ((j : ℝ) / N) (((j : ℝ) + 1) / N)) :
    quantile (empirical N x) s = x j := by
  have := isProbabilityMeasure_empirical hN x
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hs01 : s ∈ Ioo (0 : ℝ) 1 := by
    refine ⟨lt_of_le_of_lt (by positivity) hs.1, lt_of_lt_of_le hs.2 ?_⟩
    rw [div_le_one hNr]
    exact_mod_cast j.isLt
  refine le_antisymm ?_ ?_
  · rw [quantile_le_iff _ hs01, empirical_Iic_toReal]
    refine hs.2.le.trans (div_le_div_of_nonneg_right ?_ hNr.le)
    have hsub : Finset.Iic j ⊆ Finset.univ.filter fun i => x i ≤ x j := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hx (Finset.mem_Iic.1 hi)
    have := Finset.card_le_card hsub
    rw [Fin.card_Iic] at this
    exact_mod_cast this
  · by_contra h
    push Not at h
    have h1 := (quantile_le_iff _ hs01 (quantile (empirical N x) s)).1 le_rfl
    rw [empirical_Iic_toReal] at h1
    have hsub : (Finset.univ.filter fun i => x i ≤ quantile (empirical N x) s) ⊆
        Finset.Iio j := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rw [Finset.mem_Iio]
      by_contra hij
      push Not at hij
      exact absurd (hi.trans_lt h) (not_lt.2 (hx hij))
    have hc := Finset.card_le_card hsub
    rw [Fin.card_Iio] at hc
    have : s ≤ (j : ℝ) / N :=
      h1.trans (div_le_div_of_nonneg_right (by exact_mod_cast hc) hNr.le)
    exact absurd hs.1 (not_lt.2 this)

/-- The intervals `((j)/N, (j+1)/N)` cover `(0,1)` up to a null set. -/
lemma Ioo_ae_eq_iUnion {N : ℕ} (hN : 0 < N) :
    Ioo (0 : ℝ) 1 =ᵐ[volume] ⋃ j : Fin N, Ioo ((j : ℝ) / N) (((j : ℝ) + 1) / N) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  refine ae_eq_set.2 ⟨?_, ?_⟩
  · refine measure_mono_null (t := range fun k : ℕ => (k : ℝ) / N) ?_
      ((countable_range _).measure_zero volume)
    rintro s ⟨hs, hsU⟩
    set k := ⌊s * N⌋₊ with hk
    have hk1 : (k : ℝ) ≤ s * N := Nat.floor_le (by nlinarith [hs.1])
    have hk2 : s * N < k + 1 := Nat.lt_floor_add_one _
    have hkN : k < N := by
      have : s * N < N := by nlinarith [hs.2]
      exact_mod_cast (Nat.floor_lt (by nlinarith [hs.1])).2 this
    by_contra hne
    refine hsU (mem_iUnion.2 ⟨⟨k, hkN⟩, ?_, ?_⟩)
    · have : (k : ℝ) / N ≤ s := by rw [div_le_iff₀ hNr]; exact hk1
      exact lt_of_le_of_ne this fun h => hne ⟨k, h⟩
    · show s < ((k : ℝ) + 1) / N
      rw [lt_div_iff₀ hNr]; exact hk2
  · refine measure_mono_null (t := ∅) ?_ measure_empty
    rintro s ⟨hsU, hs⟩
    obtain ⟨j, hj⟩ := mem_iUnion.1 hsU
    refine hs ⟨lt_of_le_of_lt (by positivity) hj.1, lt_of_lt_of_le hj.2 ?_⟩
    rw [div_le_one hNr]
    exact_mod_cast j.isLt

/-- **Empirical clause.** If both measures give mass `1/N` to `N` ordered points, the squared
distance is the average of the squared differences of corresponding ordered points. -/
theorem W2_empirical_sq {N : ℕ} (hN : 0 < N) {x y : Fin N → ℝ} (hx : Monotone x)
    (hy : Monotone y) :
    W2 (empirical N x) (empirical N y) ^ 2 =
      ENNReal.ofReal ((1 / N : ℝ) * ∑ j, (x j - y j) ^ 2) := by
  have := isProbabilityMeasure_empirical hN x
  have := isProbabilityMeasure_empirical hN y
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [W2_eq_qm, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num only [ENNReal.rpow_one]
  rw [lintegral_qm_eq_quantile, setLIntegral_congr (Ioo_ae_eq_iUnion hN),
    lintegral_iUnion (fun j => measurableSet_Ioo) ?_, tsum_fintype]
  · have hj : ∀ j : Fin N, ∫⁻ s in Ioo ((j : ℝ) / N) (((j : ℝ) + 1) / N),
        ENNReal.ofReal (|quantile (empirical N x) s - quantile (empirical N y) s| ^ 2) =
        ENNReal.ofReal ((1 / N : ℝ) * (x j - y j) ^ 2) := by
      intro j
      rw [setLIntegral_congr_fun measurableSet_Ioo (g := fun _ => ENNReal.ofReal ((x j - y j) ^ 2))
        (fun s hs => by simp only [quantile_empirical hN hx j hs, quantile_empirical hN hy j hs,
          sq_abs]), setLIntegral_const, Real.volume_Ioo,
        ← ENNReal.ofReal_mul (sq_nonneg _), mul_comm]
      congr 1; congr 1; field_simp; ring
    simp only [hj]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity), Finset.mul_sum]
  · intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    rintro s ⟨hi1, hi2⟩ ⟨hj1, hj2⟩
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
    · have : ((i : ℝ) + 1) / N ≤ (j : ℝ) / N :=
        div_le_div_of_nonneg_right (by exact_mod_cast h) hNr.le
      linarith
    · have : ((j : ℝ) + 1) / N ≤ (i : ℝ) / N :=
        div_le_div_of_nonneg_right (by exact_mod_cast h) hNr.le
      linarith

/-! ## Clause 3: weak convergence plus convergence of second moments -/

/-- The continuous piecewise linear function equal to `1` on `(-∞, a]` and `0` on `[b, ∞)`. -/
def ramp (a b x : ℝ) : ℝ := max 0 (min 1 ((b - x) / (b - a)))

lemma continuous_ramp (a b : ℝ) : Continuous (ramp a b) :=
  continuous_const.max (continuous_const.min
    ((continuous_const.sub continuous_id).div_const _))

lemma ramp_nonneg (a b x : ℝ) : 0 ≤ ramp a b x := le_max_left _ _

lemma ramp_le_one (a b x : ℝ) : ramp a b x ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

lemma indicator_le_ramp {a b : ℝ} (hab : a < b) (x : ℝ) :
    (Iic a).indicator (1 : ℝ → ℝ) x ≤ ramp a b x := by
  by_cases hx : x ∈ Iic a
  · rw [indicator_of_mem hx, Pi.one_apply]
    have : 1 ≤ (b - x) / (b - a) := by
      rw [le_div_iff₀ (sub_pos.2 hab)]; linarith [mem_Iic.1 hx]
    unfold ramp; rw [min_eq_left this]; exact le_max_right _ _
  · rw [indicator_of_notMem hx]; exact ramp_nonneg _ _ _

lemma ramp_le_indicator {a b : ℝ} (hab : a < b) (x : ℝ) :
    ramp a b x ≤ (Iic b).indicator (1 : ℝ → ℝ) x := by
  by_cases hx : x ∈ Iic b
  · rw [indicator_of_mem hx, Pi.one_apply]; exact ramp_le_one _ _ _
  · rw [indicator_of_notMem hx]
    have : (b - x) / (b - a) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith [not_le.1 (show ¬ x ≤ b from hx)])
        (sub_pos.2 hab).le
    unfold ramp
    exact max_le le_rfl ((min_le_right _ _).trans this)

/-- `ramp a b` as a bounded continuous function. -/
def rampBCF (a b : ℝ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (ramp a b) (continuous_ramp a b) 1 fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (ramp_nonneg a b x)]; exact ramp_le_one a b x

lemma integrable_ramp (μ : Measure ℝ) [IsFiniteMeasure μ] (a b : ℝ) :
    Integrable (ramp a b) μ :=
  (rampBCF a b).integrable μ

lemma cdf_le_integral_ramp (μ : Measure ℝ) [IsProbabilityMeasure μ] {a b : ℝ} (hab : a < b) :
    (μ (Iic a)).toReal ≤ ∫ x, ramp a b x ∂μ := by
  have h := integral_mono (show Integrable ((Iic a).indicator (1 : ℝ → ℝ)) μ from
    (integrable_const (1 : ℝ)).indicator measurableSet_Iic) (integrable_ramp μ a b)
    (indicator_le_ramp hab)
  rwa [integral_indicator_one measurableSet_Iic] at h

lemma integral_ramp_le_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ] {a b : ℝ} (hab : a < b) :
    ∫ x, ramp a b x ∂μ ≤ (μ (Iic b)).toReal := by
  have h := integral_mono (integrable_ramp μ a b)
    (show Integrable ((Iic b).indicator (1 : ℝ → ℝ)) μ from
    (integrable_const (1 : ℝ)).indicator measurableSet_Iic) (ramp_le_indicator hab)
  rwa [integral_indicator_one measurableSet_Iic] at h

lemma cdf_mono' (μ : Measure ℝ) [IsProbabilityMeasure μ] {a b : ℝ} (hab : a ≤ b) :
    (μ (Iic a)).toReal ≤ (μ (Iic b)).toReal :=
  ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Iic_subset_Iic.2 hab))

/-- Hypothesis on a sequence of measures: convergence of the integrals of all the ramps with
rational nodes (a countable family of continuous piecewise linear test functions). -/
def RampConv (σs : ℕ → Measure ℝ) (σ : Measure ℝ) : Prop :=
  ∀ a b : ℚ, (a : ℝ) < b →
    Tendsto (fun j => ∫ x, ramp a b x ∂σs j) atTop (𝓝 (∫ x, ramp a b x ∂σ))

/-- Quantiles converge at every point of `(0,1)` where `Q_σ` is right-continuous. -/
lemma tendsto_quantile_of_rampConv {σs : ℕ → Measure ℝ} {σ : Measure ℝ}
    [∀ j, IsProbabilityMeasure (σs j)] [IsProbabilityMeasure σ] (h : RampConv σs σ)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (hc : ContinuousWithinAt (quantile σ) (Ioo 0 1 ∩ Ioi s) s) :
    Tendsto (fun j => quantile (σs j) s) atTop (𝓝 (quantile σ s)) := by
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · obtain ⟨a', ha1, ha2⟩ := exists_rat_btwn ha
    obtain ⟨b', hb1, hb2⟩ := exists_rat_btwn ha2
    have hFb : (σ (Iic (b' : ℝ))).toReal < s := (lt_quantile_iff σ hs _).1 hb2
    have hlt : ∫ x, ramp a' b' x ∂σ < s :=
      (integral_ramp_le_cdf σ (by exact_mod_cast hb1)).trans_lt hFb
    filter_upwards [(h a' b' (by exact_mod_cast hb1)).eventually (eventually_lt_nhds hlt)]
      with j hj
    refine (lt_quantile_iff (σs j) hs a).2 ?_
    exact ((cdf_mono' (σs j) ha1.le).trans
      (cdf_le_integral_ramp (σs j) (by exact_mod_cast hb1))).trans_lt hj
  · obtain ⟨b', hb1, hb2⟩ := exists_between hb
    have hset : Ioo (0 : ℝ) 1 ∩ Ioi s = Ioo s 1 := by
      ext t; simp only [mem_inter_iff, mem_Ioo, mem_Ioi]
      constructor
      · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨hs.1.trans h1, h2⟩, h1⟩
    rw [hset] at hc
    have hnb : (𝓝[Ioo s 1] s).NeBot := by
      rw [nhdsWithin_Ioo_eq_nhdsGT hs.2]; infer_instance
    obtain ⟨t, htQ, ht⟩ := ((hc.eventually (eventually_lt_nhds hb1)).and
      self_mem_nhdsWithin).exists
    have ht01 : t ∈ Ioo (0 : ℝ) 1 := ⟨hs.1.trans ht.1, ht.2⟩
    obtain ⟨a', ha1, ha2⟩ := exists_rat_btwn htQ
    obtain ⟨b'', hb3, hb4⟩ := exists_rat_btwn ha2
    have hFa : s < (σ (Iic (a' : ℝ))).toReal :=
      ht.1.trans_le (((quantile_le_iff σ ht01 _).1 le_rfl).trans (cdf_mono' σ ha1.le))
    have hgt : s < ∫ x, ramp a' b'' x ∂σ :=
      hFa.trans_le (cdf_le_integral_ramp σ (by exact_mod_cast hb3))
    filter_upwards [(h a' b'' (by exact_mod_cast hb3)).eventually (eventually_gt_nhds hgt)]
      with j hj
    refine lt_of_le_of_lt ((quantile_le_iff (σs j) hs b').2 ?_) hb2
    exact (hj.trans_le (integral_ramp_le_cdf (σs j) (by exact_mod_cast hb3))).le.trans
      (cdf_mono' (σs j) hb4.le)

/-- Hence the quantiles converge almost everywhere on `(0,1)` (a monotone function has at most
countably many discontinuities). -/
lemma ae_tendsto_qm_of_rampConv {σs : ℕ → Measure ℝ} {σ : Measure ℝ}
    [∀ j, IsProbabilityMeasure (σs j)] [IsProbabilityMeasure σ] (h : RampConv σs σ) :
    ∀ᵐ s ∂leb01, Tendsto (fun j => qm (σs j) s) atTop (𝓝 (qm σ s)) := by
  have hcount := (quantile_monotoneOn σ).countable_not_continuousWithinAt_Ioi
  have hnull := hcount.measure_zero (volume : Measure ℝ)
  rw [ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with s hs hs01
  have hc : ContinuousWithinAt (quantile σ) (Ioo 0 1 ∩ Ioi s) s := by
    by_contra hc; exact hs ⟨hs01, hc⟩
  simp only [qm_of_mem _ hs01]
  exact tendsto_quantile_of_rampConv h hs01 hc

/-- The functional-analysis step: an almost everywhere convergent sequence whose `L²` norms
converge to the `L²` norm of the limit converges in `L²`. -/
lemma tendsto_integral_sq_sub {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (u : ℕ → α → ℝ) (v : α → ℝ) (hu : ∀ j, Measurable (u j)) (hv : Measurable v)
    (hiu : ∀ j, Integrable (fun a => u j a ^ 2) μ) (hiv : Integrable (fun a => v a ^ 2) μ)
    (hae : ∀ᵐ a ∂μ, Tendsto (fun j => u j a) atTop (𝓝 (v a)))
    (hn : Tendsto (fun j => ∫ a, u j a ^ 2 ∂μ) atTop (𝓝 (∫ a, v a ^ 2 ∂μ))) :
    Tendsto (fun j => ∫ a, (u j a - v a) ^ 2 ∂μ) atTop (𝓝 0) := by
  set m := ∫ a, v a ^ 2 ∂μ
  have hdom : ∀ j, Integrable (fun a => 2 * u j a ^ 2 + 2 * v a ^ 2) μ := fun j =>
    ((hiu j).const_mul 2).add (hiv.const_mul 2)
  have hint_sub : ∀ j, Integrable (fun a => (u j a - v a) ^ 2) μ := fun j =>
    (hdom j).mono' (((hu j).sub hv).pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun a => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        nlinarith [sq_nonneg (u j a + v a)])
  have hint_add : ∀ j, Integrable (fun a => (u j a + v a) ^ 2) μ := fun j =>
    (hdom j).mono' (((hu j).add hv).pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun a => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        nlinarith [sq_nonneg (u j a - v a)])
  have hid : ∀ j, ∫ a, (u j a + v a) ^ 2 ∂μ =
      2 * ∫ a, u j a ^ 2 ∂μ + 2 * m - ∫ a, (u j a - v a) ^ 2 ∂μ := by
    intro j
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add ((hiu j).const_mul 2)
      (hiv.const_mul 2), ← integral_sub (hdom j) (hint_sub j)]
    refine integral_congr_ae (Eventually.of_forall fun a => ?_)
    simp only; ring
  have hm0 : 0 ≤ m := integral_nonneg fun a => sq_nonneg _
  have he0 : ∀ j, 0 ≤ ∫ a, (u j a - v a) ^ 2 ∂μ := fun j => integral_nonneg fun a => sq_nonneg _
  have hI0 : ∀ j, 0 ≤ ∫ a, (u j a + v a) ^ 2 ∂μ := fun j => integral_nonneg fun a => sq_nonneg _
  -- Fatou for the nonnegative functions `(u_j + v)^2 = 2u_j^2 + 2v^2 - (u_j - v)^2`
  have hfatou : ENNReal.ofReal (4 * m) ≤
      liminf (fun j => ENNReal.ofReal (∫ a, (u j a + v a) ^ 2 ∂μ)) atTop := by
    have hmeas : ∀ j, Measurable fun a => ENNReal.ofReal ((u j a + v a) ^ 2) := fun j =>
      ENNReal.measurable_ofReal.comp (((hu j).add hv).pow_const 2)
    have hlim : ∀ᵐ a ∂μ, liminf (fun j => ENNReal.ofReal ((u j a + v a) ^ 2)) atTop =
        ENNReal.ofReal ((v a + v a) ^ 2) := by
      filter_upwards [hae] with a ha
      exact Tendsto.liminf_eq ((ENNReal.continuous_ofReal.tendsto _).comp
        ((ha.add tendsto_const_nhds).pow 2))
    have h4 : ENNReal.ofReal (4 * m) = ∫⁻ a, ENNReal.ofReal ((v a + v a) ^ 2) ∂μ := by
      rw [← ofReal_integral_eq_lintegral_ofReal ((hiv.const_mul 4).congr
          (Eventually.of_forall fun a => by simp only; ring))
          (Eventually.of_forall fun a => sq_nonneg _)]
      congr 1
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun a => by simp only; ring)
    rw [h4, ← lintegral_congr_ae hlim]
    refine (lintegral_liminf_le hmeas).trans (le_of_eq ?_)
    congr 1; funext j
    rw [ofReal_integral_eq_lintegral_ofReal (hint_add j)
      (Eventually.of_forall fun a => sq_nonneg _)]
  refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun j => ha.trans_le (he0 j),
    fun ε hε => ?_⟩
  by_contra hcon
  rw [not_eventually] at hcon
  have hev : ∀ᶠ j in atTop, 2 * ∫ a, u j a ^ 2 ∂μ < 2 * m + ε / 2 := by
    have : Tendsto (fun j => 2 * ∫ a, u j a ^ 2 ∂μ) atTop (𝓝 (2 * m)) := hn.const_mul 2
    exact this.eventually (eventually_lt_nhds (by linarith))
  have hfreq := hcon.and_eventually hev
  have hle : liminf (fun j => ENNReal.ofReal (∫ a, (u j a + v a) ^ 2 ∂μ)) atTop ≤
      ENNReal.ofReal (4 * m - ε / 2) := by
    refine liminf_le_of_frequently_le' (hfreq.mono fun j hj => ?_)
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hid j]
    linarith [not_lt.1 hj.1, hj.2]
  rcases ENNReal.ofReal_le_ofReal_iff'.1 (hfatou.trans hle) with h1 | h1
  · linarith
  · obtain ⟨j, hj1, hj2⟩ := hfreq.exists
    have := hid j
    linarith [not_lt.1 hj1, hI0 j]

lemma W2_eq_ofReal_rpow (σ τ : Measure ℝ) [IsProbabilityMeasure σ] [IsProbabilityMeasure τ]
    (hσ : HasFiniteSecondMoment σ) (hτ : HasFiniteSecondMoment τ) :
    W2 σ τ = ENNReal.ofReal (∫ s, (qm σ s - qm τ s) ^ 2 ∂leb01) ^ (1 / 2 : ℝ) := by
  rw [← W2_sq_eq_ofReal σ τ hσ hτ, ← ENNReal.rpow_mul]; norm_num

/-- Clause 3, countable-family form: convergence against the ramps with rational nodes plus
convergence of second moments implies `W₂(σ_j, σ) → 0`. -/
theorem tendsto_W2_of_rampConv_of_moment {σs : ℕ → Measure ℝ} {σ : Measure ℝ}
    [∀ j, IsProbabilityMeasure (σs j)] [IsProbabilityMeasure σ]
    (hmj : ∀ j, HasFiniteSecondMoment (σs j)) (hm : HasFiniteSecondMoment σ)
    (h : RampConv σs σ)
    (hmom : Tendsto (fun j => ∫ x, x ^ 2 ∂σs j) atTop (𝓝 (∫ x, x ^ 2 ∂σ))) :
    Tendsto (fun j => W2 (σs j) σ) atTop (𝓝 0) := by
  have hL2 : Tendsto (fun j => ∫ s, (qm (σs j) s - qm σ s) ^ 2 ∂leb01) atTop (𝓝 0) := by
    refine tendsto_integral_sq_sub (fun j => qm (σs j)) (qm σ) (fun j => measurable_qm _)
      (measurable_qm σ) (fun j => integrable_qm_sq _ (hmj j)) (integrable_qm_sq σ hm)
      (ae_tendsto_qm_of_rampConv h) ?_
    simp only [integral_qm_sq]
    exact hmom
  simp only [fun j => W2_eq_ofReal_rpow (σs j) σ (hmj j) hm]
  have : Tendsto (fun j => ENNReal.ofReal (∫ s, (qm (σs j) s - qm σ s) ^ 2 ∂leb01) ^
      (1 / 2 : ℝ)) atTop (𝓝 (ENNReal.ofReal 0 ^ (1 / 2 : ℝ))) :=
    ((ENNReal.continuous_rpow_const).tendsto _).comp
      ((ENNReal.continuous_ofReal.tendsto _).comp hL2)
  rwa [ENNReal.ofReal_zero, ENNReal.zero_rpow_of_pos (by norm_num)] at this

/-- Weak convergence `σ_j ⇀ σ`: `∫ f dσ_j → ∫ f dσ` for every bounded continuous `f`. -/
def WeakConv (σs : ℕ → Measure ℝ) (σ : Measure ℝ) : Prop :=
  ∀ f : ℝ →ᵇ ℝ, Tendsto (fun j => ∫ x, f x ∂σs j) atTop (𝓝 (∫ x, f x ∂σ))

lemma rampConv_of_weakConv {σs : ℕ → Measure ℝ} {σ : Measure ℝ} (h : WeakConv σs σ) :
    RampConv σs σ :=
  fun a b _ => h (rampBCF a b)

/-- Mathlib's weak convergence of probability measures gives `WeakConv`. -/
lemma weakConv_of_tendsto (μs : ℕ → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ)
    (h : Tendsto μs atTop (𝓝 μ)) : WeakConv (fun j => (μs j : Measure ℝ)) μ :=
  ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 h

/-- **Clause 3.** Weak convergence `σ_j ⇀ σ` together with convergence of second moments implies
`W₂(σ_j, σ) → 0`. -/
theorem tendsto_W2_of_weak_of_moment {σs : ℕ → Measure ℝ} {σ : Measure ℝ}
    [∀ j, IsProbabilityMeasure (σs j)] [IsProbabilityMeasure σ]
    (hmj : ∀ j, HasFiniteSecondMoment (σs j)) (hm : HasFiniteSecondMoment σ)
    (hw : WeakConv σs σ)
    (hmom : Tendsto (fun j => ∫ x, x ^ 2 ∂σs j) atTop (𝓝 (∫ x, x ^ 2 ∂σ))) :
    Tendsto (fun j => W2 (σs j) σ) atTop (𝓝 0) :=
  tendsto_W2_of_rampConv_of_moment hmj hm (rampConv_of_weakConv hw) hmom

/-! ## Clause 4: random measures under the expected-tail assumption -/

lemma abs_sub_clip_le {R : ℝ} (hR : 0 ≤ R) (x : ℝ) : |x - clip R x| ≤ |x| := by
  unfold clip
  rcases le_total 0 x with hx | hx
  · have h1 : max (-R) (min x R) ≤ x := max_le (by linarith) (min_le_left _ _)
    have h2 : 0 ≤ max (-R) (min x R) := le_max_of_le_right (le_min hx hR)
    rw [abs_of_nonneg hx, abs_of_nonneg (by linarith)]; linarith
  · have h1 : x ≤ max (-R) (min x R) := by
      rw [min_eq_left (hx.trans hR)]; exact le_max_right _ _
    have h2 : max (-R) (min x R) ≤ 0 := max_le (by linarith) ((min_le_left _ _).trans hx)
    rw [abs_of_nonpos hx, abs_of_nonpos (by linarith)]; linarith

lemma abs_clip_le_abs (R x : ℝ) : |clip R x| ≤ |R| := by
  unfold clip
  rw [abs_le]
  exact ⟨le_max_of_le_left (neg_le_neg (le_abs_self R)),
    max_le (neg_le_abs R) ((min_le_right _ _).trans (le_abs_self R))⟩

/-- The tail second moment `∫_{|x|>R} x^2 dμ`. -/
def tailMoment (μ : Measure ℝ) (R : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in {x : ℝ | R < |x|}, ENNReal.ofReal (x ^ 2) ∂μ

/-- Weak convergence in probability of random probability measures `σ_N(ω)` to a fixed `σ`:
for every bounded continuous `f`, `∫ f dσ_N → ∫ f dσ` in probability. -/
def WeakConvInProb {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (σN : ℕ → Ω → Measure ℝ)
    (σ : Measure ℝ) : Prop :=
  ∀ f : ℝ →ᵇ ℝ, TendstoInMeasure P (fun N ω => ∫ x, f x ∂σN N ω) atTop (fun _ => ∫ x, f x ∂σ)

/-- `F05:expected-tail-assumption`: `lim_{R→∞} sup_N E ∫_{|x|>R} x^2 dσ_N(x) = 0`. -/
def ExpectedTailAssumption {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (σN : ℕ → Ω → Measure ℝ) : Prop :=
  Tendsto (fun R : ℝ => ⨆ N, ∫⁻ ω, tailMoment (σN N ω) R ∂P) atTop (𝓝 0)

lemma measurableSet_tail (R : ℝ) : MeasurableSet {x : ℝ | R < |x|} :=
  measurableSet_lt measurable_const continuous_abs.measurable

lemma W2_comm (σ τ : Measure ℝ) [IsProbabilityMeasure σ] [IsProbabilityMeasure τ] :
    W2 σ τ = W2 τ σ := by
  rw [W2_eq_qm, W2_eq_qm]; simp_rw [abs_sub_comm]

lemma W2_sq_le_cost' {σ τ : Measure ℝ} {π : Measure (ℝ × ℝ)} (hπ : IsCoupling σ τ π) :
    W2 σ τ ^ 2 ≤ cost π := by
  rw [← ENNReal.rpow_two]; exact W2_sq_le_cost hπ

/-- The coupling of a variable with its clipping: `W₂(μ, (χ_R)_#μ)^2 ≤ ∫_{|x|>R} x^2 dμ`. -/
lemma W2_clip_sq_le_tail (μ : Measure ℝ) [IsProbabilityMeasure μ] {R : ℝ} (hR : 0 ≤ R) :
    W2 μ (μ.map (clip R)) ^ 2 ≤ tailMoment μ R := by
  have hc : Measurable (clip R) := (continuous_clip R).measurable
  have hm : Measurable fun x => (x, clip R x) := measurable_id.prodMk hc
  have hπ : IsCoupling μ (μ.map (clip R)) (μ.map fun x => (x, clip R x)) := by
    refine ⟨inferInstance, ?_, ?_⟩
    · rw [Measure.map_map measurable_fst hm]; exact Measure.map_id
    · rw [Measure.map_map measurable_snd hm]; rfl
  refine (W2_sq_le_cost' hπ).trans ?_
  rw [cost, lintegral_map _ hm, tailMoment, ← lintegral_indicator (measurableSet_tail R)]
  · refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ {x : ℝ | R < |x|}
    · rw [indicator_of_mem hx]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [← sq_abs x]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_sub_clip_le hR x) 2
    · rw [indicator_of_notMem hx]
      simp only [clip_of_abs_le (not_lt.1 hx), sub_self, abs_zero]
      simp
  · exact ENNReal.measurable_ofReal.comp ((measurable_fst.sub measurable_snd).abs.pow_const 2)

/-- Two clipped laws: `W₂((χ_R)_#μ, (χ_R)_#ν)^2 ≤ (2R)^2` (product coupling). -/
lemma W2_clip_bound (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {R : ℝ} (hR : 0 ≤ R) :
    W2 (μ.map (clip R)) (ν.map (clip R)) ^ 2 ≤ ENNReal.ofReal ((2 * R) ^ 2) := by
  have hc : Measurable (clip R) := (continuous_clip R).measurable
  have hm : Measurable fun p : ℝ × ℝ => (clip R p.1, clip R p.2) :=
    (hc.comp measurable_fst).prodMk (hc.comp measurable_snd)
  have hπ : IsCoupling (μ.map (clip R)) (ν.map (clip R))
      ((μ.prod ν).map fun p => (clip R p.1, clip R p.2)) := by
    refine ⟨inferInstance, ?_, ?_⟩
    · rw [Measure.map_map measurable_fst hm]
      change Measure.map (clip R ∘ Prod.fst) (μ.prod ν) = _
      rw [← Measure.map_map hc measurable_fst, Measure.map_fst_prod, measure_univ, one_smul]
    · rw [Measure.map_map measurable_snd hm]
      change Measure.map (clip R ∘ Prod.snd) (μ.prod ν) = _
      rw [← Measure.map_map hc measurable_snd, Measure.map_snd_prod, measure_univ, one_smul]
  refine (W2_sq_le_cost' hπ).trans ?_
  rw [cost, lintegral_map (f := fun p : ℝ × ℝ => ENNReal.ofReal (|p.1 - p.2| ^ 2))
    (ENNReal.measurable_ofReal.comp ((measurable_fst.sub measurable_snd).abs.pow_const 2)) hm]
  calc ∫⁻ p, ENNReal.ofReal (|clip R p.1 - clip R p.2| ^ 2) ∂(μ.prod ν)
      ≤ ∫⁻ _, ENNReal.ofReal ((2 * R) ^ 2) ∂(μ.prod ν) := by
        refine lintegral_mono fun p => ENNReal.ofReal_le_ofReal ?_
        refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
        refine (abs_sub _ _).trans ?_
        linarith [abs_clip_le hR p.1, abs_clip_le hR p.2]
    _ = ENNReal.ofReal ((2 * R) ^ 2) := by rw [lintegral_const, measure_univ, mul_one]

lemma add3_sq_le (a b c : ℝ≥0∞) : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  rcases eq_or_ne a ⊤ with rfl | ha
  · simp
  rcases eq_or_ne b ⊤ with rfl | hb
  · simp
  rcases eq_or_ne c ⊤ with rfl | hc
  · simp
  lift a to NNReal using ha
  lift b to NNReal using hb
  lift c to NNReal using hc
  have : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
    rw [← NNReal.coe_le_coe]; push_cast
    nlinarith [sq_nonneg ((a : ℝ) - b), sq_nonneg ((b : ℝ) - c), sq_nonneg ((a : ℝ) - c)]
  exact_mod_cast this

lemma tendsto_tailMoment (σ : Measure ℝ) (hσ : HasFiniteSecondMoment σ) :
    Tendsto (tailMoment σ) atTop (𝓝 0) := by
  have heq : tailMoment σ = fun R => ∫⁻ x, {x : ℝ | R < |x|}.indicator
      (fun x => ENNReal.ofReal (x ^ 2)) x ∂σ :=
    funext fun R => (lintegral_indicator (measurableSet_tail R) _).symm
  rw [heq]
  have h := tendsto_lintegral_filter_of_dominated_convergence (l := (atTop : Filter ℝ))
    (μ := σ) (f := fun _ => 0)
    (F := fun R => {x : ℝ | R < |x|}.indicator (fun x => ENNReal.ofReal (x ^ 2)))
    (fun x => ENNReal.ofReal (x ^ 2))
    (Eventually.of_forall fun R =>
      (ENNReal.measurable_ofReal.comp (measurable_id.pow_const 2)).indicator
        (measurableSet_tail R))
    (Eventually.of_forall fun R => Eventually.of_forall fun x => indicator_le_self _ _ x)
    hσ.lintegral_lt_top.ne
    (Eventually.of_forall fun x => tendsto_const_nhds.congr'
      ((eventually_ge_atTop |x|).mono fun R hR =>
        (indicator_of_notMem (show x ∉ {x : ℝ | R < |x|} from not_lt.2 hR) _).symm))
  simpa using h

/-- `(χ_R)^2` as a bounded continuous function. -/
def clipSqBCF (R : ℝ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => clip R x ^ 2)
    ((continuous_clip R).pow 2) (R ^ 2) fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs (clip R x), ← sq_abs R]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_clip_le_abs R x) 2

/-- `ramp a b ∘ χ_R` as a bounded continuous function. -/
def rampClipBCF (R a b : ℝ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => ramp a b (clip R x))
    ((continuous_ramp a b).comp (continuous_clip R)) 1 fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (ramp_nonneg _ _ _)]; exact ramp_le_one _ _ _

/-- The countable family of test functions used for the clipped measures. -/
def testFn (R : ℝ) : ℕ → ℝ →ᵇ ℝ
  | 0 => clipSqBCF R
  | k + 1 => rampClipBCF R (Denumerable.ofNat (ℚ × ℚ) k).1 (Denumerable.ofNat (ℚ × ℚ) k).2

/-- Continuity of `W₂` at the fixed clipped limit, in finite-neighbourhood form: closeness of
finitely many test integrals forces the clipped `W₂^2` below `e`. -/
lemma W2_clip_nbhd (σ : Measure ℝ) [IsProbabilityMeasure σ] (R : ℝ)
    {e : ℝ≥0∞} (he : 0 < e) :
    ∃ m : ℕ, ∃ δ : ℝ, 0 < δ ∧ ∀ ν : Measure ℝ, IsProbabilityMeasure ν →
      (∀ k < m, dist (∫ x, testFn R k x ∂ν) (∫ x, testFn R k x ∂σ) < δ) →
      W2 (ν.map (clip R)) (σ.map (clip R)) ^ 2 < e := by
  by_contra hcon
  push Not at hcon
  have H : ∀ m : ℕ, ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
      (∀ k < m, dist (∫ x, testFn R k x ∂ν) (∫ x, testFn R k x ∂σ) < 1 / ((m : ℝ) + 1)) ∧
      e ≤ W2 (ν.map (clip R)) (σ.map (clip R)) ^ 2 :=
    fun m => hcon m (1 / ((m : ℝ) + 1)) (by positivity)
  choose ν hνp hνt hνW using H
  have hc : Measurable (clip R) := (continuous_clip R).measurable
  have inst : ∀ j, IsProbabilityMeasure ((ν j).map (clip R)) := fun j => by
    have := hνp j; infer_instance
  have hmapint : ∀ (μ : Measure ℝ) (g : ℝ → ℝ), Continuous g →
      ∫ x, g x ∂(μ.map (clip R)) = ∫ x, g (clip R x) ∂μ := fun μ g hg =>
    integral_map hc.aemeasurable hg.aestronglyMeasurable
  have htend : ∀ k, Tendsto (fun j => ∫ x, testFn R k x ∂ν j) atTop
      (𝓝 (∫ x, testFn R k x ∂σ)) := by
    intro k
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨J, hJ⟩ := exists_nat_gt (1 / ε)
    refine ⟨max (k + 1) J, fun j hj => ?_⟩
    refine (hνt j k (by omega)).trans_le ?_
    have h1 : 1 / ε < (j : ℝ) + 1 :=
      hJ.trans_le (by have : J ≤ j := le_of_max_le_right hj; exact_mod_cast (by omega : J ≤ j + 1))
    rw [div_lt_iff₀ hε] at h1
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hmj : ∀ j, HasFiniteSecondMoment ((ν j).map (clip R)) := fun j =>
    (integrable_map_measure (continuous_pow 2).aestronglyMeasurable hc.aemeasurable).2
      (by have := hνp j; exact (clipSqBCF R).integrable (ν j))
  have hm : HasFiniteSecondMoment (σ.map (clip R)) :=
    (integrable_map_measure (continuous_pow 2).aestronglyMeasurable hc.aemeasurable).2
      ((clipSqBCF R).integrable σ)
  have hramp : RampConv (fun j => (ν j).map (clip R)) (σ.map (clip R)) := by
    intro a b _
    obtain ⟨k, hk0⟩ := (Denumerable.eqv (ℚ × ℚ)).symm.surjective (a, b)
    have hk1 : Denumerable.ofNat (ℚ × ℚ) k = (a, b) := hk0
    have hk : testFn R (k + 1) = rampClipBCF R a b := by
      show rampClipBCF R (Denumerable.ofNat (ℚ × ℚ) k).1 (Denumerable.ofNat (ℚ × ℚ) k).2 = _
      rw [hk1]
    have := htend (k + 1)
    rw [hk] at this
    simp only [hmapint _ _ (continuous_ramp _ _)]
    exact this
  have hmom : Tendsto (fun j => ∫ x, x ^ 2 ∂((ν j).map (clip R))) atTop
      (𝓝 (∫ x, x ^ 2 ∂(σ.map (clip R)))) := by
    simp only [hmapint _ _ (continuous_pow 2)]
    exact htend 0
  have hW := tendsto_W2_of_rampConv_of_moment hmj hm hramp hmom
  have hW2 : Tendsto (fun j => W2 ((ν j).map (clip R)) (σ.map (clip R)) ^ 2) atTop (𝓝 0) := by
    have := ((ENNReal.continuous_pow 2).tendsto 0).comp hW
    simpa [Function.comp_def] using this
  obtain ⟨j, hj⟩ := (hW2.eventually (eventually_lt_nhds he)).exists
  exact absurd (hνW j) (not_le.2 hj)

/-- **Clause 4 (`F05:expected-transport`).** If random probability measures `σ_N` (each with
finite second moment almost surely) converge weakly in probability to a fixed `σ` with finite
second moment, and `F05:expected-tail-assumption` holds, then `E W₂(σ_N, σ)^2 → 0`. -/
theorem tendsto_expected_W2_sq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (σN : ℕ → Ω → Measure ℝ) [∀ N ω, IsProbabilityMeasure (σN N ω)]
    (_hmomN : ∀ N, ∀ᵐ ω ∂P, HasFiniteSecondMoment (σN N ω))
    (σ : Measure ℝ) [IsProbabilityMeasure σ] (hσ : HasFiniteSecondMoment σ)
    (hw : WeakConvInProb P σN σ) (htail : ExpectedTailAssumption P σN) :
    Tendsto (fun N => ∫⁻ ω, W2 (σN N ω) σ ^ 2 ∂P) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  by_cases hηtop : η = ⊤
  · exact Eventually.of_forall fun _ => hηtop ▸ le_top
  set δ := η / 12 with hδdef
  have hδ : 0 < δ := ENNReal.div_pos hη.ne' (by norm_num)
  obtain ⟨R, hR1, hR2, hR0⟩ := ((htail.eventually (eventually_le_nhds hδ)).and
    (((tendsto_tailMoment σ hσ).eventually (eventually_le_nhds hδ)).and
      (eventually_ge_atTop 0))).exists
  obtain ⟨m, δ', hδ', hnb⟩ := W2_clip_nbhd σ R hδ
  set bad : ℕ → ℕ → Set Ω := fun N k => {ω | ENNReal.ofReal δ' ≤
    edist (∫ x, testFn R k x ∂σN N ω) (∫ x, testFn R k x ∂σ)} with hbad
  set M : ℕ → Set Ω := fun N => toMeasurable P (⋃ k ∈ Finset.range m, bad N k) with hM
  have hMmeas : ∀ N, MeasurableSet (M N) := fun N => measurableSet_toMeasurable _ _
  have hPM : Tendsto (fun N => P (M N)) atTop (𝓝 0) := by
    have hsum : Tendsto (fun N => ∑ k ∈ Finset.range m, P (bad N k)) atTop (𝓝 0) := by
      rw [show (0 : ℝ≥0∞) = ∑ _k ∈ Finset.range m, 0 by simp]
      exact tendsto_finsetSum _ fun k _ => hw (testFn R k) _ (ENNReal.ofReal_pos.2 hδ')
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun N => bot_le) fun N => ?_
    simp only [hM, measure_toMeasurable]
    exact measure_biUnion_finset_le _ _
  set c := ENNReal.ofReal ((2 * R) ^ 2) with hc
  have hev : ∀ᶠ N in atTop, 3 * c * P (M N) ≤ 3 * δ := by
    have h3c : 3 * c ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
    have : Tendsto (fun N => 3 * c * P (M N)) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hPM (Or.inr h3c)
    exact this.eventually (eventually_le_nhds (ENNReal.mul_pos (by norm_num) hδ.ne'))
  filter_upwards [hev] with N hN
  have hpt : ∀ ω, W2 (σN N ω) σ ^ 2 ≤ 3 * tailMoment (σN N ω) R +
      ((3 * δ + 3 * tailMoment σ R) + 3 * c * (M N).indicator 1 ω) := by
    intro ω
    set μ := σN N ω
    have h1 := W2_clip_sq_le_tail μ hR0
    have h3 : W2 (σ.map (clip R)) σ ^ 2 ≤ tailMoment σ R := by
      rw [W2_comm]; exact W2_clip_sq_le_tail σ hR0
    have h2 : W2 (μ.map (clip R)) (σ.map (clip R)) ^ 2 ≤ δ + c * (M N).indicator 1 ω := by
      by_cases hω : ω ∈ M N
      · rw [indicator_of_mem hω, Pi.one_apply, mul_one]
        exact (W2_clip_bound μ σ hR0).trans le_add_self
      · have hnot : ω ∉ ⋃ k ∈ Finset.range m, bad N k := fun h =>
          hω (subset_toMeasurable _ _ h)
        have hgood : ∀ k < m, dist (∫ x, testFn R k x ∂μ) (∫ x, testFn R k x ∂σ) < δ' := by
          intro k hk
          by_contra hd
          push Not at hd
          refine hnot (mem_biUnion (Finset.mem_range.2 hk) ?_)
          show ENNReal.ofReal δ' ≤ edist (∫ x, testFn R k x ∂μ) (∫ x, testFn R k x ∂σ)
          rw [edist_dist]; exact ENNReal.ofReal_le_ofReal hd
        exact (hnb μ inferInstance hgood).le.trans le_self_add
    have htri : W2 μ σ ≤ W2 μ (μ.map (clip R)) + W2 (μ.map (clip R)) (σ.map (clip R)) +
        W2 (σ.map (clip R)) σ := by
      rw [add_assoc]
      exact (W2_triangle μ (μ.map (clip R)) σ).trans
        (add_le_add le_rfl (W2_triangle _ (σ.map (clip R)) σ))
    calc W2 μ σ ^ 2 ≤ (W2 μ (μ.map (clip R)) + W2 (μ.map (clip R)) (σ.map (clip R)) +
          W2 (σ.map (clip R)) σ) ^ 2 := pow_le_pow_left₀ bot_le htri 2
      _ ≤ 3 * (W2 μ (μ.map (clip R)) ^ 2 + W2 (μ.map (clip R)) (σ.map (clip R)) ^ 2 +
          W2 (σ.map (clip R)) σ ^ 2) := add3_sq_le _ _ _
      _ ≤ 3 * (tailMoment μ R + (δ + c * (M N).indicator 1 ω) + tailMoment σ R) := by
          gcongr
      _ = _ := by ring
  have hgm : Measurable fun ω => (3 * δ + 3 * tailMoment σ R) +
      3 * c * (M N).indicator (1 : Ω → ℝ≥0∞) ω :=
    measurable_const.add (measurable_const.mul (measurable_one.indicator (hMmeas N)))
  calc ∫⁻ ω, W2 (σN N ω) σ ^ 2 ∂P
      ≤ ∫⁻ ω, (3 * tailMoment (σN N ω) R +
          ((3 * δ + 3 * tailMoment σ R) + 3 * c * (M N).indicator 1 ω)) ∂P :=
        lintegral_mono hpt
    _ = 3 * ∫⁻ ω, tailMoment (σN N ω) R ∂P +
          ((3 * δ + 3 * tailMoment σ R) + 3 * c * P (M N)) := by
        rw [lintegral_add_right _ hgm, lintegral_const_mul' _ _ (by norm_num),
          lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_const_mul _ (measurable_one.indicator (hMmeas N)),
          lintegral_indicator_one (hMmeas N)]
    _ ≤ 3 * δ + ((3 * δ + 3 * δ) + 3 * δ) := by
        gcongr
        · exact (le_iSup (fun N => ∫⁻ ω, tailMoment (σN N ω) R ∂P) N).trans hR1
    _ = 12 * δ := by ring
    _ ≤ η := ENNReal.mul_div_le

end QuantumNLS.QuantileTransport
