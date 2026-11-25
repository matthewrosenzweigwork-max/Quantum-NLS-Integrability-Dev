import NlsGge.Ramer.CylindricalClosability
import NlsGge.Ramer.TruncatedFieldConvergence
import NlsGge.Ramer.DivergenceProductRule
import NlsGge.Ramer.LocalBump

/-!
# Closed divergence: uniqueness, product rule, locality

See `ClosedDivergenceProductRule.md`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter
open scoped Topology RealInnerProductSpace ENNReal

namespace NlsGge.Ramer

open NlsGge.Pilot

variable {lower upper : ℝ}

/-! ### The closed divergence -/

/-- `F : Ω → H` has closed divergence `η` for the actual source law `γ`: `η ∈ L²(γ)` and there are cylindrical `C²` fields `g k` of levels `N k` with
polynomially bounded value and derivative, `cylField (g k) → F` in `L²(γ;H)` and
`cylDiv (g k) → η` in `L²(γ)`. -/
def IsClosedDiv (c : BoundedCoefficients lower upper) (F : (ℤ → ℂ) → ActualCM c)
    (η : (ℤ → ℂ) → ℝ) : Prop :=
  MemLp η 2 (NlsGge.Measure.fullWeightSequenceGaussian c.val) ∧
  ∃ (N : ℕ → ℕ) (g : ∀ k, actualCMHead c (N k) → actualCMHead c (N k)) (C : ℕ → ℝ) (p : ℕ → ℕ),
    (∀ k, ContDiff ℝ 2 (g k)) ∧ (∀ k v, ‖g k v‖ ≤ C k * (1 + ‖v‖) ^ p k) ∧
    (∀ k v, ‖fderiv ℝ (g k) v‖ ≤ C k * (1 + ‖v‖) ^ p k) ∧
    Tendsto (fun k => eLpNorm (fun z => ‖cylField c (N k) (g k) z - F z‖) 2
      (NlsGge.Measure.fullWeightSequenceGaussian c.val)) atTop (𝓝 0) ∧
    Tendsto (fun k => eLpNorm (fun z => cylDiv c (N k) (g k) z - η z) 2
      (NlsGge.Measure.fullWeightSequenceGaussian c.val)) atTop (𝓝 0)

/-! ### Generic `L²` helpers -/

/-- `L²` dominated convergence for real-valued functions. -/
theorem tendsto_eLpNorm_two_of_dominated_ae {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (F : ℕ → α → ℝ) (hFm : ∀ N, AEStronglyMeasurable (F N) μ) (D : α → ℝ)
    (hD : Integrable (fun z => D z ^ 2) μ)
    (hbd : ∀ N, ∀ᵐ z ∂μ, ‖F N z‖ ≤ D z)
    (hlim : ∀ᵐ z ∂μ, Tendsto (fun N => F N z) atTop (𝓝 0)) :
    Tendsto (fun N => eLpNorm (F N) 2 μ) atTop (𝓝 0) := by
  have hint : ∀ N, eLpNorm (F N) 2 μ = (∫⁻ z, ‖F N z‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
    intro N
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) (hFm N)]
    simp
  have hlim2 : ∀ᵐ z ∂μ, Tendsto (fun N => ‖F N z‖ₑ ^ (2 : ℝ)) atTop
      (𝓝 ((fun _ => (0:ℝ≥0∞)) z)) := by
    filter_upwards [hlim] with z hz
    have h0 : Tendsto (fun N => ‖F N z‖ₑ) atTop (𝓝 0) := by
      have h := ENNReal.tendsto_ofReal (tendsto_norm_zero.comp hz)
      rw [ENNReal.ofReal_zero] at h
      exact h.congr (fun N => ofReal_norm _)
    have h := ((ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto 0).comp h0
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h
    exact h
  have hDfin : ∫⁻ z, ENNReal.ofReal (D z ^ 2) ∂μ ≠ ∞ := by
    have := hD.hasFiniteIntegral
    unfold HasFiniteIntegral at this
    refine ne_of_lt (lt_of_le_of_lt (lintegral_mono fun z => ?_) this)
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (sq_nonneg _)]
  have hDCT : Tendsto (fun N => ∫⁻ z, ‖F N z‖ₑ ^ (2 : ℝ) ∂μ) atTop (𝓝 0) := by
    have := tendsto_lintegral_of_dominated_convergence' (μ := μ)
      (F := fun N z => ‖F N z‖ₑ ^ (2 : ℝ)) (f := fun _ => 0)
      (fun z => ENNReal.ofReal (D z ^ 2))
      (fun N => (hFm N).enorm.pow_const _)
      (fun N => by
        filter_upwards [hbd N] with z hz
        have h1 : ‖F N z‖ₑ ≤ ENNReal.ofReal (D z) := by
          rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal hz
        have hD0 : 0 ≤ D z := (norm_nonneg _).trans hz
        calc ‖F N z‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal (D z) ^ (2 : ℝ) :=
              ENNReal.rpow_le_rpow h1 (by norm_num)
          _ = ENNReal.ofReal (D z ^ 2) := by
              rw [ENNReal.ofReal_rpow_of_nonneg hD0 (by norm_num)]
              norm_cast)
      hDfin hlim2
    simpa using this
  simp only [hint]
  have h := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0).comp hDCT
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h
  exact h

/-- Squeeze for `eLpNorm`: a pointwise bound by a function whose `eLpNorm` tends to `0`. -/
theorem tendsto_eLpNorm_zero_of_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (a b : ℕ → α → ℝ) (ha : ∀ k, AEStronglyMeasurable (a k) μ)
    (hab : ∀ k z, ‖a k z‖ ≤ ‖b k z‖)
    (hb : Tendsto (fun k => eLpNorm (b k) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (a k) 2 μ) atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb (fun _ => bot_le)
    (fun k => eLpNorm_mono (ha k) (fun z => hab k z))

/-- Sums of `L²`-null sequences are `L²`-null. -/
theorem tendsto_eLpNorm_zero_add {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (b d : ℕ → α → ℝ)
    (hb : Tendsto (fun k => eLpNorm (b k) 2 μ) atTop (𝓝 0))
    (hd : Tendsto (fun k => eLpNorm (d k) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (fun z => b k z + d k z) 2 μ) atTop (𝓝 0) := by
  have hs : Tendsto (fun k => eLpNorm (b k) 2 μ + eLpNorm (d k) 2 μ) atTop (𝓝 0) := by
    simpa using hb.add hd
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs (fun k => bot_le)
    (fun k => eLpNorm_add_le (f := b k) (g := d k) (by norm_num))

/-- Differences of `L²`-null sequences are `L²`-null. -/
theorem tendsto_eLpNorm_zero_sub {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (b d : ℕ → α → ℝ)
    (hb : Tendsto (fun k => eLpNorm (b k) 2 μ) atTop (𝓝 0))
    (hd : Tendsto (fun k => eLpNorm (d k) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (fun z => b k z - d k z) 2 μ) atTop (𝓝 0) := by
  have hs : Tendsto (fun k => eLpNorm (b k) 2 μ + eLpNorm (d k) 2 μ) atTop (𝓝 0) := by
    simpa using hb.add hd
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs (fun _ => bot_le)
    (fun k => eLpNorm_sub_le (f := b k) (g := d k) (by norm_num))

/-- A constant multiple of an `L²`-null sequence is `L²`-null. -/
theorem tendsto_eLpNorm_zero_const_mul {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (B : ℝ) (b : ℕ → α → ℝ)
    (hb : Tendsto (fun k => eLpNorm (b k) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (fun z => B * b k z) 2 μ) atTop (𝓝 0) := by
  have h := ENNReal.Tendsto.const_mul hb (Or.inr (by simp : ‖B‖ₑ ≠ ⊤))
  rw [mul_zero] at h
  refine h.congr (fun k => ?_)
  exact (eLpNorm_const_smul (μ := μ) (p := 2) B (b k)).symm

/-- Bounded a.e.-null multipliers of an `L²` function give an `L²`-null sequence. -/
theorem tendsto_eLpNorm_zero_of_bdd_mul {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (u : ℕ → α → ℝ) (hum : ∀ k, AEStronglyMeasurable (u k) μ) (M : ℝ)
    (hu : ∀ k z, |u k z| ≤ M) (hu0 : ∀ᵐ z ∂μ, Tendsto (fun k => u k z) atTop (𝓝 0))
    (w : α → ℝ) (hw : MemLp w 2 μ) :
    Tendsto (fun k => eLpNorm (fun z => u k z * w z) 2 μ) atTop (𝓝 0) := by
  refine tendsto_eLpNorm_two_of_dominated_ae (fun k z => u k z * w z)
    (fun k => (hum k).mul hw.aestronglyMeasurable) (fun z => |M| * ‖w z‖) ?_ ?_ ?_
  · have h := (hw.integrable_sq).const_mul (M ^ 2)
    refine h.congr (Eventually.of_forall fun z => ?_)
    simp only [mul_pow, sq_abs, Real.norm_eq_abs]
  · intro k
    refine Eventually.of_forall fun z => ?_
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right ((hu k z).trans (le_abs_self M)) (norm_nonneg _)
  · filter_upwards [hu0] with z hz
    simpa using hz.mul_const (w z)

/-! ### Measurability facts -/

/-- A cylindrical field with continuous profile is a.e. strongly measurable. -/
theorem aestronglyMeasurable_cylField (c : BoundedCoefficients lower upper) {N : ℕ}
    (g : actualCMHead c N → actualCMHead c N) (hg : Continuous g) :
    AEStronglyMeasurable (cylField c N g) (NlsGge.Measure.fullWeightSequenceGaussian c.val) :=
  ((continuous_subtype_val.comp hg).comp_stronglyMeasurable
    (measurable_headPt c N).stronglyMeasurable).aestronglyMeasurable

theorem aestronglyMeasurable_norm_cylField_sub (c : BoundedCoefficients lower upper) {N : ℕ}
    (g : actualCMHead c N → actualCMHead c N) (hg : Continuous g) (F : (ℤ → ℂ) → ActualCM c)
    (hF : AEStronglyMeasurable F (NlsGge.Measure.fullWeightSequenceGaussian c.val)) :
    AEStronglyMeasurable (fun z => ‖cylField c N g z - F z‖)
      (NlsGge.Measure.fullWeightSequenceGaussian c.val) :=
  ((aestronglyMeasurable_cylField c g hg).sub hF).norm

/-- If cylindrical fields with continuous profiles converge to `F` in the sense
`eLpNorm ‖cylField - F‖ → 0` then `F` is a.e. strongly measurable. -/
theorem aestronglyMeasurable_of_tendsto_cylField (c : BoundedCoefficients lower upper)
    {N : ℕ → ℕ} (g : ∀ k, actualCMHead c (N k) → actualCMHead c (N k))
    (hg : ∀ k, Continuous (g k)) (F : (ℤ → ℂ) → ActualCM c)
    (hF : Tendsto (fun k => eLpNorm (fun z => ‖cylField c (N k) (g k) z - F z‖) 2
      (NlsGge.Measure.fullWeightSequenceGaussian c.val)) atTop (𝓝 0)) :
    AEStronglyMeasurable F (NlsGge.Measure.fullWeightSequenceGaussian c.val) := by
  set γ := NlsGge.Measure.fullWeightSequenceGaussian c.val with hγ
  have hmeas : TendstoInMeasure γ (fun k z => ‖cylField c (N k) (g k) z - F z‖) atTop
      (fun _ => (0 : ℝ)) := by
    refine tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num) ?_
    refine hF.congr (fun k => ?_)
    congr 1
    funext z
    simp
  obtain ⟨ns, -, hns⟩ := hmeas.exists_seq_tendsto_ae
  refine aestronglyMeasurable_of_tendsto_ae atTop
    (fun i => aestronglyMeasurable_cylField c (g (ns i)) (hg (ns i))) ?_
  filter_upwards [hns] with z hz
  have : Tendsto (fun i => cylField c (N (ns i)) (g (ns i)) z - F z) atTop (𝓝 0) := by
    exact tendsto_zero_iff_norm_tendsto_zero.2 hz
  simpa using this.add_const (F z)

/-! ### Goal 1: uniqueness of the closed divergence -/

theorem IsClosedDiv.aestronglyMeasurable {c : BoundedCoefficients lower upper}
    {F : (ℤ → ℂ) → ActualCM c} {η : (ℤ → ℂ) → ℝ} (h : IsClosedDiv c F η) :
    AEStronglyMeasurable F (NlsGge.Measure.fullWeightSequenceGaussian c.val) := by
  obtain ⟨-, N, g, C, p, hg, -, -, hF, -⟩ := h
  exact aestronglyMeasurable_of_tendsto_cylField c g
    (fun k => (hg k).continuous) F hF

/-- **Uniqueness of the closed divergence.** -/
theorem IsClosedDiv.ae_eq {c : BoundedCoefficients lower upper}
    {F : (ℤ → ℂ) → ActualCM c} {η η' : (ℤ → ℂ) → ℝ} (h : IsClosedDiv c F η)
    (h' : IsClosedDiv c F η') :
    η =ᵐ[NlsGge.Measure.fullWeightSequenceGaussian c.val] η' := by
  set γ := NlsGge.Measure.fullWeightSequenceGaussian c.val with hγ
  have hFm := h.aestronglyMeasurable
  obtain ⟨hη, N, g, C, p, hg, hgg, hDg, hF, hδ⟩ := h
  obtain ⟨hη', N', g', C', p', hg', hgg', hDg', hF', hδ'⟩ := h'
  refine cylDiv_closure_unique c g g' (fun k => (hg k).of_le (by norm_num))
    (fun k => (hg' k).of_le (by norm_num)) C C' p p' hgg hDg hgg' hDg' η η' hη hη' ?_ hδ hδ'
  refine tendsto_eLpNorm_zero_of_le
    (fun k z => ‖cylField c (N k) (g k) z - cylField c (N' k) (g' k) z‖)
    (fun k z => ‖cylField c (N k) (g k) z - F z‖ + ‖cylField c (N' k) (g' k) z - F z‖)
    (fun k => ?_) (fun k z => ?_) (tendsto_eLpNorm_zero_add _ _ hF hF')
  · exact ((aestronglyMeasurable_cylField c (g k) (hg k).continuous).sub
      (aestronglyMeasurable_cylField c (g' k) (hg' k).continuous)).norm
  · rw [norm_norm, Real.norm_eq_abs, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    calc ‖cylField c (N k) (g k) z - cylField c (N' k) (g' k) z‖
        = ‖(cylField c (N k) (g k) z - F z) - (cylField c (N' k) (g' k) z - F z)‖ := by
          congr 1; abel
      _ ≤ _ := norm_sub_le _ _

/-! ### The product-rule class and level-`L` cutoff fields -/

/-- Data of a scalar `f : E_s → ℝ` with an `H`-gradient `gradf : E_s → H`, in the class for which
the product rule is proved: `f` is `C²`, `‖f‖ ≤ B`, `⟪∇f(x), h⟫_H = Df(x)(i h)` for all `h ∈ H`
(`i : H → E_s` the inclusion), and `‖∇f(x)‖_H ≤ B`. -/
structure ProductRuleClass (c : BoundedCoefficients lower upper) (s : ℝ) (hs0 : 0 ≤ s)
    (f : FullWeightedHilbert c s → ℝ) (gradf : FullWeightedHilbert c s → ActualCM c)
    (B : ℝ) : Prop where
  contDiff : ContDiff ℝ 2 f
  bound : ∀ x, ‖f x‖ ≤ B
  grad_bound : ∀ x, ‖gradf x‖ ≤ B
  grad_rep : ∀ (x : FullWeightedHilbert c s) (h : ActualCM c),
    ⟪gradf x, h⟫ = fderiv ℝ f x (cmToFullWeightedHilbert c s hs0 h)

/-- The head embedding `headToE` is the restriction of the inclusion `H → E_s`. -/
theorem headToE_eq_incl (c : BoundedCoefficients lower upper) (s : ℝ) (hs0 : 0 ≤ s) (N : ℕ)
    (v : actualCMHead c N) :
    headToE c s N v = cmToFullWeightedHilbert c s hs0 (v : ActualCM c) := by
  apply fullWeighted_ext
  intro n
  rw [headToE_coord, cmToFullWeightedHilbert_apply]
  rfl

section Class

variable {c : BoundedCoefficients lower upper} {s : ℝ} {hs0 : 0 ≤ s}
  {f : FullWeightedHilbert c s → ℝ} {gradf : FullWeightedHilbert c s → ActualCM c} {B : ℝ}

theorem ProductRuleClass.nonneg (hf : ProductRuleClass c s hs0 f gradf B) : 0 ≤ B :=
  (norm_nonneg _).trans (hf.bound 0)

theorem ProductRuleClass.continuous (hf : ProductRuleClass c s hs0 f gradf B) : Continuous f :=
  hf.contDiff.continuous

theorem ProductRuleClass.differentiable (hf : ProductRuleClass c s hs0 f gradf B) :
    Differentiable ℝ f := hf.contDiff.differentiable (by norm_num)

/-- The inclusion `H → E_s` has norm at most one. -/
theorem norm_cmToFullWeightedHilbert_le_self (c : BoundedCoefficients lower upper) (s : ℝ)
    (hs0 : 0 ≤ s) (x : ActualCM c) : ‖cmToFullWeightedHilbert c s hs0 x‖ ≤ ‖x‖ := by
  refine (cmToFullWeightedHilbert_norm_le c s hs0 x).trans ?_
  have : Real.sqrt (1 / 2 : ℝ) ≤ 1 := Real.sqrt_le_one.2 (by norm_num)
  nlinarith [norm_nonneg x]

/-- The gradient is continuous: `‖∇f x - ∇f y‖ ≤ ‖Df x - Df y‖`. -/
theorem ProductRuleClass.continuous_grad (hf : ProductRuleClass c s hs0 f gradf B) :
    Continuous gradf := by
  set i := cmToFullWeightedHilbert c s hs0 with hi
  have hD : Continuous (fderiv ℝ f) := hf.contDiff.continuous_fderiv (by norm_num)
  have key : ∀ x y, ‖gradf x - gradf y‖ ≤ ‖fderiv ℝ f x - fderiv ℝ f y‖ := by
    intro x y
    set u := gradf x - gradf y with hu
    have h1 : ‖u‖ * ‖u‖ = (fderiv ℝ f x - fderiv ℝ f y) (i u) := by
      have e0 : ⟪u, u⟫ = ‖u‖ * ‖u‖ := real_inner_self_eq_norm_mul_norm u
      have e : ⟪u, u⟫ = ⟪gradf x, u⟫ - ⟪gradf y, u⟫ := inner_sub_left _ _ _
      rw [← e0, e, hf.grad_rep x u, hf.grad_rep y u]
      rfl
    have h2 : ‖u‖ * ‖u‖ ≤ ‖fderiv ℝ f x - fderiv ℝ f y‖ * ‖u‖ := by
      rw [h1]
      calc (fderiv ℝ f x - fderiv ℝ f y) (i u)
          ≤ ‖(fderiv ℝ f x - fderiv ℝ f y) (i u)‖ := Real.le_norm_self _
        _ ≤ ‖fderiv ℝ f x - fderiv ℝ f y‖ * ‖i u‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖fderiv ℝ f x - fderiv ℝ f y‖ * ‖u‖ :=
            mul_le_mul_of_nonneg_left (norm_cmToFullWeightedHilbert_le_self c s hs0 u)
              (norm_nonneg _)
    rcases (norm_nonneg u).eq_or_lt with h0 | h0
    · rw [← h0]; exact norm_nonneg _
    · exact le_of_mul_le_mul_right h2 h0
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have h3 : Tendsto (fun y => ‖fderiv ℝ f y - fderiv ℝ f x‖) (𝓝 x) (𝓝 0) := by
    have := ((hD.tendsto x).sub_const (fderiv ℝ f x))
    rw [sub_self] at this
    exact tendsto_norm_zero.comp this
  refine squeeze_zero (fun y => norm_nonneg _) (fun y => ?_) h3
  exact key y x

end Class

section Level

variable {c : BoundedCoefficients lower upper} {s : ℝ} {hs0 : 0 ≤ s}
  {f : FullWeightedHilbert c s → ℝ} {gradf : FullWeightedHilbert c s → ActualCM c} {B : ℝ}

/-- The level-`L` cutoff `v ↦ f(headToE v)` has derivative `u ↦ ⟪∇f(headToE v), u⟫_H`. -/
theorem fderiv_levelScalar_apply (hf : ProductRuleClass c s hs0 f gradf B) (L : ℕ)
    (v u : actualCMHead c L) :
    fderiv ℝ (fun w : actualCMHead c L => f (headToE c s L w)) v u =
      ⟪gradf (headToE c s L v), (u : ActualCM c)⟫ := by
  have hd : HasFDerivAt (fun w : actualCMHead c L => f (headToE c s L w))
      ((fderiv ℝ f (headToE c s L v)).comp (headToE c s L)) v :=
    (hf.differentiable (headToE c s L v)).hasFDerivAt.comp v (headToE c s L).hasFDerivAt
  rw [hd.fderiv]
  change fderiv ℝ f (headToE c s L v) (headToE c s L u) = _
  rw [headToE_eq_incl c s hs0 L u, ← hf.grad_rep]

theorem norm_fderiv_levelScalar_le (hf : ProductRuleClass c s hs0 f gradf B) (L : ℕ)
    (v : actualCMHead c L) :
    ‖fderiv ℝ (fun w : actualCMHead c L => f (headToE c s L w)) v‖ ≤ B := by
  refine ContinuousLinearMap.opNorm_le_bound _ hf.nonneg (fun u => ?_)
  rw [fderiv_levelScalar_apply hf, Real.norm_eq_abs]
  refine (abs_real_inner_le_norm _ _).trans ?_
  exact mul_le_mul_of_nonneg_right (hf.grad_bound _) (norm_nonneg _)

theorem contDiff_levelScalar (hf : ProductRuleClass c s hs0 f gradf B) (L : ℕ) :
    ContDiff ℝ 2 (fun w : actualCMHead c L => f (headToE c s L w)) :=
  hf.contDiff.comp (headToE c s L).contDiff

/-- The level-`L` field `v ↦ f(headToE v) · (lift of g)(v)`. -/
def fieldMul (c : BoundedCoefficients lower upper) (s : ℝ)
    (f : FullWeightedHilbert c s → ℝ) {N L : ℕ} (h : N ≤ L)
    (g : actualCMHead c N → actualCMHead c N) : actualCMHead c L → actualCMHead c L :=
  fun v => f (headToE c s L v) • liftField c h g v

theorem contDiff_liftField (c : BoundedCoefficients lower upper) {N L : ℕ} (h : N ≤ L)
    (g : actualCMHead c N → actualCMHead c N) (hg : ContDiff ℝ 2 g) :
    ContDiff ℝ 2 (liftField c h g) :=
  (levelIncl c h).contDiff.comp (hg.comp (levelProj c N L).contDiff)

theorem contDiff_fieldMul (hf : ProductRuleClass c s hs0 f gradf B) {N L : ℕ} (h : N ≤ L)
    (g : actualCMHead c N → actualCMHead c N) (hg : ContDiff ℝ 2 g) :
    ContDiff ℝ 2 (fieldMul c s f h g) :=
  (contDiff_levelScalar hf L).smul (contDiff_liftField c h g hg)

/-- Polynomial growth of the cutoff field and its derivative. -/
theorem fieldMul_growth (hf : ProductRuleClass c s hs0 f gradf B) {N L : ℕ} (h : N ≤ L)
    (g : actualCMHead c N → actualCMHead c N) (hg : ContDiff ℝ 2 g) (C : ℝ) (p : ℕ)
    (hgg : ∀ v, ‖g v‖ ≤ C * (1 + ‖v‖) ^ p) (hDg : ∀ v, ‖fderiv ℝ g v‖ ≤ C * (1 + ‖v‖) ^ p) :
    (∀ v, ‖fieldMul c s f h g v‖ ≤ (2 * B * C) * (1 + ‖v‖) ^ p) ∧
      ∀ v, ‖fderiv ℝ (fieldMul c s f h g) v‖ ≤ (2 * B * C) * (1 + ‖v‖) ^ p := by
  have hB := hf.nonneg
  have hC : 0 ≤ C := by simpa using (norm_nonneg (g 0)).trans (hgg 0)
  obtain ⟨hGcd, hGg, hDG⟩ := liftField_growth c h g (hg.of_le (by norm_num)) C p hgg hDg
  have hG2 := contDiff_liftField c h g hg
  have hGd : Differentiable ℝ (liftField c h g) := hG2.differentiable (by norm_num)
  have hSd : Differentiable ℝ (fun w : actualCMHead c L => f (headToE c s L w)) :=
    (contDiff_levelScalar hf L).differentiable (by norm_num)
  have hpos : ∀ v : actualCMHead c L, 0 ≤ C * (1 + ‖v‖) ^ p := fun v => by positivity
  refine ⟨fun v => ?_, fun v => ?_⟩
  · calc ‖fieldMul c s f h g v‖ = |f (headToE c s L v)| * ‖liftField c h g v‖ := by
          change ‖f (headToE c s L v) • liftField c h g v‖ = _
          rw [norm_smul, Real.norm_eq_abs]
      _ ≤ B * (C * (1 + ‖v‖) ^ p) :=
          mul_le_mul (by simpa using hf.bound _) (hGg v) (norm_nonneg _) hB
      _ ≤ (2 * B * C) * (1 + ‖v‖) ^ p := by nlinarith [hpos v]
  · have hd : fderiv ℝ (fieldMul c s f h g) v =
        f (headToE c s L v) • fderiv ℝ (liftField c h g) v +
          (fderiv ℝ (fun w : actualCMHead c L => f (headToE c s L w)) v).smulRight
            (liftField c h g v) :=
      ((hSd v).hasFDerivAt.smul (hGd v).hasFDerivAt).fderiv
    rw [hd]
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun u => ?_)
    have hu0 := norm_nonneg u
    have hD1 : ‖fderiv ℝ (liftField c h g) v u‖ ≤ (C * (1 + ‖v‖) ^ p) * ‖u‖ :=
      ((fderiv ℝ (liftField c h g) v).le_opNorm u).trans
        (mul_le_mul_of_nonneg_right (hDG v) hu0)
    have hS1 : |fderiv ℝ (fun w : actualCMHead c L => f (headToE c s L w)) v u| ≤ B * ‖u‖ := by
      rw [← Real.norm_eq_abs]
      exact ((fderiv ℝ (fun w : actualCMHead c L => f (headToE c s L w)) v).le_opNorm u).trans
        (mul_le_mul_of_nonneg_right (norm_fderiv_levelScalar_le hf L v) hu0)
    have e : (f (headToE c s L v) • fderiv ℝ (liftField c h g) v +
          (fderiv ℝ (fun w : actualCMHead c L => f (headToE c s L w)) v).smulRight
            (liftField c h g v)) u =
        f (headToE c s L v) • fderiv ℝ (liftField c h g) v u +
          fderiv ℝ (fun w : actualCMHead c L => f (headToE c s L w)) v u • liftField c h g v := rfl
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    have hb1 : |f (headToE c s L v)| ≤ B := by simpa using hf.bound _
    have t1 : |f (headToE c s L v)| * ‖fderiv ℝ (liftField c h g) v u‖ ≤
        B * ((C * (1 + ‖v‖) ^ p) * ‖u‖) :=
      mul_le_mul hb1 hD1 (norm_nonneg _) hB
    have t2 : |fderiv ℝ (fun w : actualCMHead c L => f (headToE c s L w)) v u| *
        ‖liftField c h g v‖ ≤ (B * ‖u‖) * (C * (1 + ‖v‖) ^ p) :=
      mul_le_mul hS1 (hGg v) (norm_nonneg _) (by positivity)
    nlinarith [t1, t2]

theorem cylField_fieldMul (c : BoundedCoefficients lower upper) (s : ℝ)
    (f : FullWeightedHilbert c s → ℝ) {N L : ℕ} (h : N ≤ L)
    (g : actualCMHead c N → actualCMHead c N) (z : ℤ → ℂ) :
    cylField c L (fieldMul c s f h g) z =
      f (headToE c s L (headPt c L z)) • cylField c N g z := by
  rw [← cylField_lift c h g z]
  rfl

/-- **Pointwise product rule for cylindrical fields.** -/
theorem cylDiv_fieldMul (hf : ProductRuleClass c s hs0 f gradf B) {N L : ℕ} (h : N ≤ L)
    (g : actualCMHead c N → actualCMHead c N) (hg : ContDiff ℝ 2 g) (z : ℤ → ℂ) :
    cylDiv c L (fieldMul c s f h g) z =
      f (headToE c s L (headPt c L z)) * cylDiv c N g z -
        ⟪gradf (headToE c s L (headPt c L z)), cylField c N g z⟫ := by
  have hG2 := contDiff_liftField c h g hg
  have hGd : Differentiable ℝ (liftField c h g) := hG2.differentiable (by norm_num)
  have hSd : Differentiable ℝ (fun w : actualCMHead c L => f (headToE c s L w)) :=
    (contDiff_levelScalar hf L).differentiable (by norm_num)
  have key := finiteGaussianDivergence_smul (fun w : actualCMHead c L => f (headToE c s L w))
    (liftField c h g) (headPt c L z) (hSd _) (hGd _)
  change finiteGaussianDivergence (fun y => f (headToE c s L y) • liftField c h g y)
    (headPt c L z) = _
  rw [key, fderiv_levelScalar_apply hf]
  have e1 : finiteGaussianDivergence (liftField c h g) (headPt c L z) = cylDiv c N g z :=
    cylDiv_lift c h g (hg.differentiable (by norm_num)) z
  have e2 : ((liftField c h g (headPt c L z) : actualCMHead c L) : ActualCM c) =
      cylField c N g z := cylField_lift c h g z
  rw [e1, e2]

end Level

/-! ### Goal 2: the product rule -/

/-- Closed-divergence fields are in `L²(γ;H)`. -/
theorem IsClosedDiv.memLp_norm {c : BoundedCoefficients lower upper}
    {F : (ℤ → ℂ) → ActualCM c} {η : (ℤ → ℂ) → ℝ} (h : IsClosedDiv c F η) :
    MemLp (fun z => ‖F z‖) 2 (NlsGge.Measure.fullWeightSequenceGaussian c.val) := by
  set γ := NlsGge.Measure.fullWeightSequenceGaussian c.val with hγ
  have hFm := h.aestronglyMeasurable
  obtain ⟨-, N, g, C, p, hg, hgg, hDg, hF, -⟩ := h
  obtain ⟨k, hk⟩ := (hF.eventually (gt_mem_nhds (zero_lt_one' ℝ≥0∞))).exists
  have h1 : MemLp (fun z => ‖cylField c (N k) (g k) z - F z‖) 2 γ :=
    lt_of_lt_of_le hk le_top
  have h2 : MemLp (fun z => ‖cylField c (N k) (g k) z‖) 2 γ := by
    refine (memLp_two_iff_integrable_sq
      ((aestronglyMeasurable_cylField c (g k) (hg k).continuous).norm)).2 ?_
    exact (integral_sq_cylDiv_le_of_growth c (N k) (g k) (hg k) (C k) (p k) (hgg k) (hDg k)).2.1
  refine (h2.add h1).mono' hFm.norm (Eventually.of_forall fun z => ?_)
  simp only [Pi.add_apply, norm_norm]
  calc ‖F z‖ = ‖cylField c (N k) (g k) z - (cylField c (N k) (g k) z - F z)‖ := by
        congr 1; abel
    _ ≤ _ := norm_sub_le _ _

/-- Along any level sequence `L k = N k + k → ∞`, the embedded head points converge to the
realization in `E_s`, almost surely. -/
theorem ae_tendsto_headToE_level (c : BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) (N : ℕ → ℕ) :
    ∀ᵐ z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val),
      Tendsto (fun k => headToE c s (N k + k) (headPt c (N k + k) z)) atTop
        (𝓝 (NlsGge.Measure.fullWeightedSequenceRealization c s z)) := by
  filter_upwards [NlsGge.Measure.ae_fullWeightedSequenceRealization_apply c s hs] with z hz
  exact (tendsto_headToE_headPt c s z hz).comp
    (tendsto_atTop_mono (fun k => Nat.le_add_left k (N k)) tendsto_id)

/-- **Product rule for the closed divergence.** If `F` has closed divergence `η`, and `f` is in
the product-rule class (`C²`, bounded, with bounded `H`-gradient `∇f`), then `f(ξ) F` has closed
divergence `f(ξ) η - ⟨∇f(ξ), F⟩_H`, where `ξ = fullWeightedSequenceRealization c s`. -/
theorem IsClosedDiv.smul {c : BoundedCoefficients lower upper} {s : ℝ} (hs : (1 : ℝ) / 2 < s)
    {hs0 : 0 ≤ s} {f : FullWeightedHilbert c s → ℝ} {gradf : FullWeightedHilbert c s → ActualCM c}
    {B : ℝ} (hf : ProductRuleClass c s hs0 f gradf B)
    {F : (ℤ → ℂ) → ActualCM c} {η : (ℤ → ℂ) → ℝ} (h : IsClosedDiv c F η) :
    IsClosedDiv c (fun z => f (NlsGge.Measure.fullWeightedSequenceRealization c s z) • F z)
      (fun z => f (NlsGge.Measure.fullWeightedSequenceRealization c s z) * η z -
        ⟪gradf (NlsGge.Measure.fullWeightedSequenceRealization c s z), F z⟫) := by
  set γ := NlsGge.Measure.fullWeightSequenceGaussian c.val with hγ
  set R := NlsGge.Measure.fullWeightedSequenceRealization c s with hR
  have hFm := h.aestronglyMeasurable
  have hFn := h.memLp_norm
  obtain ⟨hη, N, g, C, p, hg, hgg, hDg, hF, hδ⟩ := h
  have hB := hf.nonneg
  have hRm : Measurable R := NlsGge.Measure.measurable_fullWeightedSequenceRealization c s
  have hRs : StronglyMeasurable R := hRm.stronglyMeasurable
  have hfR : AEStronglyMeasurable (fun z => f (R z)) γ :=
    (hf.continuous.comp_stronglyMeasurable hRs).aestronglyMeasurable
  have hgR : AEStronglyMeasurable (fun z => gradf (R z)) γ :=
    (hf.continuous_grad.comp_stronglyMeasurable hRs).aestronglyMeasurable
  have hηm := hη.aestronglyMeasurable
  -- the new data
  have hL : ∀ k, N k ≤ N k + k := fun k => Nat.le_add_right _ _
  set P : ∀ k : ℕ, (ℤ → ℂ) → FullWeightedHilbert c s :=
    fun k z => headToE c s (N k + k) (headPt c (N k + k) z) with hPdef
  have hPs : ∀ k, StronglyMeasurable (P k) := fun k =>
    (headToE c s (N k + k)).continuous.comp_stronglyMeasurable
      (measurable_headPt c (N k + k)).stronglyMeasurable
  have hP : ∀ᵐ z ∂γ, Tendsto (fun k => P k z) atTop (𝓝 (R z)) :=
    ae_tendsto_headToE_level c s hs N
  have hfP : ∀ k, AEStronglyMeasurable (fun z => f (P k z)) γ := fun k =>
    (hf.continuous.comp_stronglyMeasurable (hPs k)).aestronglyMeasurable
  have hgP : ∀ k, AEStronglyMeasurable (fun z => gradf (P k z)) γ := fun k =>
    (hf.continuous_grad.comp_stronglyMeasurable (hPs k)).aestronglyMeasurable
  -- the null multipliers
  have hv1m : ∀ k, AEStronglyMeasurable (fun z => ‖f (P k z) - f (R z)‖) γ := fun k =>
    ((hfP k).sub hfR).norm
  have hv2m : ∀ k, AEStronglyMeasurable (fun z => ‖gradf (P k z) - gradf (R z)‖) γ := fun k =>
    ((hgP k).sub hgR).norm
  have hv1b : ∀ k z, |‖f (P k z) - f (R z)‖| ≤ 2 * B := by
    intro k z
    rw [abs_of_nonneg (norm_nonneg _)]
    refine (norm_sub_le _ _).trans ?_
    linarith [hf.bound (P k z), hf.bound (R z)]
  have hv2b : ∀ k z, |‖gradf (P k z) - gradf (R z)‖| ≤ 2 * B := by
    intro k z
    rw [abs_of_nonneg (norm_nonneg _)]
    refine (norm_sub_le _ _).trans ?_
    linarith [hf.grad_bound (P k z), hf.grad_bound (R z)]
  have hv10 : ∀ᵐ z ∂γ, Tendsto (fun k => ‖f (P k z) - f (R z)‖) atTop (𝓝 0) := by
    filter_upwards [hP] with z hz
    have := ((hf.continuous.tendsto (R z)).comp hz).sub_const (f (R z))
    rw [sub_self] at this
    exact tendsto_norm_zero.comp this
  have hv20 : ∀ᵐ z ∂γ, Tendsto (fun k => ‖gradf (P k z) - gradf (R z)‖) atTop (𝓝 0) := by
    filter_upwards [hP] with z hz
    have := ((hf.continuous_grad.tendsto (R z)).comp hz).sub_const (gradf (R z))
    rw [sub_self] at this
    exact tendsto_norm_zero.comp this
  have hT1 := tendsto_eLpNorm_zero_of_bdd_mul _ hv1m (2 * B) hv1b hv10 _ hFn
  have hT1' := tendsto_eLpNorm_zero_of_bdd_mul _ hv1m (2 * B) hv1b hv10 _ hη
  have hT2 := tendsto_eLpNorm_zero_of_bdd_mul _ hv2m (2 * B) hv2b hv20 _ hFn
  have hFB := tendsto_eLpNorm_zero_const_mul B _ hF
  have hδB := tendsto_eLpNorm_zero_const_mul B (fun k z => cylDiv c (N k) (g k) z - η z) hδ
  -- measurability of the cylindrical pieces
  have hcyl : ∀ k, AEStronglyMeasurable (cylField c (N k) (g k)) γ := fun k =>
    aestronglyMeasurable_cylField c (g k) (hg k).continuous
  have hdiv : ∀ k, AEStronglyMeasurable (cylDiv c (N k) (g k)) γ := fun k =>
    aestronglyMeasurable_cylDiv c (g k) ((hg k).of_le (by norm_num))
  have hg'2 : ∀ k, ContDiff ℝ 2 (fieldMul c s f (hL k) (g k)) := fun k =>
    contDiff_fieldMul hf (hL k) (g k) (hg k)
  have hfield : ∀ k z, cylField c (N k + k) (fieldMul c s f (hL k) (g k)) z =
      f (P k z) • cylField c (N k) (g k) z := fun k z =>
    cylField_fieldMul c s f (hL k) (g k) z
  have hdivf : ∀ k z, cylDiv c (N k + k) (fieldMul c s f (hL k) (g k)) z =
      f (P k z) * cylDiv c (N k) (g k) z - ⟪gradf (P k z), cylField c (N k) (g k) z⟫ :=
    fun k z => cylDiv_fieldMul hf (hL k) (g k) (hg k) z
  -- new `η`
  have hη'm : AEStronglyMeasurable (fun z => f (R z) * η z - ⟪gradf (R z), F z⟫) γ :=
    (hfR.mul hηm).sub (hgR.inner hFm)
  have hη' : MemLp (fun z => f (R z) * η z - ⟪gradf (R z), F z⟫) 2 γ := by
    refine ((hη.norm.const_mul B).add (hFn.const_mul B)).mono' hη'm
      (Eventually.of_forall fun z => ?_)
    simp only [Pi.add_apply]
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hf.bound _) (norm_nonneg _)
    · rw [Real.norm_eq_abs]
      refine (abs_real_inner_le_norm _ _).trans ?_
      exact mul_le_mul_of_nonneg_right (hf.grad_bound _) (norm_nonneg _)
  have hFm' : AEStronglyMeasurable (fun z => f (R z) • F z) γ := hfR.smul hFm
  refine ⟨hη', fun k => N k + k, fun k => fieldMul c s f (hL k) (g k), fun k => 2 * B * C k, p,
    hg'2, fun k v => (fieldMul_growth hf (hL k) (g k) (hg k) (C k) (p k) (hgg k) (hDg k)).1 v,
    fun k v => (fieldMul_growth hf (hL k) (g k) (hg k) (C k) (p k) (hgg k) (hDg k)).2 v, ?_, ?_⟩
  · -- field convergence
    refine tendsto_eLpNorm_zero_of_le _
      (fun k z => B * ‖cylField c (N k) (g k) z - F z‖ +
        ‖f (P k z) - f (R z)‖ * ‖F z‖) (fun k => ?_) (fun k z => ?_)
      (tendsto_eLpNorm_zero_add _ _ hFB hT1)
    · exact ((aestronglyMeasurable_cylField c _ (hg'2 k).continuous).sub hFm').norm
    · simp only [hfield, norm_norm]
      have hnn : 0 ≤ B * ‖cylField c (N k) (g k) z - F z‖ + ‖f (P k z) - f (R z)‖ * ‖F z‖ := by
        positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      have e : f (P k z) • cylField c (N k) (g k) z - f (R z) • F z =
          f (P k z) • (cylField c (N k) (g k) z - F z) + (f (P k z) - f (R z)) • F z := by
        rw [smul_sub, sub_smul]; abel
      change ‖f (P k z) • cylField c (N k) (g k) z - f (R z) • F z‖ ≤ _
      rw [e]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_smul, Real.norm_eq_abs]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        simpa using hf.bound _
      · rw [norm_smul, Real.norm_eq_abs]
  · -- divergence convergence
    have hTeq : ∀ k z, cylDiv c (N k + k) (fieldMul c s f (hL k) (g k)) z -
        (f (R z) * η z - ⟪gradf (R z), F z⟫) =
        ((f (P k z) * (cylDiv c (N k) (g k) z - η z) + (f (P k z) - f (R z)) * η z) -
          ⟪gradf (P k z), cylField c (N k) (g k) z - F z⟫) -
          ⟪gradf (P k z) - gradf (R z), F z⟫ := by
      intro k z
      have i1 : ⟪gradf (P k z), cylField c (N k) (g k) z - F z⟫ =
          ⟪gradf (P k z), cylField c (N k) (g k) z⟫ - ⟪gradf (P k z), F z⟫ :=
        inner_sub_right _ _ _
      have i2 : ⟪gradf (P k z) - gradf (R z), F z⟫ =
          ⟪gradf (P k z), F z⟫ - ⟪gradf (R z), F z⟫ := inner_sub_left _ _ _
      rw [hdivf k z, i1, i2]
      ring
    have hfun : (fun k => eLpNorm (fun z => cylDiv c (N k + k) (fieldMul c s f (hL k) (g k)) z -
        (f (R z) * η z - ⟪gradf (R z), F z⟫)) 2 γ) = fun k => eLpNorm (fun z =>
        ((f (P k z) * (cylDiv c (N k) (g k) z - η z) + (f (P k z) - f (R z)) * η z) -
          ⟪gradf (P k z), cylField c (N k) (g k) z - F z⟫) -
          ⟪gradf (P k z) - gradf (R z), F z⟫) 2 γ := by
      funext k
      congr 1
      funext z
      exact hTeq k z
    show Tendsto (fun k => eLpNorm (fun z => cylDiv c (N k + k)
      (fieldMul c s f (hL k) (g k)) z -
        (f (R z) * η z - ⟪gradf (R z), F z⟫)) 2 γ) atTop (𝓝 0)
    rw [hfun]
    refine tendsto_eLpNorm_zero_sub _ _ (tendsto_eLpNorm_zero_sub _ _
      (tendsto_eLpNorm_zero_add _ _ ?_ ?_) ?_) ?_
    · -- t1
      refine tendsto_eLpNorm_zero_of_le _ (fun k z => B * (cylDiv c (N k) (g k) z - η z))
        (fun k => ((hfP k).mul ((hdiv k).sub hηm))) (fun k z => ?_) hδB
      rw [norm_mul, norm_mul]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      rw [Real.norm_eq_abs]
      exact (hf.bound _).trans (le_abs_self B) |>.trans_eq (by rw [Real.norm_eq_abs])
    · -- t2
      refine tendsto_eLpNorm_zero_of_le _ (fun k z => ‖f (P k z) - f (R z)‖ * η z)
        (fun k => ((hfP k).sub hfR).mul hηm) (fun k z => ?_) hT1'
      rw [norm_mul, norm_mul, norm_norm]
    · -- t3
      refine tendsto_eLpNorm_zero_of_le _ (fun k z => B * ‖cylField c (N k) (g k) z - F z‖)
        (fun k => (hgP k).inner ((hcyl k).sub hFm)) (fun k z => ?_) hFB
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hB (norm_nonneg _))]
      refine (abs_real_inner_le_norm _ _).trans ?_
      exact mul_le_mul_of_nonneg_right (hf.grad_bound _) (norm_nonneg _)
    · -- t4
      refine tendsto_eLpNorm_zero_of_le _ (fun k z => ‖gradf (P k z) - gradf (R z)‖ * ‖F z‖)
        (fun k => ((hgP k).sub hgR).inner hFm) (fun k z => ?_) hT2
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
      exact abs_real_inner_le_norm _ _

/-! ### Goal 3: locality / bump independence -/

/-- If `ρ = 1` on an open set `U`, the `H`-gradient of `ρ` vanishes on `U`. -/
theorem ProductRuleClass.grad_eq_zero_of_eqOn_one {c : BoundedCoefficients lower upper}
    {s : ℝ} {hs0 : 0 ≤ s} {ρ : FullWeightedHilbert c s → ℝ}
    {gradρ : FullWeightedHilbert c s → ActualCM c} {B : ℝ}
    (hρ : ProductRuleClass c s hs0 ρ gradρ B) {U : Set (FullWeightedHilbert c s)}
    (hU : IsOpen U) (hρ1 : ∀ x ∈ U, ρ x = 1) {x : FullWeightedHilbert c s} (hx : x ∈ U) :
    gradρ x = 0 := by
  have hev : ρ =ᶠ[𝓝 x] fun _ => (1 : ℝ) :=
    Filter.eventuallyEq_of_mem (hU.mem_nhds hx) (fun y hy => hρ1 y hy)
  have hD : fderiv ℝ ρ x = 0 := by
    rw [hev.fderiv_eq, fderiv_fun_const]; rfl
  have h0 : ⟪gradρ x, gradρ x⟫ = 0 := by
    rw [hρ.grad_rep x, hD]; rfl
  exact inner_self_eq_zero.1 h0

/-- **Locality / independence of the bump.** Let `G, G' : E_s → H` with `G ∘ ξ` and `G' ∘ ξ` having
closed divergences `η`, `η'`. If `ρ` is in the product-rule class, `ρ = 1` on an open set `U`,
and `ρ G = ρ G'` everywhere, then `η = η'` almost surely on `{ξ ∈ U}`. -/
theorem IsClosedDiv.local_eq {c : BoundedCoefficients lower upper} {s : ℝ}
    (hs : (1 : ℝ) / 2 < s) {hs0 : 0 ≤ s} {ρ : FullWeightedHilbert c s → ℝ}
    {gradρ : FullWeightedHilbert c s → ActualCM c} {B : ℝ}
    (hρ : ProductRuleClass c s hs0 ρ gradρ B) {U : Set (FullWeightedHilbert c s)}
    (hU : IsOpen U) (hρ1 : ∀ x ∈ U, ρ x = 1) {G G' : FullWeightedHilbert c s → ActualCM c}
    (hGG : ∀ x, ρ x • G x = ρ x • G' x) {η η' : (ℤ → ℂ) → ℝ}
    (h : IsClosedDiv c (fun z => G (NlsGge.Measure.fullWeightedSequenceRealization c s z)) η)
    (h' : IsClosedDiv c (fun z => G' (NlsGge.Measure.fullWeightedSequenceRealization c s z)) η') :
    ∀ᵐ z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val),
      NlsGge.Measure.fullWeightedSequenceRealization c s z ∈ U → η z = η' z := by
  set R := NlsGge.Measure.fullWeightedSequenceRealization c s with hR
  have h1 := h.smul hs hρ
  have h2 := h'.smul hs hρ
  have e : (fun z => ρ (R z) • G' (R z)) = (fun z => ρ (R z) • G (R z)) :=
    funext (fun z => (hGG _).symm)
  have h2' : IsClosedDiv c (fun z => ρ (R z) • G (R z))
      (fun z => ρ (R z) * η' z - ⟪gradρ (R z), G' (R z)⟫) := by
    have := h2
    rwa [e] at this
  filter_upwards [h1.ae_eq h2'] with z hz hzU
  have h1z := hρ1 _ hzU
  have h0 := hρ.grad_eq_zero_of_eqOn_one hU hρ1 hzU
  have hz' : ρ (R z) * η z - ⟪gradρ (R z), G (R z)⟫ =
      ρ (R z) * η' z - ⟪gradρ (R z), G' (R z)⟫ := hz
  have i1 : ⟪gradρ (R z), G (R z)⟫ = 0 := by rw [h0]; exact inner_zero_left _
  have i2 : ⟪gradρ (R z), G' (R z)⟫ = 0 := by rw [h0]; exact inner_zero_left _
  rw [i1, i2, h1z] at hz'
  linarith

/-! ### Satisfiability of the class -/

/-- The Riesz vector: `⟪∇f x, h⟫ = Df(x)(i h)`. -/
theorem exists_riesz_grad (c : BoundedCoefficients lower upper) (s : ℝ) (hs0 : 0 ≤ s)
    (f : FullWeightedHilbert c s → ℝ) (B : ℝ) (x : FullWeightedHilbert c s)
    (hB : ‖fderiv ℝ f x‖ ≤ B) :
    ∃ v : ActualCM c, (∀ h : ActualCM c, ⟪v, h⟫ = fderiv ℝ f x (cmToFullWeightedHilbert c s hs0 h)) ∧
      ‖v‖ ≤ B := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans hB
  refine ⟨(InnerProductSpace.toDual ℝ (ActualCM c)).symm
    (LinearMap.mkContinuous
      { toFun := fun h => fderiv ℝ f x (cmToFullWeightedHilbert c s hs0 h)
        map_add' := fun a b => by
          rw [map_add, map_add]
        map_smul' := fun r a => by
          rw [map_smul, map_smul]; rfl } B (fun h => ?_)), fun h => ?_, ?_⟩
  · change ‖fderiv ℝ f x (cmToFullWeightedHilbert c s hs0 h)‖ ≤ B * ‖h‖
    calc ‖fderiv ℝ f x (cmToFullWeightedHilbert c s hs0 h)‖
          ≤ ‖fderiv ℝ f x‖ * ‖cmToFullWeightedHilbert c s hs0 h‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ B * ‖h‖ :=
            mul_le_mul hB (norm_cmToFullWeightedHilbert_le_self c s hs0 h) (norm_nonneg _) hB0
  · rw [InnerProductSpace.toDual_symm_apply]
    rfl
  · rw [LinearIsometryEquiv.norm_map]
    exact LinearMap.mkContinuous_norm_le _ hB0 _

/-- **Satisfiability of the product-rule class.** Every `C²` function `f` on `E_s` with `|f| ≤ B`
and `‖Df‖ ≤ B` has an `H`-gradient, hence lies in `ProductRuleClass`. -/
theorem exists_productRuleClass (c : BoundedCoefficients lower upper) (s : ℝ) (hs0 : 0 ≤ s)
    (f : FullWeightedHilbert c s → ℝ) (hf : ContDiff ℝ 2 f) (B : ℝ) (hfb : ∀ x, ‖f x‖ ≤ B)
    (hDb : ∀ x, ‖fderiv ℝ f x‖ ≤ B) :
    ∃ gradf : FullWeightedHilbert c s → ActualCM c, ProductRuleClass c s hs0 f gradf B := by
  choose v hv1 hv2 using fun x => exists_riesz_grad c s hs0 f B x (hDb x)
  exact ⟨v, hf, hfb, hv2, fun x h => hv1 x h⟩

/-- **Existence of bumps in the class.** For every `x₀ ∈ E_s` there are `r > 0` and a function
`ρ` in the product-rule class with `ρ = 1` on the open ball `B(x₀, r)` (from `LocalBump`). -/
theorem exists_bump_productRuleClass (c : BoundedCoefficients lower upper) (s : ℝ) (hs0 : 0 ≤ s)
    (x₀ : FullWeightedHilbert c s) :
    ∃ r > 0, ∃ (ρ : FullWeightedHilbert c s → ℝ) (gradρ : FullWeightedHilbert c s → ActualCM c) (B : ℝ),
      ProductRuleClass c s hs0 ρ gradρ B ∧ ∀ x ∈ Metric.ball x₀ r, ρ x = 1 := by
  obtain ⟨r, hr, G, B, hG, hGb, hDGb, hEq⟩ := exists_bumped_field_generic
    (fun _ : FullWeightedHilbert c s => (1 : ℝ)) contDiff_const x₀
  obtain ⟨gradρ, hρ⟩ := exists_productRuleClass c s hs0 G hG B hGb hDGb
  exact ⟨r, hr, G, gradρ, B, hρ, fun x hx => hEq hx⟩

end NlsGge.Ramer
