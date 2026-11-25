import NlsGge.Ramer.General.ClosedDivergenceProductRuleGa
import NlsGge.Ramer.General.LocalBumpG

/-!
# Closed divergence: product rule and locality (GB6, part b)

Generalization of the second part of `NlsGge/Ramer/ClosedDivergenceProductRule.lean`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter
open scoped Topology RealInnerProductSpace ENNReal

namespace NlsGge.Ramer.General.RamerSetting

open NlsGge.Pilot NlsGge.Ramer NlsGge.Ramer.Gen

variable (S : NlsGge.Ramer.General.RamerSetting)

/-! ### The product-rule class and level-`L` cutoff fields -/

/-- Data of a scalar `f : E_s → ℝ` with an `H`-gradient `gradf : E_s → H`, in the class for which
the product rule is proved: `f` is `C²`, `‖f‖ ≤ B`, `⟪∇f(x), h⟫_H = Df(x)(i h)` for all `h ∈ H`
(`i : H → E_s` the inclusion), and `‖∇f(x)‖_H ≤ B`. -/
structure ProductRuleClass 
    (f : S.E → ℝ) (gradf : S.E → S.H)
    (B : ℝ) : Prop where
  contDiff : ContDiff ℝ 2 f
  bound : ∀ x, ‖f x‖ ≤ B
  grad_bound : ∀ x, ‖gradf x‖ ≤ B
  grad_rep : ∀ (x : S.E) (h : S.H),
    ⟪gradf x, h⟫ = fderiv ℝ f x (S.incl h)

/-- The head embedding `headToE` is the restriction of the inclusion `H → E_s`. -/
theorem headToE_eq_incl (N : ℕ)
    (v : S.head N) :
    S.headToE N v = S.incl (v : S.H) := by
  rfl

section Class

variable {S}
  {f : S.E → ℝ} {gradf : S.E → S.H} {B : ℝ}

theorem ProductRuleClass.nonneg (hf : S.ProductRuleClass f gradf B) : 0 ≤ B :=
  (norm_nonneg _).trans (hf.bound 0)

theorem ProductRuleClass.continuous (hf : S.ProductRuleClass f gradf B) : Continuous f :=
  hf.contDiff.continuous

theorem ProductRuleClass.differentiable (hf : S.ProductRuleClass f gradf B) :
    Differentiable ℝ f := hf.contDiff.differentiable (by norm_num)

/-- The gradient is continuous: `‖∇f x - ∇f y‖ ≤ √ratioSup ‖Df x - Df y‖`
(the inclusion `H → E` has norm at most `√ratioSup`). -/
theorem ProductRuleClass.continuous_grad (hf : S.ProductRuleClass f gradf B) :
    Continuous gradf := by
  set i := S.incl with hi
  have hD : Continuous (fderiv ℝ f) := hf.contDiff.continuous_fderiv (by norm_num)
  have key : ∀ x y, ‖gradf x - gradf y‖ ≤ Real.sqrt S.ratioSup * ‖fderiv ℝ f x - fderiv ℝ f y‖ := by
    intro x y
    set u := gradf x - gradf y with hu
    have h1 : ‖u‖ * ‖u‖ = (fderiv ℝ f x - fderiv ℝ f y) (i u) := by
      have e0 : ⟪u, u⟫ = ‖u‖ * ‖u‖ := real_inner_self_eq_norm_mul_norm u
      have e : ⟪u, u⟫ = ⟪gradf x, u⟫ - ⟪gradf y, u⟫ := inner_sub_left _ _ _
      rw [← e0, e, hf.grad_rep x u, hf.grad_rep y u]
      rfl
    have h2 : ‖u‖ * ‖u‖ ≤ (Real.sqrt S.ratioSup * ‖fderiv ℝ f x - fderiv ℝ f y‖) * ‖u‖ := by
      rw [h1]
      calc (fderiv ℝ f x - fderiv ℝ f y) (i u)
          ≤ ‖(fderiv ℝ f x - fderiv ℝ f y) (i u)‖ := Real.le_norm_self _
        _ ≤ ‖fderiv ℝ f x - fderiv ℝ f y‖ * ‖i u‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖fderiv ℝ f x - fderiv ℝ f y‖ * (Real.sqrt S.ratioSup * ‖u‖) :=
            mul_le_mul_of_nonneg_left (S.incl_norm_le u) (norm_nonneg _)
        _ = (Real.sqrt S.ratioSup * ‖fderiv ℝ f x - fderiv ℝ f y‖) * ‖u‖ := by ring
    rcases (norm_nonneg u).eq_or_lt with h0 | h0
    · rw [← h0]; exact mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
    · exact le_of_mul_le_mul_right h2 h0
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have h3 : Tendsto (fun y => ‖fderiv ℝ f y - fderiv ℝ f x‖) (𝓝 x) (𝓝 0) := by
    have := ((hD.tendsto x).sub_const (fderiv ℝ f x))
    rw [sub_self] at this
    exact tendsto_norm_zero.comp this
  have h3' := h3.const_mul (Real.sqrt S.ratioSup)
  rw [mul_zero] at h3'
  exact squeeze_zero (fun y => norm_nonneg _) (fun y => key y x) h3'

end Class

section Level

variable {S}
  {f : S.E → ℝ} {gradf : S.E → S.H} {B : ℝ}

/-- The level-`L` cutoff `v ↦ f(headToE v)` has derivative `u ↦ ⟪∇f(headToE v), u⟫_H`. -/
theorem fderiv_levelScalar_apply (hf : S.ProductRuleClass f gradf B) (L : ℕ)
    (v u : S.head L) :
    fderiv ℝ (fun w : S.head L => f (S.headToE L w)) v u =
      ⟪gradf (S.headToE L v), (u : S.H)⟫ := by
  have hd : HasFDerivAt (fun w : S.head L => f (S.headToE L w))
      ((fderiv ℝ f (S.headToE L v)).comp (S.headToE L)) v :=
    (hf.differentiable (S.headToE L v)).hasFDerivAt.comp v (S.headToE L).hasFDerivAt
  rw [hd.fderiv]
  change fderiv ℝ f (S.headToE L v) (S.headToE L u) = _
  exact (hf.grad_rep _ _).symm

theorem norm_fderiv_levelScalar_le (hf : S.ProductRuleClass f gradf B) (L : ℕ)
    (v : S.head L) :
    ‖fderiv ℝ (fun w : S.head L => f (S.headToE L w)) v‖ ≤ B := by
  refine ContinuousLinearMap.opNorm_le_bound _ hf.nonneg (fun u => ?_)
  rw [fderiv_levelScalar_apply hf, Real.norm_eq_abs]
  refine (abs_real_inner_le_norm _ _).trans ?_
  exact mul_le_mul_of_nonneg_right (hf.grad_bound _) (norm_nonneg _)

theorem contDiff_levelScalar (hf : S.ProductRuleClass f gradf B) (L : ℕ) :
    ContDiff ℝ 2 (fun w : S.head L => f (S.headToE L w)) :=
  hf.contDiff.comp (S.headToE L).contDiff

variable (S) in
/-- The level-`L` field `v ↦ f(headToE v) · (lift of g)(v)`. -/
def fieldMul (f : S.E → ℝ) {N L : ℕ} (h : N ≤ L)
    (g : S.head N → S.head N) : S.head L → S.head L :=
  fun v => f (S.headToE L v) • S.liftField h g v

variable (S) in
theorem contDiff_liftField {N L : ℕ} (h : N ≤ L)
    (g : S.head N → S.head N) (hg : ContDiff ℝ 2 g) :
    ContDiff ℝ 2 (S.liftField h g) :=
  (S.levelIncl h).contDiff.comp (hg.comp (S.levelProj N L).contDiff)

theorem contDiff_fieldMul (hf : S.ProductRuleClass f gradf B) {N L : ℕ} (h : N ≤ L)
    (g : S.head N → S.head N) (hg : ContDiff ℝ 2 g) :
    ContDiff ℝ 2 (S.fieldMul f h g) :=
  (contDiff_levelScalar hf L).smul (contDiff_liftField S h g hg)

/-- Polynomial growth of the cutoff field and its derivative. -/
theorem fieldMul_growth (hf : S.ProductRuleClass f gradf B) {N L : ℕ} (h : N ≤ L)
    (g : S.head N → S.head N) (hg : ContDiff ℝ 2 g) (C : ℝ) (p : ℕ)
    (hgg : ∀ v, ‖g v‖ ≤ C * (1 + ‖v‖) ^ p) (hDg : ∀ v, ‖fderiv ℝ g v‖ ≤ C * (1 + ‖v‖) ^ p) :
    (∀ v, ‖S.fieldMul f h g v‖ ≤ (2 * B * C) * (1 + ‖v‖) ^ p) ∧
      ∀ v, ‖fderiv ℝ (S.fieldMul f h g) v‖ ≤ (2 * B * C) * (1 + ‖v‖) ^ p := by
  have hB := hf.nonneg
  have hC : 0 ≤ C := by simpa using (norm_nonneg (g 0)).trans (hgg 0)
  obtain ⟨hGcd, hGg, hDG⟩ := S.liftField_growth h g (hg.of_le (by norm_num)) C p hgg hDg
  have hG2 := contDiff_liftField S h g hg
  have hGd : Differentiable ℝ (S.liftField h g) := hG2.differentiable (by norm_num)
  have hSd : Differentiable ℝ (fun w : S.head L => f (S.headToE L w)) :=
    (contDiff_levelScalar hf L).differentiable (by norm_num)
  have hpos : ∀ v : S.head L, 0 ≤ C * (1 + ‖v‖) ^ p := fun v => by positivity
  refine ⟨fun v => ?_, fun v => ?_⟩
  · calc ‖S.fieldMul f h g v‖ = |f (S.headToE L v)| * ‖S.liftField h g v‖ := by
          change ‖f (S.headToE L v) • S.liftField h g v‖ = _
          rw [norm_smul, Real.norm_eq_abs]
      _ ≤ B * (C * (1 + ‖v‖) ^ p) :=
          mul_le_mul (by simpa using hf.bound _) (hGg v) (norm_nonneg _) hB
      _ ≤ (2 * B * C) * (1 + ‖v‖) ^ p := by nlinarith [hpos v]
  · have hd : fderiv ℝ (S.fieldMul f h g) v =
        f (S.headToE L v) • fderiv ℝ (S.liftField h g) v +
          (fderiv ℝ (fun w : S.head L => f (S.headToE L w)) v).smulRight
            (S.liftField h g v) :=
      ((hSd v).hasFDerivAt.smul (hGd v).hasFDerivAt).fderiv
    rw [hd]
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun u => ?_)
    have hu0 := norm_nonneg u
    have hD1 : ‖fderiv ℝ (S.liftField h g) v u‖ ≤ (C * (1 + ‖v‖) ^ p) * ‖u‖ :=
      ((fderiv ℝ (S.liftField h g) v).le_opNorm u).trans
        (mul_le_mul_of_nonneg_right (hDG v) hu0)
    have hS1 : |fderiv ℝ (fun w : S.head L => f (S.headToE L w)) v u| ≤ B * ‖u‖ := by
      rw [← Real.norm_eq_abs]
      exact ((fderiv ℝ (fun w : S.head L => f (S.headToE L w)) v).le_opNorm u).trans
        (mul_le_mul_of_nonneg_right (norm_fderiv_levelScalar_le hf L v) hu0)
    have e : (f (S.headToE L v) • fderiv ℝ (S.liftField h g) v +
          (fderiv ℝ (fun w : S.head L => f (S.headToE L w)) v).smulRight
            (S.liftField h g v)) u =
        f (S.headToE L v) • fderiv ℝ (S.liftField h g) v u +
          fderiv ℝ (fun w : S.head L => f (S.headToE L w)) v u • S.liftField h g v := rfl
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    have hb1 : |f (S.headToE L v)| ≤ B := by simpa using hf.bound _
    have t1 : |f (S.headToE L v)| * ‖fderiv ℝ (S.liftField h g) v u‖ ≤
        B * ((C * (1 + ‖v‖) ^ p) * ‖u‖) :=
      mul_le_mul hb1 hD1 (norm_nonneg _) hB
    have t2 : |fderiv ℝ (fun w : S.head L => f (S.headToE L w)) v u| *
        ‖S.liftField h g v‖ ≤ (B * ‖u‖) * (C * (1 + ‖v‖) ^ p) :=
      mul_le_mul hS1 (hGg v) (norm_nonneg _) (by positivity)
    nlinarith [t1, t2]

variable (S) in
theorem cylField_fieldMul (f : S.E → ℝ) {N L : ℕ} (h : N ≤ L)
    (g : S.head N → S.head N) (z : ℤ → ℂ) :
    S.cylField L (S.fieldMul f h g) z =
      f (S.headToE L (S.headPt L z)) • S.cylField N g z := by
  rw [← S.cylField_lift h g z]
  rfl

/-- **Pointwise product rule for cylindrical fields.** -/
theorem cylDiv_fieldMul (hf : S.ProductRuleClass f gradf B) {N L : ℕ} (h : N ≤ L)
    (g : S.head N → S.head N) (hg : ContDiff ℝ 2 g) (z : ℤ → ℂ) :
    S.cylDiv L (S.fieldMul f h g) z =
      f (S.headToE L (S.headPt L z)) * S.cylDiv N g z -
        ⟪gradf (S.headToE L (S.headPt L z)), S.cylField N g z⟫ := by
  have hG2 := contDiff_liftField S h g hg
  have hGd : Differentiable ℝ (S.liftField h g) := hG2.differentiable (by norm_num)
  have hSd : Differentiable ℝ (fun w : S.head L => f (S.headToE L w)) :=
    (contDiff_levelScalar hf L).differentiable (by norm_num)
  have key := finiteGaussianDivergence_smul (fun w : S.head L => f (S.headToE L w))
    (S.liftField h g) (S.headPt L z) (hSd _) (hGd _)
  change finiteGaussianDivergence (fun y => f (S.headToE L y) • S.liftField h g y)
    (S.headPt L z) = _
  rw [key, fderiv_levelScalar_apply hf]
  have e1 : finiteGaussianDivergence (S.liftField h g) (S.headPt L z) = S.cylDiv N g z :=
    S.cylDiv_lift h g (hg.differentiable (by norm_num)) z
  have e2 : ((S.liftField h g (S.headPt L z) : S.head L) : S.H) =
      S.cylField N g z := S.cylField_lift h g z
  rw [e1, e2]

end Level

/-! ### Goal 2: the product rule -/

variable {S} in
/-- Closed-divergence fields are in `L²(γ;H)`. -/
theorem IsClosedDiv.memLp_norm 
    {F : (ℤ → ℂ) → S.H} {η : (ℤ → ℂ) → ℝ} (h : S.IsClosedDiv F η) :
    MemLp (fun z => ‖F z‖) 2 S.γ := by
  set γ := S.γ with hγ
  have hFm := h.aestronglyMeasurable
  obtain ⟨-, N, g, C, p, hg, hgg, hDg, hF, -⟩ := h
  obtain ⟨k, hk⟩ := (hF.eventually (gt_mem_nhds (zero_lt_one' ℝ≥0∞))).exists
  have h1 : MemLp (fun z => ‖S.cylField (N k) (g k) z - F z‖) 2 γ :=
    lt_of_lt_of_le hk le_top
  have h2 : MemLp (fun z => ‖S.cylField (N k) (g k) z‖) 2 γ := by
    refine (memLp_two_iff_integrable_sq
      ((S.aestronglyMeasurable_cylField (g k) (hg k).continuous).norm)).2 ?_
    exact (S.integral_sq_cylDiv_le_of_growth (N k) (g k) (hg k) (C k) (p k) (hgg k) (hDg k)).2.1
  refine (h2.add h1).mono' hFm.norm (Eventually.of_forall fun z => ?_)
  simp only [Pi.add_apply, norm_norm]
  calc ‖F z‖ = ‖S.cylField (N k) (g k) z - (S.cylField (N k) (g k) z - F z)‖ := by
        congr 1; abel
    _ ≤ _ := norm_sub_le _ _

/-- Along any level sequence `L k = N k + k → ∞`, the embedded head points converge to the
realization in `E_s`, almost surely. -/
theorem ae_tendsto_headToE_level (N : ℕ → ℕ) :
    ∀ᵐ z ∂S.γ,
      Tendsto (fun k => S.headToE (N k + k) (S.headPt (N k + k) z)) atTop
        (𝓝 (S.R z)) := by
  filter_upwards [S.coord_R_ae] with z hz
  exact (S.tendsto_headToE_headPt z hz).comp
    (tendsto_atTop_mono (fun k => Nat.le_add_left k (N k)) tendsto_id)

variable {S} in
/-- **Product rule for the closed divergence.** If `F` has closed divergence `η`, and `f` is in
the product-rule class (`C²`, bounded, with bounded `H`-gradient `∇f`), then `f(ξ) F` has closed
divergence `f(ξ) η - ⟨∇f(ξ), F⟩_H`, where `ξ = fullWeightedSequenceRealization c s`. -/
theorem IsClosedDiv.smul {f : S.E → ℝ} {gradf : S.E → S.H}
    {B : ℝ} (hf : S.ProductRuleClass f gradf B)
    {F : (ℤ → ℂ) → S.H} {η : (ℤ → ℂ) → ℝ} (h : S.IsClosedDiv F η) :
    S.IsClosedDiv (fun z => f (S.R z) • F z)
      (fun z => f (S.R z) * η z -
        ⟪gradf (S.R z), F z⟫) := by
  set γ := S.γ with hγ
  set R := S.R with hR
  have hFm := h.aestronglyMeasurable
  have hFn := h.memLp_norm
  obtain ⟨hη, N, g, C, p, hg, hgg, hDg, hF, hδ⟩ := h
  have hB := hf.nonneg
  have hRm : Measurable R := S.measurable_R
  have hRs : StronglyMeasurable R := hRm.stronglyMeasurable
  have hfR : AEStronglyMeasurable (fun z => f (R z)) γ :=
    (hf.continuous.comp_stronglyMeasurable hRs).aestronglyMeasurable
  have hgR : AEStronglyMeasurable (fun z => gradf (R z)) γ :=
    (hf.continuous_grad.comp_stronglyMeasurable hRs).aestronglyMeasurable
  have hηm := hη.aestronglyMeasurable
  -- the new data
  have hL : ∀ k, N k ≤ N k + k := fun k => Nat.le_add_right _ _
  set P : ∀ k : ℕ, (ℤ → ℂ) → S.E :=
    fun k z => S.headToE (N k + k) (S.headPt (N k + k) z) with hPdef
  have hPs : ∀ k, StronglyMeasurable (P k) := fun k =>
    (S.headToE (N k + k)).continuous.comp_stronglyMeasurable
      (S.measurable_headPt (N k + k)).stronglyMeasurable
  have hP : ∀ᵐ z ∂γ, Tendsto (fun k => P k z) atTop (𝓝 (R z)) :=
    S.ae_tendsto_headToE_level N
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
  have hδB := tendsto_eLpNorm_zero_const_mul B (fun k z => S.cylDiv (N k) (g k) z - η z) hδ
  -- measurability of the cylindrical pieces
  have hcyl : ∀ k, AEStronglyMeasurable (S.cylField (N k) (g k)) γ := fun k =>
    S.aestronglyMeasurable_cylField (g k) (hg k).continuous
  have hdiv : ∀ k, AEStronglyMeasurable (S.cylDiv (N k) (g k)) γ := fun k =>
    S.aestronglyMeasurable_cylDiv (g k) ((hg k).of_le (by norm_num))
  have hg'2 : ∀ k, ContDiff ℝ 2 (S.fieldMul f (hL k) (g k)) := fun k =>
    contDiff_fieldMul hf (hL k) (g k) (hg k)
  have hfield : ∀ k z, S.cylField (N k + k) (S.fieldMul f (hL k) (g k)) z =
      f (P k z) • S.cylField (N k) (g k) z := fun k z =>
    cylField_fieldMul S f (hL k) (g k) z
  have hdivf : ∀ k z, S.cylDiv (N k + k) (S.fieldMul f (hL k) (g k)) z =
      f (P k z) * S.cylDiv (N k) (g k) z - ⟪gradf (P k z), S.cylField (N k) (g k) z⟫ :=
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
  refine ⟨hη', fun k => N k + k, fun k => S.fieldMul f (hL k) (g k), fun k => 2 * B * C k, p,
    hg'2, fun k v => (fieldMul_growth hf (hL k) (g k) (hg k) (C k) (p k) (hgg k) (hDg k)).1 v,
    fun k v => (fieldMul_growth hf (hL k) (g k) (hg k) (C k) (p k) (hgg k) (hDg k)).2 v, ?_, ?_⟩
  · -- field convergence
    refine tendsto_eLpNorm_zero_of_le _
      (fun k z => B * ‖S.cylField (N k) (g k) z - F z‖ +
        ‖f (P k z) - f (R z)‖ * ‖F z‖) (fun k => ?_) (fun k z => ?_)
      (tendsto_eLpNorm_zero_add _ _ hFB hT1)
    · exact ((S.aestronglyMeasurable_cylField _ (hg'2 k).continuous).sub hFm').norm
    · simp only [hfield, norm_norm]
      have hnn : 0 ≤ B * ‖S.cylField (N k) (g k) z - F z‖ + ‖f (P k z) - f (R z)‖ * ‖F z‖ := by
        positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      have e : f (P k z) • S.cylField (N k) (g k) z - f (R z) • F z =
          f (P k z) • (S.cylField (N k) (g k) z - F z) + (f (P k z) - f (R z)) • F z := by
        rw [smul_sub, sub_smul]; abel
      change ‖f (P k z) • S.cylField (N k) (g k) z - f (R z) • F z‖ ≤ _
      rw [e]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_smul, Real.norm_eq_abs]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        simpa using hf.bound _
      · rw [norm_smul, Real.norm_eq_abs]
  · -- divergence convergence
    have hTeq : ∀ k z, S.cylDiv (N k + k) (S.fieldMul f (hL k) (g k)) z -
        (f (R z) * η z - ⟪gradf (R z), F z⟫) =
        ((f (P k z) * (S.cylDiv (N k) (g k) z - η z) + (f (P k z) - f (R z)) * η z) -
          ⟪gradf (P k z), S.cylField (N k) (g k) z - F z⟫) -
          ⟪gradf (P k z) - gradf (R z), F z⟫ := by
      intro k z
      have i1 : ⟪gradf (P k z), S.cylField (N k) (g k) z - F z⟫ =
          ⟪gradf (P k z), S.cylField (N k) (g k) z⟫ - ⟪gradf (P k z), F z⟫ :=
        inner_sub_right _ _ _
      have i2 : ⟪gradf (P k z) - gradf (R z), F z⟫ =
          ⟪gradf (P k z), F z⟫ - ⟪gradf (R z), F z⟫ := inner_sub_left _ _ _
      rw [hdivf k z, i1, i2]
      ring
    have hfun : (fun k => eLpNorm (fun z => S.cylDiv (N k + k) (S.fieldMul f (hL k) (g k)) z -
        (f (R z) * η z - ⟪gradf (R z), F z⟫)) 2 γ) = fun k => eLpNorm (fun z =>
        ((f (P k z) * (S.cylDiv (N k) (g k) z - η z) + (f (P k z) - f (R z)) * η z) -
          ⟪gradf (P k z), S.cylField (N k) (g k) z - F z⟫) -
          ⟪gradf (P k z) - gradf (R z), F z⟫) 2 γ := by
      funext k
      congr 1
      funext z
      exact hTeq k z
    show Tendsto (fun k => eLpNorm (fun z => S.cylDiv (N k + k)
      (S.fieldMul f (hL k) (g k)) z -
        (f (R z) * η z - ⟪gradf (R z), F z⟫)) 2 γ) atTop (𝓝 0)
    rw [hfun]
    refine tendsto_eLpNorm_zero_sub _ _ (tendsto_eLpNorm_zero_sub _ _
      (tendsto_eLpNorm_zero_add _ _ ?_ ?_) ?_) ?_
    · -- t1
      refine tendsto_eLpNorm_zero_of_le _ (fun k z => B * (S.cylDiv (N k) (g k) z - η z))
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
      refine tendsto_eLpNorm_zero_of_le _ (fun k z => B * ‖S.cylField (N k) (g k) z - F z‖)
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

variable {S} in
/-- If `ρ = 1` on an open set `U`, the `H`-gradient of `ρ` vanishes on `U`. -/
theorem ProductRuleClass.grad_eq_zero_of_eqOn_one {ρ : S.E → ℝ}
    {gradρ : S.E → S.H} {B : ℝ}
    (hρ : S.ProductRuleClass ρ gradρ B) {U : Set (S.E)}
    (hU : IsOpen U) (hρ1 : ∀ x ∈ U, ρ x = 1) {x : S.E} (hx : x ∈ U) :
    gradρ x = 0 := by
  have hev : ρ =ᶠ[𝓝 x] fun _ => (1 : ℝ) :=
    Filter.eventuallyEq_of_mem (hU.mem_nhds hx) (fun y hy => hρ1 y hy)
  have hD : fderiv ℝ ρ x = 0 := by
    rw [hev.fderiv_eq, fderiv_fun_const]; rfl
  have h0 : ⟪gradρ x, gradρ x⟫ = 0 := by
    rw [hρ.grad_rep x, hD]; rfl
  exact inner_self_eq_zero.1 h0

variable {S} in
/-- **Locality / independence of the bump.** Let `G, G' : E_s → H` with `G ∘ ξ` and `G' ∘ ξ` having
closed divergences `η`, `η'`. If `ρ` is in the product-rule class, `ρ = 1` on an open set `U`,
and `ρ G = ρ G'` everywhere, then `η = η'` almost surely on `{ξ ∈ U}`. -/
theorem IsClosedDiv.local_eq {ρ : S.E → ℝ}
    {gradρ : S.E → S.H} {B : ℝ}
    (hρ : S.ProductRuleClass ρ gradρ B) {U : Set (S.E)}
    (hU : IsOpen U) (hρ1 : ∀ x ∈ U, ρ x = 1) {G G' : S.E → S.H}
    (hGG : ∀ x, ρ x • G x = ρ x • G' x) {η η' : (ℤ → ℂ) → ℝ}
    (h : S.IsClosedDiv (fun z => G (S.R z)) η)
    (h' : S.IsClosedDiv (fun z => G' (S.R z)) η') :
    ∀ᵐ z ∂S.γ,
      S.R z ∈ U → η z = η' z := by
  set R := S.R with hR
  have h1 := h.smul hρ
  have h2 := h'.smul hρ
  have e : (fun z => ρ (R z) • G' (R z)) = (fun z => ρ (R z) • G (R z)) :=
    funext (fun z => (hGG _).symm)
  have h2' : S.IsClosedDiv (fun z => ρ (R z) • G (R z))
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
theorem exists_riesz_grad 
    (f : S.E → ℝ) (B : ℝ) (x : S.E)
    (hB : ‖fderiv ℝ f x‖ ≤ B) :
    ∃ v : S.H, (∀ h : S.H, ⟪v, h⟫ = fderiv ℝ f x (S.incl h)) ∧
      ‖v‖ ≤ Real.sqrt S.ratioSup * B := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans hB
  have hK0 : 0 ≤ Real.sqrt S.ratioSup * B := mul_nonneg (Real.sqrt_nonneg _) hB0
  refine ⟨(InnerProductSpace.toDual ℝ (S.H)).symm
    (LinearMap.mkContinuous
      { toFun := fun h => fderiv ℝ f x (S.incl h)
        map_add' := fun a b => by
          rw [map_add, map_add]
        map_smul' := fun r a => by
          rw [map_smul, map_smul]; rfl } (Real.sqrt S.ratioSup * B) (fun h => ?_)), fun h => ?_, ?_⟩
  · change ‖fderiv ℝ f x (S.incl h)‖ ≤ (Real.sqrt S.ratioSup * B) * ‖h‖
    calc ‖fderiv ℝ f x (S.incl h)‖
          ≤ ‖fderiv ℝ f x‖ * ‖S.incl h‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ B * (Real.sqrt S.ratioSup * ‖h‖) :=
            mul_le_mul hB (S.incl_norm_le h) (norm_nonneg _) hB0
        _ = (Real.sqrt S.ratioSup * B) * ‖h‖ := by ring
  · rw [InnerProductSpace.toDual_symm_apply]
    rfl
  · rw [LinearIsometryEquiv.norm_map]
    exact LinearMap.mkContinuous_norm_le _ hK0 _

/-- **Satisfiability of the product-rule class.** Every `C²` function `f` on `E_s` with `|f| ≤ B`
and `‖Df‖ ≤ B` has an `H`-gradient, hence lies in `ProductRuleClass` with constant
`(1 + √ratioSup) B` (the Riesz vector has norm `≤ √ratioSup B` since `‖incl‖ ≤ √ratioSup`). -/
theorem exists_productRuleClass 
    (f : S.E → ℝ) (hf : ContDiff ℝ 2 f) (B : ℝ) (hfb : ∀ x, ‖f x‖ ≤ B)
    (hDb : ∀ x, ‖fderiv ℝ f x‖ ≤ B) :
    ∃ gradf : S.E → S.H, S.ProductRuleClass f gradf ((1 + Real.sqrt S.ratioSup) * B) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hfb 0)
  have hs := Real.sqrt_nonneg S.ratioSup
  choose v hv1 hv2 using fun x => S.exists_riesz_grad f B x (hDb x)
  refine ⟨v, hf, fun x => (hfb x).trans ?_, fun x => (hv2 x).trans ?_, fun x h => hv1 x h⟩ <;>
    nlinarith [mul_nonneg hs hB0]

/-- **Existence of bumps in the class.** For every `x₀ ∈ E_s` there are `r > 0` and a function
`ρ` in the product-rule class with `ρ = 1` on the open ball `B(x₀, r)` (from `LocalBump`). -/
theorem exists_bump_productRuleClass 
    (x₀ : S.E) :
    ∃ r > 0, ∃ (ρ : S.E → ℝ) (gradρ : S.E → S.H) (B : ℝ),
      S.ProductRuleClass ρ gradρ B ∧ ∀ x ∈ Metric.ball x₀ r, ρ x = 1 := by
  obtain ⟨r, hr, G, B, hG, hGb, hDGb, hEq⟩ := exists_bumped_field_generic
    (fun _ : S.E => (1 : ℝ)) contDiff_const x₀
  obtain ⟨gradρ, hρ⟩ := S.exists_productRuleClass G hG B hGb hDGb
  exact ⟨r, hr, G, gradρ, (1 + Real.sqrt S.ratioSup) * B, hρ, fun x hx => hEq hx⟩

end NlsGge.Ramer.General.RamerSetting
