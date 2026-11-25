import Mathlib
import NlsGge.Atomic.G4.G4012

/- G5-027 SUPPORT 1 `G5027Sup1` (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/Atomic/G5/G5027Sup1.lean, namespace NlsGge.GKDefinitionDesign.G5027Aux.
   Generic tip asymptotic (GK Lemma 18.4, analytic core; no NLS content):  if r^2 = mu - a with r, mu, a analytic near phi0,
   mu phi0 = a phi0 and g analytic at (phi0, a phi0), then for e = r * int_0^1 g(., a + t(mu - a)) / sqrt t dt and any
   phi_j -> phi0 with r phi_j != 0,  de(phi_j) - (g(phi_j, mu phi_j)/r phi_j) • (dmu - da)(phi_j) -> 0.
   Route: K = int g/sqrt t analytic (G4-012); d(rK) = r dK + K dr; 2 r dr = dmu - da; |K - 2 g(mu)| <= 2 B |r|^2 by the mean value
   bound of z |-> g(phi, z) and int_0^1 t^(-1/2) = 2; r(phi_j) -> r(phi0) = 0. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory

namespace NlsGge.GKDefinitionDesign
namespace G5027Aux
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The segment integral. -/
def segK (g : E × ℂ → ℂ) (a μ : E → ℂ) (φ : E) : ℂ :=
  ∫ t in (0 : ℝ)..1, g (φ, a φ + (t : ℂ) * (μ φ - a φ)) / (Real.sqrt t : ℂ)

theorem seg_mem_ball {z0 a m : ℂ} {δ : ℝ} (ha : a ∈ ball z0 δ) (hm : m ∈ ball z0 δ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : a + (t : ℂ) * (m - a) ∈ ball z0 δ := by
  have h := (convex_ball z0 δ) ha hm (sub_nonneg.2 ht.2) ht.1 (by ring)
  convert h using 1
  simp only [Complex.real_smul]
  push_cast
  ring

theorem inv_sqrt_eq_rpow {t : ℝ} (ht : 0 < t) : (Real.sqrt t)⁻¹ = t ^ (-(1 / 2 : ℝ)) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_neg ht.le]

theorem integral_inv_sqrt : ∫ t in (0 : ℝ)..1, t ^ (-(1 / 2 : ℝ)) = 2 := by
  rw [integral_rpow (Or.inl (by norm_num))]
  norm_num

theorem intervalIntegrable_rpow_half : IntervalIntegrable (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) volume 0 1 :=
  intervalIntegral.intervalIntegrable_rpow' (by norm_num)

/-- A bounded continuous-on-(0,1] function divided by sqrt t is interval integrable. -/
theorem integrable_div_sqrt (h : ℝ → ℂ) (C : ℝ) (hc : ContinuousOn h (Ioc (0 : ℝ) 1))
    (hb : ∀ t ∈ Ioc (0 : ℝ) 1, ‖h t‖ ≤ C) :
    IntervalIntegrable (fun t : ℝ => h t / (Real.sqrt t : ℂ)) volume 0 1 := by
  have hmaj : IntervalIntegrable (fun t : ℝ => C * t ^ (-(1 / 2 : ℝ))) volume 0 1 :=
    intervalIntegrable_rpow_half.const_mul C
  refine hmaj.mono_fun' ?_ ?_
  · rw [Set.uIoc_of_le zero_le_one]
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
    refine hc.div (Complex.continuous_ofReal.comp_continuousOn Real.continuous_sqrt.continuousOn) ?_
    intro t ht
    exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 ht.1).ne'
  · refine (ae_restrict_iff' measurableSet_uIoc).2 (Filter.Eventually.of_forall fun t ht => ?_)
    rw [Set.uIoc_of_le zero_le_one] at ht
    have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht.1
    show ‖h t / (Real.sqrt t : ℂ)‖ ≤ C * t ^ (-(1 / 2 : ℝ))
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hs.le, ← inv_sqrt_eq_rpow ht.1,
      ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_right (hb t ht) hs.le

theorem fderiv_sq_root {r μ a : E → ℂ} {V : Set E} (hV : IsOpen V) {φ : E} (hφ : φ ∈ V)
    (hr : AnalyticOnNhd ℂ r V) (hμ : AnalyticOnNhd ℂ μ V) (ha : AnalyticOnNhd ℂ a V)
    (hsq : ∀ ψ ∈ V, r ψ ^ 2 = μ ψ - a ψ) (hne : r φ ≠ 0) :
    fderiv ℂ r φ = (2 * r φ)⁻¹ • (fderiv ℂ μ φ - fderiv ℂ a φ) := by
  have h1 : HasFDerivAt (fun ψ => r ψ * r ψ) (r φ • fderiv ℂ r φ + r φ • fderiv ℂ r φ) φ :=
    (hr φ hφ).differentiableAt.hasFDerivAt.mul (hr φ hφ).differentiableAt.hasFDerivAt
  have h2 : HasFDerivAt (fun ψ => μ ψ - a ψ) (fderiv ℂ μ φ - fderiv ℂ a φ) φ :=
    (hμ φ hφ).differentiableAt.hasFDerivAt.sub (ha φ hφ).differentiableAt.hasFDerivAt
  have heq : (fun ψ => μ ψ - a ψ) =ᶠ[𝓝 φ] (fun ψ => r ψ * r ψ) := by
    filter_upwards [hV.mem_nhds hφ] with ψ hψ
    rw [← hsq ψ hψ, sq]
  have h3 := (h1.congr_of_eventuallyEq heq).unique h2
  rw [← h3]
  ext v
  simp only [smul_apply, add_apply, smul_eq_mul]
  field_simp
  ring

theorem tip_asymptotic (V : Set E) (hV : IsOpen V) (φ0 : E) (h0 : φ0 ∈ V) (a μ r : E → ℂ)
    (ha : AnalyticOnNhd ℂ a V) (hμ : AnalyticOnNhd ℂ μ V) (hr : AnalyticOnNhd ℂ r V)
    (hsq : ∀ φ ∈ V, r φ ^ 2 = μ φ - a φ) (hμa : μ φ0 = a φ0)
    (g : E × ℂ → ℂ) (hg : AnalyticAt ℂ g (φ0, a φ0))
    (φs : ℕ → E) (hφs : Tendsto φs atTop (𝓝 φ0)) (hne : ∀ j : ℕ, r (φs j) ≠ 0) :
    Tendsto (fun j : ℕ => fderiv ℂ (fun φ => r φ * segK g a μ φ) (φs j) -
      (g (φs j, μ (φs j)) / r (φs j)) • (fderiv ℂ μ (φs j) - fderiv ℂ a (φs j)))
      atTop (𝓝 0) := by
  -- Step A: local constants for g near (φ0, a φ0)
  obtain ⟨δ1, hδ1, hA1⟩ := Metric.eventually_nhds_iff_ball.1 hg.eventually_analyticAt
  have hAn1 : AnalyticOnNhd ℂ g (ball (φ0, a φ0) δ1) := fun p hp => hA1 p hp
  have hcontD : ContinuousAt (fderiv ℂ g) (φ0, a φ0) :=
    hAn1.fderiv.continuousOn.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hδ1))
  obtain ⟨B, hB0, evB⟩ : ∃ B : ℝ, 0 < B ∧ ∀ᶠ p in 𝓝 (φ0, a φ0), ‖fderiv ℂ g p‖ < B :=
    ⟨_, by positivity, hcontD.norm.eventually (gt_mem_nhds (lt_add_one _))⟩
  obtain ⟨M, hM0, evM⟩ : ∃ M : ℝ, 0 < M ∧ ∀ᶠ p in 𝓝 (φ0, a φ0), ‖g p‖ < M :=
    ⟨_, by positivity, hg.continuousAt.norm.eventually (gt_mem_nhds (lt_add_one _))⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1
    (hg.eventually_analyticAt.and (evB.and evM))
  -- Step B: a neighbourhood of φ0
  have hac : ContinuousAt a φ0 := (ha φ0 h0).continuousAt
  have hμc : ContinuousAt μ φ0 := (hμ φ0 h0).continuousAt
  have hμball : ∀ᶠ y in 𝓝 (μ φ0), y ∈ ball (a φ0) δ := by
    rw [hμa]; exact ball_mem_nhds _ hδ
  have e0 : ∀ᶠ φ in 𝓝 φ0, φ ∈ V := hV.mem_nhds h0
  have e1 : ∀ᶠ φ in 𝓝 φ0, φ ∈ ball φ0 δ := ball_mem_nhds φ0 hδ
  have e2' : ∀ᶠ y in 𝓝 (a φ0), y ∈ ball (a φ0) δ := ball_mem_nhds _ hδ
  have e2 : ∀ᶠ φ in 𝓝 φ0, a φ ∈ ball (a φ0) δ := hac.eventually e2'
  have e3 : ∀ᶠ φ in 𝓝 φ0, μ φ ∈ ball (a φ0) δ := hμc.eventually hμball
  have evU : ∀ᶠ φ in 𝓝 φ0, φ ∈ V ∧ φ ∈ ball φ0 δ ∧ a φ ∈ ball (a φ0) δ ∧ μ φ ∈ ball (a φ0) δ :=
    e0.and (e1.and (e2.and e3))
  obtain ⟨η, hη, hU⟩ := Metric.eventually_nhds_iff_ball.1 evU
  have hmemP : ∀ φ ∈ ball φ0 η, ∀ t ∈ Icc (0 : ℝ) 1,
      ((φ, a φ + (t : ℂ) * (μ φ - a φ)) : E × ℂ) ∈ ball (φ0, a φ0) δ := by
    intro φ hφ t ht
    obtain ⟨-, h1, h2, h3⟩ := hU φ hφ
    rw [← ball_prod_same]
    exact ⟨h1, seg_mem_ball h2 h3 ht⟩
  have hpath : ∀ t : ℝ, ∀ φ ∈ ball φ0 η,
      AnalyticAt ℂ (fun ψ : E => ((ψ, a ψ + (t : ℂ) * (μ ψ - a ψ)) : E × ℂ)) φ := by
    intro t φ hφ
    have hφV := (hU φ hφ).1
    exact analyticAt_id.prod ((ha φ hφV).add (analyticAt_const.mul ((hμ φ hφV).sub (ha φ hφV))))
  have hGan : ∀ t ∈ Icc (0 : ℝ) 1, ∀ φ ∈ ball φ0 η,
      AnalyticAt ℂ (fun ψ : E => g (ψ, a ψ + (t : ℂ) * (μ ψ - a ψ))) φ :=
    fun t ht φ hφ => AnalyticAt.comp (g := g)
      (f := fun ψ : E => ((ψ, a ψ + (t : ℂ) * (μ ψ - a ψ)) : E × ℂ))
      (hball _ (hmemP φ hφ t ht)).1 (hpath t φ hφ)
  have hGc : ∀ φ ∈ ball φ0 η,
      ContinuousOn (fun t : ℝ => g (φ, a φ + (t : ℂ) * (μ φ - a φ))) (Icc (0 : ℝ) 1) := by
    intro φ hφ t ht
    apply ContinuousAt.continuousWithinAt
    have hc : Continuous (fun s : ℝ => ((φ, a φ + (s : ℂ) * (μ φ - a φ)) : E × ℂ)) := by fun_prop
    exact ContinuousAt.comp (g := g)
      (f := fun s : ℝ => ((φ, a φ + (s : ℂ) * (μ φ - a φ)) : E × ℂ))
      (hball _ (hmemP φ hφ t ht)).1.continuousAt hc.continuousAt
  -- Step C: the segment integral is analytic near φ0
  have hK : AnalyticOnNhd ℂ (segK g a μ) (ball φ0 η) := by
    have hmain := NlsGge.Atomic.G4.analyticOn_integral_of_rpow_half_locally_dominated
      (E := E) (F := ℂ) (U := ball φ0 η)
      (a := fun (t : ℝ) (φ : E) => g (φ, a φ + (t : ℂ) * (μ φ - a φ)) / (Real.sqrt t : ℂ))
      M hM0.le isOpen_ball
      ((ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun t ht φ hφ =>
        (hGan t (Ioo_subset_Icc_self ht) φ hφ).div analyticAt_const
          (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 ht.1).ne')))
      (fun φ hφ => by
        refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
        refine ((hGc φ hφ).mono Ioo_subset_Icc_self).div
          (Complex.continuous_ofReal.comp_continuousOn Real.continuous_sqrt.continuousOn) ?_
        intro t ht
        exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 ht.1).ne')
      (fun φ hφ => by
        obtain ⟨ρ, hρ, hsub⟩ := Metric.isOpen_iff.1 isOpen_ball φ hφ
        refine ⟨ρ, hρ, hsub, fun v hv => ?_⟩
        refine (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun t ht => ?_)
        have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht.1
        have hb := (hball _ (hmemP v (hsub hv) t (Ioo_subset_Icc_self ht))).2.2
        have hr' : Real.rpow t (-1 / 2) = (Real.sqrt t)⁻¹ := by
          rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num]
          exact (inv_sqrt_eq_rpow ht.1).symm
        rw [hr', norm_div, Complex.norm_real, Real.norm_of_nonneg hs.le, ← div_eq_mul_inv]
        exact div_le_div_of_nonneg_right hb.le hs.le)
    have hfun : (fun φ : E => ∫ t, g (φ, a φ + (t : ℂ) * (μ φ - a φ)) / (Real.sqrt t : ℂ)
        ∂(volume.restrict (Ioo (0 : ℝ) 1))) = segK g a μ := by
      funext φ
      simp only [segK]
      rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
    rw [← hfun]
    exact hmain
  -- Step D-F: the exact decomposition at points with r ≠ 0
  have hform : ∀ φ ∈ ball φ0 η, r φ ≠ 0 →
      fderiv ℂ (fun ψ => r ψ * segK g a μ ψ) φ -
        (g (φ, μ φ) / r φ) • (fderiv ℂ μ φ - fderiv ℂ a φ) =
      r φ • fderiv ℂ (segK g a μ) φ +
        ((segK g a μ φ - 2 * g (φ, μ φ)) / (2 * r φ)) • (fderiv ℂ μ φ - fderiv ℂ a φ) := by
    intro φ hφ hrφ
    have hφV := (hU φ hφ).1
    have hmul : fderiv ℂ (fun ψ => r ψ * segK g a μ ψ) φ =
        r φ • fderiv ℂ (segK g a μ) φ + segK g a μ φ • fderiv ℂ r φ :=
      ((hr φ hφV).differentiableAt.hasFDerivAt.mul (hK φ hφ).differentiableAt.hasFDerivAt).fderiv
    rw [hmul, fderiv_sq_root hV hφV hr hμ ha hsq hrφ]
    ext v
    simp only [sub_apply, add_apply,
      smul_apply, smul_eq_mul]
    field_simp
    ring
  -- Step G: the quadratic bound
  have hbound : ∀ φ ∈ ball φ0 η,
      ‖segK g a μ φ - 2 * g (φ, μ φ)‖ ≤ 2 * B * ‖μ φ - a φ‖ := by
    intro φ hφ
    obtain ⟨-, hφδ, haδ, hμδ⟩ := hU φ hφ
    have hdiff : ∀ z ∈ ball (a φ0) δ, HasFDerivWithinAt (fun w : ℂ => g (φ, w))
        ((fderiv ℂ g (φ, z)).comp (ContinuousLinearMap.inr ℂ E ℂ)) (ball (a φ0) δ) z := by
      intro z hz
      have hp : ((φ, z) : E × ℂ) ∈ ball (φ0, a φ0) δ := by
        rw [← ball_prod_same]; exact ⟨hφδ, hz⟩
      have h1 := (hball _ hp).1.differentiableAt.hasFDerivAt
      exact (h1.comp z (hasFDerivAt_prodMk_right φ z)).hasFDerivWithinAt
    have hbd : ∀ z ∈ ball (a φ0) δ,
        ‖(fderiv ℂ g (φ, z)).comp (ContinuousLinearMap.inr ℂ E ℂ)‖ ≤ B := by
      intro z hz
      have hp : ((φ, z) : E × ℂ) ∈ ball (φ0, a φ0) δ := by
        rw [← ball_prod_same]; exact ⟨hφδ, hz⟩
      refine ContinuousLinearMap.opNorm_le_bound _ hB0.le (fun v => ?_)
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
      have hn : ‖((0 : E), v)‖ = ‖v‖ := by simp [Prod.norm_def]
      calc ‖fderiv ℂ g (φ, z) (0, v)‖ ≤ ‖fderiv ℂ g (φ, z)‖ * ‖((0 : E), v)‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ B * ‖v‖ := by
            rw [hn]
            exact mul_le_mul_of_nonneg_right (hball _ hp).2.1.le (norm_nonneg v)
    have hlip : ∀ t ∈ Icc (0 : ℝ) 1,
        ‖g (φ, a φ + (t : ℂ) * (μ φ - a φ)) - g (φ, μ φ)‖ ≤ B * ‖μ φ - a φ‖ := by
      intro t ht
      have hmv := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
        (f := fun w : ℂ => g (φ, w)) hdiff hbd (convex_ball (a φ0) δ) hμδ (seg_mem_ball haδ hμδ ht)
      have he : a φ + (t : ℂ) * (μ φ - a φ) - μ φ = ((t - 1 : ℝ) : ℂ) * (μ φ - a φ) := by
        push_cast; ring
      have h1 : ‖((t - 1 : ℝ) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
        constructor <;> linarith [ht.1, ht.2]
      calc ‖g (φ, a φ + (t : ℂ) * (μ φ - a φ)) - g (φ, μ φ)‖
          ≤ B * ‖a φ + (t : ℂ) * (μ φ - a φ) - μ φ‖ := hmv
        _ ≤ B * ‖μ φ - a φ‖ := by
            refine mul_le_mul_of_nonneg_left ?_ hB0.le
            rw [he, norm_mul]
            exact mul_le_of_le_one_left (norm_nonneg _) h1
    have hI1 : IntervalIntegrable (fun t : ℝ =>
        g (φ, a φ + (t : ℂ) * (μ φ - a φ)) / (Real.sqrt t : ℂ)) volume 0 1 :=
      integrable_div_sqrt _ M ((hGc φ hφ).mono Ioc_subset_Icc_self)
        (fun t ht => (hball _ (hmemP φ hφ t (Ioc_subset_Icc_self ht))).2.2.le)
    have hI2 : IntervalIntegrable (fun t : ℝ => g (φ, μ φ) / (Real.sqrt t : ℂ)) volume 0 1 :=
      integrable_div_sqrt _ ‖g (φ, μ φ)‖ continuousOn_const (fun _ _ => le_rfl)
    have hreal : ∫ t in (0 : ℝ)..1, (Real.sqrt t)⁻¹ = 2 := by
      rw [← integral_inv_sqrt]
      refine intervalIntegral.integral_congr (fun t ht => ?_)
      rw [Set.uIcc_of_le zero_le_one] at ht
      rcases eq_or_lt_of_le ht.1 with h | h
      · subst h
        simp
      · exact inv_sqrt_eq_rpow h
    have h2 : ∫ t in (0 : ℝ)..1, g (φ, μ φ) / (Real.sqrt t : ℂ) = 2 * g (φ, μ φ) := by
      simp_rw [div_eq_mul_inv]
      rw [intervalIntegral.integral_const_mul]
      have hc : (fun t : ℝ => ((Real.sqrt t : ℂ))⁻¹) = fun t => (((Real.sqrt t)⁻¹ : ℝ) : ℂ) := by
        funext t; push_cast; rfl
      rw [hc, intervalIntegral.integral_ofReal, hreal]
      push_cast
      ring
    have hdiffI : segK g a μ φ - 2 * g (φ, μ φ) = ∫ t in (0 : ℝ)..1,
        (g (φ, a φ + (t : ℂ) * (μ φ - a φ)) - g (φ, μ φ)) / (Real.sqrt t : ℂ) := by
      rw [← h2, segK, ← intervalIntegral.integral_sub hI1 hI2]
      congr 1
      funext t
      ring
    rw [hdiffI]
    calc ‖∫ t in (0 : ℝ)..1,
          (g (φ, a φ + (t : ℂ) * (μ φ - a φ)) - g (φ, μ φ)) / (Real.sqrt t : ℂ)‖
        ≤ ∫ t in (0 : ℝ)..1, B * ‖μ φ - a φ‖ * t ^ (-(1 / 2 : ℝ)) := by
          refine intervalIntegral.norm_integral_le_of_norm_le zero_le_one
            (Filter.Eventually.of_forall fun t ht => ?_)
            (intervalIntegrable_rpow_half.const_mul _)
          have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht.1
          rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hs.le, ← inv_sqrt_eq_rpow ht.1,
            ← div_eq_mul_inv]
          exact div_le_div_of_nonneg_right (hlip t (Ioc_subset_Icc_self ht)) hs.le
      _ = 2 * B * ‖μ φ - a φ‖ := by
          rw [intervalIntegral.integral_const_mul, integral_inv_sqrt]
          ring
  -- Step H: the limit
  have hr0 : r φ0 = 0 := by
    have h := hsq φ0 h0
    rw [hμa, sub_self] at h
    exact (pow_eq_zero_iff two_ne_zero).1 h
  have hev : ∀ᶠ j in atTop, φs j ∈ ball φ0 η :=
    hφs.eventually (isOpen_ball.mem_nhds (mem_ball_self hη))
  have trR : Tendsto (fun j => r (φs j)) atTop (𝓝 0) := by
    rw [← hr0]
    exact (hr φ0 h0).continuousAt.tendsto.comp hφs
  have trDK : Tendsto (fun j => fderiv ℂ (segK g a μ) (φs j)) atTop
      (𝓝 (fderiv ℂ (segK g a μ) φ0)) :=
    (hK.fderiv.continuousOn.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hη))).tendsto.comp hφs
  have trD : Tendsto (fun j => fderiv ℂ μ (φs j) - fderiv ℂ a (φs j)) atTop
      (𝓝 (fderiv ℂ μ φ0 - fderiv ℂ a φ0)) :=
    ((hμ.fderiv.continuousOn.continuousAt (hV.mem_nhds h0)).tendsto.comp hφs).sub
      ((ha.fderiv.continuousOn.continuousAt (hV.mem_nhds h0)).tendsto.comp hφs)
  have trQ : Tendsto (fun j => (segK g a μ (φs j) - 2 * g (φs j, μ (φs j))) / (2 * r (φs j)))
      atTop (𝓝 0) := by
    have hq : ∀ᶠ j in atTop, ‖(segK g a μ (φs j) - 2 * g (φs j, μ (φs j))) / (2 * r (φs j))‖ ≤
        B * ‖r (φs j)‖ := by
      filter_upwards [hev] with j hj
      have hb := hbound _ hj
      rw [← hsq _ (hU _ hj).1, norm_pow] at hb
      have hrpos : 0 < ‖r (φs j)‖ := norm_pos_iff.2 (hne j)
      have h2 : ‖(2 : ℂ)‖ = 2 := by simp
      rw [norm_div, norm_mul, h2, div_le_iff₀ (by positivity)]
      nlinarith [hb]
    exact squeeze_zero_norm' hq (by simpa using trR.norm.const_mul B)
  have hlim : Tendsto (fun j => r (φs j) • fderiv ℂ (segK g a μ) (φs j) +
      ((segK g a μ (φs j) - 2 * g (φs j, μ (φs j))) / (2 * r (φs j))) •
        (fderiv ℂ μ (φs j) - fderiv ℂ a (φs j))) atTop (𝓝 0) := by
    have := (trR.smul trDK).add (trQ.smul trD)
    convert this using 2
    ext v
    simp
  refine hlim.congr' ?_
  filter_upwards [hev] with j hj
  exact (hform _ hj (hne j)).symm

end
end G5027Aux
end NlsGge.GKDefinitionDesign
