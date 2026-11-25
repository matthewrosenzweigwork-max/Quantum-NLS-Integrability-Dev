/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams

Adaptation for NLS-GGE: eight selected supporting proofs are combined in one
namespace with pinned Mathlib imports and legacy non-module syntax. The arc-index
continuity and kernel-holomorphy proofs are generalized from equal endpoints to
arbitrary endpoints; their proofs never use endpoint equality. The literal
normalized arcIndex below replaces the upstream closed-curve-only definition.

Upstream: https://github.com/bjbraams/lean-CA
Commit: 333a684877588d3667c7a0d37e5074aaa2e5b7b7
Source paths:
  ComplexAnalysis/LogDerivIntegral.lean
  ComplexAnalysis/HolomorphicIntegral.lean
  ComplexAnalysis/CurveIndex/Continuity.lean
  ComplexAnalysis/Cycle/Cauchy.lean
  ComplexAnalysis/CurveIndex.lean (literal normalized index definition)
Sources: https://github.com/bjbraams/lean-CA/tree/333a684877588d3667c7a0d37e5074aaa2e5b7b7
The upstream license and credits are included in licenses/.
-/

import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Normed.Operator.Mul

/-! Actual C1-leaf logarithmic integrals and Banach-valued parameter calculus.
No cycle Cauchy theorem, Jordan index value, or geometric realization is asserted.
-/

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory Filter Metric ContinuousLinearMap
open scoped Topology Real

namespace NlsGge.Atomic.ContourKernelParameter

section LogDerivative
open scoped unitInterval

/- Selected upstream A1: ComplexAnalysis/LogDerivIntegral.lean:45. -/
theorem exp_integral_div_of_hasDerivAt {g g' : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hg : ContinuousOn g (Icc a b)) (hg' : ContinuousOn g' (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt g (g' t) t)
    (h0 : ∀ t ∈ Icc a b, g t ≠ 0) :
    exp (∫ t in a..b, g' t / g t) = g b / g a := by
  rcases eq_or_lt_of_le hab with rfl | hab'
  · simp [h0 a ⟨le_rfl, le_rfl⟩]
  let v : ℝ → ℂ := fun t => g' t / g t
  have hv : ContinuousOn v (Icc a b) := hg'.div hg h0
  have hi : IntervalIntegrable v volume a b := hv.intervalIntegrable_of_Icc hab
  let J : ℝ → ℂ := fun t => ∫ s in a..t, v s
  have hJ : ContinuousOn J (Icc a b) := by
    simpa only [uIcc_of_le hab] using
      (intervalIntegral.continuousOn_primitive_interval' hi left_mem_uIcc)
  have hdJ (t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt J (v t) t := by
    have hit : IntervalIntegrable v volume a t :=
      (hv.mono (Icc_subset_Icc le_rfl ht.2.le)).intervalIntegrable_of_Icc ht.1.le
    apply intervalIntegral.integral_hasDerivAt_right hit
    · exact (hv.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo t ht
    · exact hv.continuousAt (Icc_mem_nhds ht.1 ht.2)
  have haux : ∀ t ∈ Ioo a b, HasDerivAt (fun s => exp (-J s) * g s) 0 t := by
    intro t ht
    have h := ((hdJ t ht).neg.cexp).mul (hd t ht)
    convert h using 1
    dsimp [v]
    field_simp [h0 t (Ioo_subset_Icc_self ht)]
    all_goals ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    (hJ.neg.cexp.mul hg) haux
    (intervalIntegrable_const : IntervalIntegrable (fun _ => (0 : ℂ)) volume a b)
  have he' : exp (-J b) * g b = g a := by
    apply sub_eq_zero.mp
    simpa only [Pi.mul_apply, Pi.neg_apply, J, intervalIntegral.integral_same, neg_zero,
      exp_zero, one_mul, intervalIntegral.integral_zero] using he.symm
  apply (eq_div_iff (h0 a (left_mem_Icc.mpr hab))).mpr
  change exp (J b) * g a = g b
  rw [← he', ← mul_assoc, ← exp_add, add_neg_cancel, exp_zero, one_mul]

/- Selected upstream A2: ComplexAnalysis/LogDerivIntegral.lean:85. -/
theorem exp_curveIntegral_sub_inv {a b w : ℂ} (γ : Path a b)
    (hγ : ContDiffOn ℝ 1 γ.extend I) (hw : ∀ t, γ t ≠ w) :
    exp (curveIntegral (fun z => ContinuousLinearMap.toSpanSingleton ℂ ((z - w)⁻¹)) γ) =
      (b - w) / (a - w) := by
  have h0 : ∀ t ∈ I, γ.extend t - w ≠ 0 := by
    intro t ht
    rw [γ.extend_apply ht]
    exact sub_ne_zero.mpr (hw ⟨t, ht⟩)
  have hd : ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (fun s => γ.extend s - w) (derivWithin γ.extend I t) t := by
    intro t ht
    have h := (hγ.differentiableOn one_ne_zero t (Ioo_subset_Icc_self ht)).hasDerivWithinAt
    exact (h.hasDerivAt (Icc_mem_nhds ht.1 ht.2)).sub_const w
  have h := exp_integral_div_of_hasDerivAt (g := fun s => γ.extend s - w) zero_le_one
    (γ.continuous_extend.continuousOn.sub continuousOn_const)
    (hγ.continuousOn_derivWithin uniqueDiffOn_Icc_zero_one le_rfl) hd h0
  simpa only [curveIntegral_def, curveIntegralFun_def, ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul, div_eq_mul_inv, mul_comm, γ.extend_one, γ.extend_zero] using h

end LogDerivative

section ParameterIntegrals

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/- Selected upstream A3: ComplexAnalysis/HolomorphicIntegral.lean:48. -/
omit [CompleteSpace E] in
theorem intervalIntegral_intervalIntegral_swap_of_continuousOn
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) {G : ℝ → ℝ → E}
    (hG : ContinuousOn (fun p : ℝ × ℝ => G p.1 p.2) (Icc a b ×ˢ Icc c d)) :
    ∫ x in a..b, ∫ y in c..d, G x y = ∫ y in c..d, ∫ x in a..b, G x y := by
  have hint : Integrable (Function.uncurry G)
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c d))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact (hG.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  simp only [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd]
  exact integral_integral_swap hint

omit [CompleteSpace E] in

/- Selected upstream A4: ComplexAnalysis/HolomorphicIntegral.lean:63. -/
omit [CompleteSpace E] in
theorem continuousOn_intervalIntegral_of_continuousOn {X : Type*} [TopologicalSpace X]
    [LocallyCompactSpace X] {U : Set X} (hU : IsOpen U) {a b : ℝ} (hab : a ≤ b)
    {F : X → ℝ → E} (hF : ContinuousOn (fun p : X × ℝ => F p.1 p.2) (U ×ˢ Icc a b)) :
    ContinuousOn (fun x => ∫ t in a..b, F x t) U := by
  let G : X → ℝ → E := fun x t => F x (projIcc a b hab t)
  have hGF : ∀ x, ∫ t in a..b, F x t = ∫ t in a..b, G x t := fun x =>
    intervalIntegral.integral_congr fun t ht => by
      simp only [G, projIcc_of_mem hab (by rwa [uIcc_of_le hab] at ht)]
  simp_rw [hGF]
  rw [continuousOn_iff_continuous_domRestrict]
  have := hU.locallyCompactSpace
  have hG : Continuous (fun p : U × ℝ => G p.1 p.2) := by
    have : (fun p : U × ℝ => G p.1 p.2) = (fun p : X × ℝ => F p.1 p.2) ∘
        (fun p : U × ℝ => ((p.1 : X), (projIcc a b hab p.2 : ℝ))) := rfl
    rw [this]
    exact hF.comp_continuous (by fun_prop) fun p => ⟨p.1.2, (projIcc a b hab p.2).2⟩
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun x : U => G x) hG a b

/- Selected upstream A5: ComplexAnalysis/HolomorphicIntegral.lean:87. -/
theorem differentiableOn_intervalIntegral_of_continuousOn {U : Set ℂ} (hU : IsOpen U)
    {a b : ℝ} (hab : a ≤ b) {F : ℂ → ℝ → E}
    (hF : ContinuousOn (fun p : ℂ × ℝ => F p.1 p.2) (U ×ˢ Icc a b))
    (hd : ∀ t ∈ Icc a b, DifferentiableOn ℂ (fun z => F z t) U) :
    DifferentiableOn ℂ (fun z => ∫ t in a..b, F z t) U := by
  intro z₀ hz₀
  obtain ⟨r, hr, hball⟩ := nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hz₀)
  set g : ℂ → E := fun z => ∫ t in a..b, F z t with hg_def
  have hgc : ContinuousOn g U := continuousOn_intervalIntegral_of_continuousOn hU hab hF
  have hrep : ∀ z ∈ ball z₀ r,
      g z = (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(z₀, r), (ζ - z)⁻¹ • g ζ := by
    intro z hz
    have hcauchy : ∀ t ∈ Icc a b,
        F z t = (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(z₀, r), (ζ - z)⁻¹ • F ζ t := by
      intro t ht
      refine (DiffContOnCl.two_pi_i_inv_smul_circleIntegral_sub_inv_smul (f := fun z => F z t)
        ?_ hz).symm
      refine DifferentiableOn.diffContOnCl ?_
      rw [closure_ball z₀ hr.ne']
      exact (hd t ht).mono hball
    have hcont : ContinuousOn
        (fun p : ℝ × ℝ => deriv (circleMap z₀ r) p.2 •
          ((circleMap z₀ r p.2 - z)⁻¹ • F (circleMap z₀ r p.2) p.1))
        (Icc a b ×ˢ Icc 0 (2 * π)) := by
      have h1 : ContinuousOn (fun p : ℝ × ℝ => F (circleMap z₀ r p.2) p.1)
          (Icc a b ×ˢ Icc 0 (2 * π)) := by
        refine hF.comp (f := fun p : ℝ × ℝ => (circleMap z₀ r p.2, p.1)) (by fun_prop) ?_
        rintro ⟨t, θ⟩ ⟨ht, _⟩
        exact ⟨hball (circleMap_mem_closedBall z₀ hr.le θ), ht⟩
      have h2 : ContinuousOn (fun p : ℝ × ℝ => (circleMap z₀ r p.2 - z)⁻¹)
          (Icc a b ×ˢ Icc 0 (2 * π)) := by
        refine ContinuousOn.inv₀ (by fun_prop) ?_
        rintro ⟨t, θ⟩ _
        exact sub_ne_zero.mpr (circleMap_ne_mem_ball hz θ)
      have h3 : Continuous (fun p : ℝ × ℝ => deriv (circleMap z₀ r) p.2) := by
        simp only [deriv_circleMap]
        fun_prop
      exact h3.continuousOn.smul (h2.smul h1)
    calc g z = ∫ t in a..b, (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(z₀, r), (ζ - z)⁻¹ • F ζ t :=
          intervalIntegral.integral_congr fun t ht =>
            hcauchy t (by rwa [uIcc_of_le hab] at ht)
      _ = (2 * π * I : ℂ)⁻¹ • ∫ t in a..b, ∮ ζ in C(z₀, r), (ζ - z)⁻¹ • F ζ t :=
          intervalIntegral.integral_smul _ _
      _ = (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(z₀, r), (ζ - z)⁻¹ • g ζ := by
          congr 1
          simp only [circleIntegral, hg_def]
          rw [intervalIntegral_intervalIntegral_swap_of_continuousOn hab Real.two_pi_pos.le
            hcont]
          refine intervalIntegral.integral_congr fun θ _ => ?_
          simp only [intervalIntegral.integral_smul]
  have hint : CircleIntegrable g z₀ r :=
    (hgc.mono (sphere_subset_closedBall.trans hball)).circleIntegrable hr.le
  have hw : z₀ ∉ sphere z₀ |r| := by
    rw [abs_of_pos hr]
    exact fun h => hr.ne (by simpa using h)
  have hderiv := (hasDerivAt_circleIntegral_sub_inv_smul hint hw).const_smul
    ((2 * π * I : ℂ)⁻¹)
  have heq : g =ᶠ[𝓝 z₀] fun z => (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(z₀, r), (ζ - z)⁻¹ • g ζ := by
    filter_upwards [ball_mem_nhds z₀ hr] with z hz
    exact hrep z hz
  exact ((heq.differentiableAt_iff).mpr hderiv.differentiableAt).differentiableWithinAt

/- Selected upstream A6: ComplexAnalysis/HolomorphicIntegral.lean:151. -/
theorem continuousOn_dslope_prod_of_differentiableOn {U : Set ℂ} (hU : IsOpen U) {f : ℂ → E}
    (hf : DifferentiableOn ℂ f U) :
    ContinuousOn (fun p : ℂ × ℂ => dslope f p.1 p.2) (U ×ˢ U) := by
  have hderiv : ContinuousOn (deriv f) U := (hf.analyticOnNhd hU).deriv.continuousOn
  intro p hp
  by_cases hne : p.1 = p.2
  · obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU p.1 hp.1
    have hseg : ∀ x ∈ ball p.1 r, ∀ y ∈ ball p.1 r, ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 →
        x + (s : ℂ) * (y - x) ∈ ball p.1 r := by
      intro x hx y hy s hs
      have := (convex_ball p.1 r).add_smul_sub_mem hx hy hs
      rwa [Complex.real_smul] at this
    have hrep : EqOn (fun q : ℂ × ℂ => dslope f q.1 q.2)
        (fun q : ℂ × ℂ => ∫ s in (0 : ℝ)..1, deriv f (q.1 + (s : ℂ) * (q.2 - q.1)))
        (ball p.1 r ×ˢ ball p.1 r) := by
      rintro ⟨x, y⟩ ⟨hx, hy⟩
      dsimp only
      by_cases hxy : y = x
      · subst hxy
        simp [dslope_same]
      · rw [dslope_of_ne _ hxy, slope_def_module]
        have hFTC : ∫ s in (0 : ℝ)..1, (y - x) • deriv f (x + (s : ℂ) * (y - x)) =
            f y - f x := by
          have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := 1)
            (f := fun s : ℝ => f (x + (s : ℂ) * (y - x)))
            (f' := fun s : ℝ => (y - x) • deriv f (x + (s : ℂ) * (y - x))) ?_ ?_
          · simpa using h
          · intro s hs
            rw [uIcc_of_le zero_le_one] at hs
            have h1 : HasDerivAt (fun w : ℂ => x + w * (y - x)) (y - x) (s : ℂ) := by
              simpa using ((hasDerivAt_id (s : ℂ)).mul_const (y - x)).const_add x
            have hmem := hball (hseg x hx y hy s hs)
            have h2 := ((hf.differentiableAt (hU.mem_nhds hmem)).hasDerivAt.scomp (s : ℂ) h1)
            simpa only [ofRealCLM_apply, ofReal_one, one_smul, Function.comp_def] using!
              h2.scomp s ofRealCLM.hasDerivAt
          · refine (ContinuousOn.intervalIntegrable ?_)
            rw [uIcc_of_le zero_le_one]
            refine continuousOn_const.smul
              (hderiv.comp (f := fun s : ℝ => x + (s : ℂ) * (y - x)) (by fun_prop) ?_)
            intro s hs
            exact hball (hseg x hx y hy s hs)
        rw [intervalIntegral.integral_smul] at hFTC
        rw [← hFTC, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hxy), one_smul]
    have hcont : ContinuousOn
        (fun q : ℂ × ℂ => ∫ s in (0 : ℝ)..1, deriv f (q.1 + (s : ℂ) * (q.2 - q.1)))
        (ball p.1 r ×ˢ ball p.1 r) := by
      refine continuousOn_intervalIntegral_of_continuousOn (isOpen_ball.prod isOpen_ball)
        zero_le_one ?_
      refine hderiv.comp (f := fun q : (ℂ × ℂ) × ℝ => q.1.1 + (q.2 : ℂ) * (q.1.2 - q.1.1))
        (by fun_prop) ?_
      rintro ⟨⟨x, y⟩, s⟩ ⟨⟨hx, hy⟩, hs⟩
      exact hball (hseg x hx y hy s hs)
    have hmem : p ∈ ball p.1 r ×ˢ ball p.1 r :=
      ⟨mem_ball_self hr, by rw [← hne]; exact mem_ball_self hr⟩
    exact ((hcont.congr hrep).continuousAt
      ((isOpen_ball.prod isOpen_ball).mem_nhds hmem)).continuousWithinAt
  · have hev : ∀ᶠ q : ℂ × ℂ in 𝓝 p, q.1 ≠ q.2 :=
      (isOpen_ne_fun continuous_fst continuous_snd).mem_nhds hne
    have hc : ContinuousAt (fun q : ℂ × ℂ => (q.2 - q.1)⁻¹ • (f q.2 - f q.1)) p := by
      have hf1 : ContinuousAt f p.1 := hf.continuousOn.continuousAt (hU.mem_nhds hp.1)
      have hf2 : ContinuousAt f p.2 := hf.continuousOn.continuousAt (hU.mem_nhds hp.2)
      refine ContinuousAt.smul ?_ ((hf2.comp continuousAt_snd).sub (hf1.comp continuousAt_fst))
      exact (continuousAt_snd.sub continuousAt_fst).inv₀ (sub_ne_zero.mpr (Ne.symm hne))
    refine (hc.congr_of_eventuallyEq ?_).continuousWithinAt
    filter_upwards [hev] with q hq
    rw [dslope_of_ne _ (Ne.symm hq), slope_def_module]

end ParameterIntegrals

open scoped unitInterval

/-- The literal normalized scalar kernel integral, for arbitrary path endpoints.
No integer or geometric index value is part of this definition. -/
def arcIndex {a b : ℂ} (γ : Path a b) (w : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
    curveIntegral (fun z => ContinuousLinearMap.toSpanSingleton ℂ ((z - w)⁻¹)) γ

/- Selected upstream A7: ComplexAnalysis/CurveIndex/Continuity.lean:49. -/
theorem continuousOn_arcIndex {a b : ℂ} (γ : Path a b)
    (hγ : ContDiffOn ℝ 1 γ.extend I) :
    ContinuousOn (arcIndex γ) (range γ)ᶜ := by
  let U := (range γ)ᶜ
  have hU : IsOpen U := (isCompact_range γ.continuous).isClosed.isOpen_compl
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let D : ℝ → ℂ := fun t => derivWithin γ.extend I (projIcc 0 1 zero_le_one t)
  have hD : Continuous D :=
    (continuousOn_iff_continuous_domRestrict.mp
      (hγ.continuousOn_derivWithin uniqueDiffOn_Icc_zero_one le_rfl)).comp continuous_projIcc
  let K : U → ℝ → ℂ := fun w t => (γ.extend t - w)⁻¹ * D t
  have hK : Continuous K.uncurry := by
    apply Continuous.mul
    · apply Continuous.inv₀
      · exact (γ.continuous_extend.comp continuous_snd).sub
          (continuous_subtype_val.comp continuous_fst)
      · intro p
        apply sub_ne_zero.mpr
        intro he
        exact p.1.property ⟨projIcc 0 1 zero_le_one p.2, he⟩
    · exact hD.comp continuous_snd
  have hc := continuous_parametric_integral_of_continuous hK isCompact_Icc
    (μ := volume) (s := I)
  have he (w : U) : arcIndex γ w =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * ∫ t in I, K w t := by
    rw [arcIndex, curveIntegral_def, intervalIntegral.integral_of_le zero_le_one,
      ← integral_Icc_eq_integral_Ioc]
    congr 1
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    simp only [curveIntegralFun_def, ContinuousLinearMap.toSpanSingleton_apply,
      smul_eq_mul, K, D, projIcc_of_mem zero_le_one ht, mul_comm]
  exact continuousOn_iff_continuous_domRestrict.mpr
    ((continuous_const.mul hc).congr (fun w => (he w).symm))

section CurveParameter

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/- Selected upstream A8: ComplexAnalysis/Cycle/Cauchy.lean:46. -/
theorem differentiableOn_curveIntegral_kernel {U : Set ℂ} (hU : IsOpen U) {a b : ℂ}
    {γ : Path a b} (hγ : ContDiffOn ℝ 1 γ.extend I) {V : Set ℂ} (hγV : ∀ t, γ t ∈ V)
    {K : ℂ → ℂ → F} (hK : ContinuousOn (fun p : ℂ × ℂ => K p.1 p.2) (U ×ˢ V))
    (hd : ∀ w ∈ V, DifferentiableOn ℂ (fun z => K z w) U) :
    DifferentiableOn ℂ (fun z => curveIntegral (fun w => toSpanSingleton ℂ (K z w)) γ) U := by
  have hV : ∀ t : ℝ, γ.extend t ∈ V := fun t => by
    obtain ⟨s, hs⟩ : γ.extend t ∈ Set.range γ := γ.extend_range ▸ mem_range_self t
    rw [← hs]
    exact hγV s
  simp only [curveIntegral_def, curveIntegralFun_def, toSpanSingleton_apply]
  refine differentiableOn_intervalIntegral_of_continuousOn hU zero_le_one ?_ ?_
  · have hder : ContinuousOn (fun p : ℂ × ℝ => derivWithin γ.extend I p.2) (U ×ˢ Icc 0 1) :=
      (hγ.continuousOn_derivWithin uniqueDiffOn_Icc_zero_one le_rfl).comp
        continuous_snd.continuousOn fun p hp => hp.2
    refine hder.smul ?_
    refine hK.comp (f := fun p : ℂ × ℝ => (p.1, γ.extend p.2)) ?_ ?_
    · exact continuous_fst.continuousOn.prodMk (γ.continuous_extend.comp_continuousOn
        continuous_snd.continuousOn)
    · rintro ⟨z, t⟩ ⟨hz, _⟩
      exact ⟨hz, hV t⟩
  · intro t _
    exact (hd _ (hV t)).const_smul _

end CurveParameter

end NlsGge.Atomic.ContourKernelParameter
