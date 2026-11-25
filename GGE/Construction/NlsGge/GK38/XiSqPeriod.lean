import NlsGge.GK38.XiSqKernel
import NlsGge.Analysis.NonvanishingLoop
import Mathlib.Analysis.SpecialFunctions.Complex.Log

set_option autoImplicit false
open Set Filter Topology Metric MeasureTheory
namespace NlsGge.GK38
noncomputable section

def a5LogQuotient38 (φ : PotPair) (z : ℂ) : ℂ :=
  deriv (discrim φ) z / canonRoot38 φ z

def a5Period38 (φ : PotPair) (n : ℤ) : ℂ :=
  circleIntegral (a5LogQuotient38 φ) (discC φ n) (discR φ n)

theorem a5LogQuotient_joint_analytic38 :
    AnalyticOnNhd ℂ (Function.uncurry a5LogQuotient38) rootDomain38 := by
  intro p hp
  exact (analyticOnNhd_discrimDeriv_joint38 p (mem_univ _)).div
    (canonRoot_analytic38 p hp) (canonRoot_ne_zero38 p.1 hp.1 p.2 hp.2)

theorem a5LogQuotient_analytic38 (φ : PotPair) (hφ : φ ∈ gkW) :
    AnalyticOnNhd ℂ (a5LogQuotient38 φ) (actionCutDomain38 φ) := by
  intro z hz
  exact AnalyticAt.comp (g := Function.uncurry a5LogQuotient38)
    (f := fun w : ℂ => (φ, w)) (a5LogQuotient_joint_analytic38 _ ⟨hφ, hz⟩)
    (analyticAt_const.prod analyticAt_id)

theorem a5DeltaPlusRoot_ne_zero38 (φ : PotPair) (hφ : φ ∈ gkW)
    (z : ℂ) (hz : z ∉ gapSegments38 φ) :
    discrim φ z + canonRoot38 φ z ≠ 0 := by
  intro he
  have hs := canonRoot_sq38 φ hφ z hz
  rw [perChar_eq] at hs
  have hr : canonRoot38 φ z = -discrim φ z := by linear_combination he
  rw [hr] at hs
  have : (4 : ℂ) = 0 := by linear_combination hs
  norm_num at this

theorem a5DeltaPlusRoot_hasDeriv38 (φ : PotPair) (hφ : φ ∈ gkW)
    (z : ℂ) (hz : z ∉ gapSegments38 φ) :
    HasDerivAt (fun w => discrim φ w + canonRoot38 φ w)
      (a5LogQuotient38 φ z * (discrim φ z + canonRoot38 φ z)) z := by
  have hd := (analyticOnNhd_discrim_z φ z (mem_univ _)).differentiableAt.hasDerivAt
  have hrA : AnalyticAt ℂ (canonRoot38 φ) z :=
    AnalyticAt.comp (g := fun p : PotPair × ℂ => canonRoot38 p.1 p.2)
      (f := fun w : ℂ => (φ, w)) (canonRoot_analytic38 _ ⟨hφ, hz⟩)
      (analyticAt_const.prod analyticAt_id)
  have hr := hrA.differentiableAt.hasDerivAt
  have he : (fun w => canonRoot38 φ w ^ 2) =ᶠ[𝓝 z]
      (fun w => discrim φ w ^ 2 - 4) := by
    filter_upwards [(isOpen_actionCutDomain38 φ hφ).mem_nhds hz] with w hw
    exact (canonRoot_sq38 φ hφ w hw).trans (perChar_eq φ w)
  have hsq := ((hr.pow 2).congr_of_eventuallyEq he.symm).unique
    ((hd.pow 2).sub_const 4)
  apply (hd.add hr).congr_deriv
  unfold a5LogQuotient38
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff (canonRoot_ne_zero38 φ hφ z hz)).2
  have hsimpl : (deriv (discrim φ) z + deriv (canonRoot38 φ) z) * canonRoot38 φ z =
      deriv (discrim φ) z * (discrim φ z + canonRoot38 φ z) := by
    linear_combination hsq / 2
  exact hsimpl

theorem a5FixedPeriod_exp38 (φ : PotPair) (hφ : φ ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hf : IsolatingFamily38 φ C R) (n : ℤ) :
    CircleIntegrable (a5LogQuotient38 φ) (C n) (R n) ∧
      Complex.exp (circleIntegral (a5LogQuotient38 φ) (C n) (R n)) = 1 := by
  have hr := isolating_radius_pos38 hf n
  have hs := fixed_sphere_subset φ C R hf n
  have ha := a5LogQuotient_analytic38 φ hφ
  have hi := (ha.continuousOn.mono hs).circleIntegrable hr.le
  let c := circleMap (C n) (R n)
  let g : ℝ → ℂ := fun θ => discrim φ (c θ) + canonRoot38 φ (c θ)
  let h : ℝ → ℂ := fun θ => deriv c θ * a5LogQuotient38 φ (c θ)
  have hc : Continuous c := continuous_circleMap _ _
  have hmem : ∀ θ : ℝ, c θ ∈ actionCutDomain38 φ :=
    fun θ => hs (circleMap_mem_sphere _ hr.le θ)
  have hq : Continuous (fun θ => a5LogQuotient38 φ (c θ)) := by
    exact continuous_iff_continuousAt.mpr (fun θ =>
      (ha _ (hmem θ)).continuousAt.comp (hc.continuousAt))
  have hv : Continuous (deriv c) := by
    have he : deriv c = fun θ => circleMap 0 (R n) θ * Complex.I :=
      funext (fun θ => deriv_circleMap (C n) (R n) θ)
    rw [he]
    fun_prop
  have hh : Continuous h := hv.mul hq
  have hg : ∀ θ : ℝ, HasDerivAt g (h θ * g θ) θ := by
    intro θ
    have hd := (a5DeltaPlusRoot_hasDeriv38 φ hφ (c θ) (hmem θ)).scomp θ
      (hasDerivAt_circleMap (C n) (R n) θ)
    apply hd.congr_deriv
    dsimp only [g, h]
    rw [show deriv c θ = circleMap 0 (R n) θ * Complex.I from deriv_circleMap (C n) (R n) θ]
    simp only [smul_eq_mul]
    ring
  have hclosed : g (2 * Real.pi) = g 0 := by
    have hcperiod := periodic_circleMap (C n) (R n) 0
    have he : c (2 * Real.pi) = c 0 := by simpa only [zero_add] using hcperiod
    dsimp [g]
    rw [he]
  have h0 : g 0 ≠ 0 := a5DeltaPlusRoot_ne_zero38 φ hφ _ (hmem 0)
  have hexp := NlsGge.Analysis.NonvanishingLoop.exp_integral_eq_one_of_closed_logarithmic_ODE
    g h (2 * Real.pi) hh hg hclosed h0
  refine ⟨hi, ?_⟩
  simpa only [circleIntegral, h, smul_eq_mul] using hexp.2

theorem a5FixedPeriod_agreement38 (φ : PotPair) (hφ : φ ∈ gkW)
    (C0 C1 : ℤ → ℂ) (R0 R1 : ℤ → ℝ)
    (hf0 : IsolatingFamily38 φ C0 R0) (hf1 : IsolatingFamily38 φ C1 R1) (n : ℤ) :
    circleIntegral (a5LogQuotient38 φ) (C0 n) (R0 n) =
      circleIntegral (a5LogQuotient38 φ) (C1 n) (R1 n) := by
  exact (NlsGge.Analysis.circleIntegral_eq_of_affine_circle_homotopy
    (isOpen_actionCutDomain38 φ hφ) (a5LogQuotient_analytic38 φ hφ)
    (isolating_radius_pos38 hf0 n) (isolating_radius_pos38 hf1 n)
    (fun t ht => action_contour_sphere_subset38 φ C0 C1 R0 R1 hf0 hf1 n t ht)).2.2

theorem a5Period_analytic38 (n : ℤ) :
    AnalyticOnNhd ℂ (fun φ => a5Period38 φ n) gkW := by
  intro φ hφ
  obtain ⟨V, hV, hVW, hVo, _, C, R, hf⟩ := local_isolatingFamily φ hφ
  have hφV := mem_of_mem_nhds hV
  have hjoint : AnalyticOnNhd ℂ (Function.uncurry a5LogQuotient38)
      (V ×ˢ sphere (C n) (R n)) := by
    intro p hp
    exact a5LogQuotient_joint_analytic38 p
      ⟨hVW hp.1, fixed_sphere_subset p.1 C R (hf p.1 hp.1) n hp.2⟩
  have h := Lib.parametricCircleAnalytic38 PotPair V (C n) (R n)
    a5LogQuotient38 hVo (isolating_radius_pos38 (hf φ hφV) n) hjoint
  apply (h.2 φ hφV).congr
  filter_upwards [hV] with ψ hψ
  exact (a5FixedPeriod_agreement38 ψ (hVW hψ) (discC ψ) C (discR ψ) R
    (isolating_family38 ψ (hVW hψ)) (hf ψ hψ) n).symm

theorem a5Period_exp38 (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) :
    Complex.exp (a5Period38 φ n) = 1 :=
  (a5FixedPeriod_exp38 φ hφ (discC φ) (discR φ) (isolating_family38 φ hφ) n).2

theorem a5Period_free38 (n : ℤ) : a5Period38 0 n = 0 := by
  have hf := isolating_family38 (0 : PotPair) free_mem_gkW
  have hr := isolating_radius_pos38 hf n
  have he : EqOn (a5LogQuotient38 0) (fun _ : ℂ => -Complex.I)
      (sphere (discC 0 n) (discR 0 n)) := by
    intro z hz
    have hoff := fixed_sphere_subset 0 (discC 0) (discR 0) hf n hz
    have hd := free_discrim_hasDeriv z
    have hrz := canonRoot_free38 z hoff
    have hne := canonRoot_ne_zero38 0 free_mem_gkW z hoff
    unfold a5LogQuotient38
    rw [hd.deriv]
    apply (div_eq_iff hne).2
    rw [hrz]
    linear_combination -(2 * Complex.sin z) * Complex.I_sq
  unfold a5Period38
  rw [circleIntegral.integral_congr hr.le he]
  exact Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le
    (s := (∅ : Set ℂ)) countable_empty continuousOn_const
    (fun z _ => (analyticAt_const (v := -Complex.I)).differentiableAt)

theorem a5Period_zero38 (n : ℤ) : ∀ φ ∈ gkW, a5Period38 φ n = 0 := by
  apply (a5Period_analytic38 n).eqOn_of_preconnected_of_eventuallyEq
    analyticOnNhd_const isPreconnected_gkW free_mem_gkW
  have hcont := ((a5Period_analytic38 n) 0 free_mem_gkW).continuousAt
  have him : ContinuousAt (fun φ : PotPair => (a5Period38 φ n).im) 0 :=
    Complex.continuous_im.continuousAt.comp' hcont
  have hevt : ∀ᶠ φ in 𝓝 (0 : PotPair),
      -Real.pi < (a5Period38 φ n).im ∧ (a5Period38 φ n).im < Real.pi := by
    have hbounds : (a5Period38 (0 : PotPair) n).im ∈ Ioo (-Real.pi) Real.pi := by
      rw [a5Period_free38]
      exact ⟨by simpa only [Complex.zero_im] using neg_lt_zero.mpr Real.pi_pos,
        by simpa only [Complex.zero_im] using Real.pi_pos⟩
    exact him.eventually (Ioo_mem_nhds hbounds.1 hbounds.2)
  filter_upwards [isOpen_gkW.mem_nhds free_mem_gkW, hevt] with φ hφ hb
  exact Complex.exp_inj_of_neg_pi_lt_of_le_pi hb.1 hb.2.le
    (by simpa only [Complex.zero_im] using neg_lt_zero.mpr Real.pi_pos)
    (by simpa only [Complex.zero_im] using Real.pi_pos.le)
    ((a5Period_exp38 φ hφ n).trans Complex.exp_zero.symm)

theorem a5FixedPeriod_zero38 (φ : PotPair) (hφ : φ ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hf : IsolatingFamily38 φ C R) (n : ℤ) :
    CircleIntegrable (a5LogQuotient38 φ) (C n) (R n) ∧
      circleIntegral (a5LogQuotient38 φ) (C n) (R n) = 0 := by
  refine ⟨(a5FixedPeriod_exp38 φ hφ C R hf n).1, ?_⟩
  exact (a5FixedPeriod_agreement38 φ hφ C (discC φ) R (discR φ)
    hf (isolating_family38 φ hφ) n).trans (a5Period_zero38 n φ hφ)

end
end NlsGge.GK38
