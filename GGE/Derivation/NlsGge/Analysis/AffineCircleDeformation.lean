import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic.Ring

/-! Affine deformation of oriented circle integrals on an open complex domain.
The proof uses only the traced circles; its domain may contain holes.
Transported from the independently reviewed, pinned Trellis A1 package. -/

set_option autoImplicit false

namespace NlsGge.Analysis
namespace AffineCircleDeformation

-- [TABLET NODE: AffineCircleCenter]
noncomputable def AffineCircleCenter (c0 c1 : ℂ) (t : ℝ) : ℂ :=
-- BODY
  (1 - t) • c0 + t • c1

-- [TABLET NODE: AffineCircleRadius]
def AffineCircleRadius (r0 r1 t : ℝ) : ℝ :=
-- BODY
  (1 - t) * r0 + t * r1

-- [TABLET NODE: AffineCirclePoint]
noncomputable def AffineCirclePoint (c0 c1 : ℂ) (r0 r1 t θ : ℝ) : ℂ :=
-- BODY
  circleMap (AffineCircleCenter c0 c1 t) (AffineCircleRadius r0 r1 t) θ

-- [TABLET NODE: AffineCircleGeometry]
theorem AffineCircleGeometry (c0 c1 : ℂ) (r0 r1 : ℝ) :
    Continuous (fun p : ℝ × ℝ => AffineCirclePoint c0 c1 r0 r1 p.1 p.2) ∧
    IsCompact ((fun p : ℝ × ℝ => AffineCirclePoint c0 c1 r0 r1 p.1 p.2) ''
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi))) := by
-- BODY
  have hz : Continuous (fun p : ℝ × ℝ => AffineCirclePoint c0 c1 r0 r1 p.1 p.2) := by
    unfold AffineCirclePoint AffineCircleCenter AffineCircleRadius circleMap
    fun_prop
  exact ⟨hz, (isCompact_Icc.prod isCompact_Icc).image hz⟩

-- [TABLET NODE: AffineCircleRadiusPositive]
theorem AffineCircleRadiusPositive {r0 r1 t : ℝ}
    (hr0 : 0 < r0) (hr1 : 0 < r1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    0 < AffineCircleRadius r0 r1 t := by
-- BODY
  unfold AffineCircleRadius
  rcases lt_or_eq_of_le ht.2 with hlt | heq
  · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hlt) hr0)
      (mul_nonneg ht.1 hr1.le)
  · simpa [heq] using hr1

-- [TABLET NODE: AffineCircleSphereMembership]
theorem AffineCircleSphereMembership {c0 c1 : ℂ} {r0 r1 : ℝ}
    (hr0 : 0 < r0) (hr1 : 0 < r1) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ θ : ℝ,
      AffineCirclePoint c0 c1 r0 r1 t θ ∈
        Metric.sphere (AffineCircleCenter c0 c1 t) (AffineCircleRadius r0 r1 t) := by
-- BODY
  intro t ht θ
  exact circleMap_mem_sphere (AffineCircleCenter c0 c1 t)
    (AffineCircleRadiusPositive hr0 hr1 ht).le θ

-- [TABLET NODE: AffineCircleDomainTube]
theorem AffineCircleDomainTube {Ω : Set ℂ} {c0 c1 : ℂ} {r0 r1 : ℝ}
    (hΩ : IsOpen Ω) (hr0 : 0 < r0) (hr1 : 0 < r1)
    (hsphere : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Metric.sphere (AffineCircleCenter c0 c1 t) (AffineCircleRadius r0 r1 t) ⊆ Ω) :
    ∃ U V : Set ℝ, IsOpen U ∧ IsOpen V ∧ Set.Icc (0 : ℝ) 1 ⊆ U ∧
      Set.Icc (0 : ℝ) (2 * Real.pi) ⊆ V ∧
      ∀ t ∈ U, ∀ θ ∈ V, AffineCirclePoint c0 c1 r0 r1 t θ ∈ Ω := by
-- BODY
  obtain ⟨U, V, hU, hV, htU, hθV, hUV⟩ :=
    generalized_tube_lemma (s := Set.Icc (0 : ℝ) 1) isCompact_Icc
      (t := Set.Icc (0 : ℝ) (2 * Real.pi)) isCompact_Icc
      (hΩ.preimage (AffineCircleGeometry c0 c1 r0 r1).1)
      (by
        rintro ⟨t, θ⟩ ⟨ht, _⟩
        exact hsphere t ht (AffineCircleSphereMembership hr0 hr1 t ht θ))
  exact ⟨U, V, hU, hV, htU, hθV,
    fun t ht θ hθ => hUV (show (t, θ) ∈ U ×ˢ V from ⟨ht, hθ⟩)⟩

-- [TABLET NODE: AffineCircleIntegrability]
theorem AffineCircleIntegrability {Ω : Set ℂ} {f : ℂ → ℂ}
    {c0 c1 : ℂ} {r0 r1 : ℝ} (hf : AnalyticOnNhd ℂ f Ω)
    (hr0 : 0 < r0) (hr1 : 0 < r1)
    (hsphere : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Metric.sphere (AffineCircleCenter c0 c1 t) (AffineCircleRadius r0 r1 t) ⊆ Ω) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      CircleIntegrable f (AffineCircleCenter c0 c1 t) (AffineCircleRadius r0 r1 t) := by
-- BODY
  intro t ht
  exact (hf.continuousOn.mono (hsphere t ht)).circleIntegrable
    (AffineCircleRadiusPositive hr0 hr1 ht).le

-- [TABLET NODE: AffineCirclePullback]
noncomputable def AffineCirclePullback (f : ℂ → ℂ) (c0 c1 : ℂ)
    (r0 r1 t θ : ℝ) : ℂ :=
-- BODY
  Complex.I * (AffineCircleRadius r0 r1 t : ℂ) * circleMap 0 1 θ *
    f (AffineCirclePoint c0 c1 r0 r1 t θ)

open MeasureTheory

-- [TABLET NODE: AffineCirclePullbackIntegral]
theorem AffineCirclePullbackIntegral {f : ℂ → ℂ} {c0 c1 : ℂ} {r0 r1 t : ℝ}
    (hcircle : CircleIntegrable f (AffineCircleCenter c0 c1 t) (AffineCircleRadius r0 r1 t)) :
    IntervalIntegrable (AffineCirclePullback f c0 c1 r0 r1 t) volume 0 (2 * Real.pi) ∧
    (∫ θ in (0 : ℝ)..2 * Real.pi, AffineCirclePullback f c0 c1 r0 r1 t θ) =
      circleIntegral f (AffineCircleCenter c0 c1 t) (AffineCircleRadius r0 r1 t) := by
-- BODY
  have hform :
      (fun θ : ℝ => deriv (circleMap (AffineCircleCenter c0 c1 t)
        (AffineCircleRadius r0 r1 t)) θ •
        f (circleMap (AffineCircleCenter c0 c1 t) (AffineCircleRadius r0 r1 t) θ)) =
      AffineCirclePullback f c0 c1 r0 r1 t := by
    funext θ
    simp [AffineCirclePullback, AffineCirclePoint, deriv_circleMap, circleMap,
      smul_eq_mul, mul_assoc, mul_comm, mul_left_comm]
  constructor
  · rw [← hform]
    exact hcircle.out
  · unfold circleIntegral
    rw [hform]

-- [TABLET NODE: AffineCircleVelocity]
noncomputable def AffineCircleVelocity (c0 c1 : ℂ) (r0 r1 θ : ℝ) : ℂ :=
-- BODY
  c1 - c0 + ((r1 - r0 : ℝ) : ℂ) * circleMap 0 1 θ

-- [TABLET NODE: AffineCircleCommonDerivative]
noncomputable def AffineCircleCommonDerivative (f : ℂ → ℂ) (c0 c1 : ℂ)
    (r0 r1 t θ : ℝ) : ℂ :=
-- BODY
  Complex.I * ((r1 - r0 : ℝ) : ℂ) * circleMap 0 1 θ *
      f (AffineCirclePoint c0 c1 r0 r1 t θ) +
    Complex.I * (AffineCircleRadius r0 r1 t : ℂ) * circleMap 0 1 θ *
      (deriv f (AffineCirclePoint c0 c1 r0 r1 t θ) *
        AffineCircleVelocity c0 c1 r0 r1 θ)

open MeasureTheory

-- [TABLET NODE: AffineCircleRegularity]
theorem AffineCircleRegularity {Ω : Set ℂ} {f : ℂ → ℂ}
    {c0 c1 : ℂ} {r0 r1 : ℝ} {U V : Set ℝ}
    (hf : AnalyticOnNhd ℂ f Ω) (hθV : Set.Icc (0 : ℝ) (2 * Real.pi) ⊆ V)
    (hUV : ∀ t ∈ U, ∀ θ ∈ V, AffineCirclePoint c0 c1 r0 r1 t θ ∈ Ω) :
    ContinuousOn (fun p : ℝ × ℝ => AffineCirclePullback f c0 c1 r0 r1 p.1 p.2)
      (U ×ˢ V) ∧
    ContinuousOn (fun p : ℝ × ℝ => AffineCircleCommonDerivative f c0 c1 r0 r1 p.1 p.2)
      (U ×ˢ V) ∧
    ∀ t ∈ U,
      IntervalIntegrable (AffineCirclePullback f c0 c1 r0 r1 t) volume 0 (2 * Real.pi) ∧
      IntervalIntegrable (AffineCircleCommonDerivative f c0 c1 r0 r1 t) volume 0
        (2 * Real.pi) := by
-- BODY
  have hz := (AffineCircleGeometry c0 c1 r0 r1).1
  have hF : ContinuousOn (fun p : ℝ × ℝ => f (AffineCirclePoint c0 c1 r0 r1 p.1 p.2))
      (U ×ˢ V) :=
    hf.continuousOn.comp hz.continuousOn (fun p hp => hUV p.1 hp.1 p.2 hp.2)
  have hF' : ContinuousOn (fun p : ℝ × ℝ => deriv f (AffineCirclePoint c0 c1 r0 r1 p.1 p.2))
      (U ×ˢ V) :=
    hf.deriv.continuousOn.comp hz.continuousOn (fun p hp => hUV p.1 hp.1 p.2 hp.2)
  have hr : Continuous (fun p : ℝ × ℝ => (AffineCircleRadius r0 r1 p.1 : ℂ)) := by
    unfold AffineCircleRadius
    fun_prop
  have hq : Continuous (fun p : ℝ × ℝ => circleMap 0 1 p.2) :=
    (continuous_circleMap 0 1).comp continuous_snd
  have hv : Continuous (fun p : ℝ × ℝ => AffineCircleVelocity c0 c1 r0 r1 p.2) := by
    unfold AffineCircleVelocity
    fun_prop
  have hH : ContinuousOn (fun p : ℝ × ℝ => AffineCirclePullback f c0 c1 r0 r1 p.1 p.2)
      (U ×ˢ V) :=
    ((continuousOn_const.mul hr.continuousOn).mul hq.continuousOn).mul hF
  have hD : ContinuousOn (fun p : ℝ × ℝ => AffineCircleCommonDerivative f c0 c1 r0 r1 p.1 p.2)
      (U ×ˢ V) :=
    (((continuousOn_const.mul continuousOn_const).mul hq.continuousOn).mul hF).add
      (((continuousOn_const.mul hr.continuousOn).mul hq.continuousOn).mul
        (hF'.mul hv.continuousOn))
  refine ⟨hH, hD, ?_⟩
  intro t ht
  have hslice : Continuous (fun θ : ℝ => (t, θ)) := continuous_const.prodMk continuous_id
  have hmaps : Set.MapsTo (fun θ : ℝ => (t, θ)) (Set.Icc (0 : ℝ) (2 * Real.pi)) (U ×ˢ V) :=
    fun θ hθ => ⟨ht, hθV hθ⟩
  have hsH : ContinuousOn (AffineCirclePullback f c0 c1 r0 r1 t)
      (Set.uIcc (0 : ℝ) (2 * Real.pi)) := by
    simpa only [Set.uIcc_of_le Real.two_pi_pos.le, Function.comp_def] using
      hH.comp hslice.continuousOn hmaps
  have hsD : ContinuousOn (AffineCircleCommonDerivative f c0 c1 r0 r1 t)
      (Set.uIcc (0 : ℝ) (2 * Real.pi)) := by
    simpa only [Set.uIcc_of_le Real.two_pi_pos.le, Function.comp_def] using
      hD.comp hslice.continuousOn hmaps
  exact ⟨hsH.intervalIntegrable, hsD.intervalIntegrable⟩

-- [TABLET NODE: AffineCircleCurveDerivatives]
theorem AffineCircleCurveDerivatives (c0 c1 : ℂ) (r0 r1 t θ : ℝ) :
    HasDerivAt (fun s : ℝ => AffineCirclePoint c0 c1 r0 r1 s θ)
      (AffineCircleVelocity c0 c1 r0 r1 θ) t ∧
    HasDerivAt (AffineCirclePoint c0 c1 r0 r1 t)
      (Complex.I * (AffineCircleRadius r0 r1 t : ℂ) * circleMap 0 1 θ) θ ∧
    HasDerivAt (AffineCircleVelocity c0 c1 r0 r1)
      (Complex.I * ((r1 - r0 : ℝ) : ℂ) * circleMap 0 1 θ) θ := by
-- BODY
  have hc : HasDerivAt (AffineCircleCenter c0 c1) (c1 - c0) t := by
    convert (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).smul_const c0).add
      ((hasDerivAt_id t).smul_const c1) using 1
    · rfl
    · simp [sub_eq_add_neg, add_comm]
  have hr : HasDerivAt (AffineCircleRadius r0 r1) (r1 - r0) t := by
    convert (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).mul_const r0).add
      ((hasDerivAt_id t).mul_const r1) using 1
    · rfl
    · simp [sub_eq_add_neg, add_comm]
  have ht : HasDerivAt (fun s : ℝ => AffineCirclePoint c0 c1 r0 r1 s θ)
      (AffineCircleVelocity c0 c1 r0 r1 θ) t := by
    convert hc.add (hr.ofReal_comp.mul_const (circleMap 0 1 θ)) using 1
    · funext s
      simp [AffineCirclePoint, circleMap]
    · simp [AffineCircleVelocity, circleMap]
  have hθ : HasDerivAt (AffineCirclePoint c0 c1 r0 r1 t)
      (Complex.I * (AffineCircleRadius r0 r1 t : ℂ) * circleMap 0 1 θ) θ := by
    convert hasDerivAt_circleMap (AffineCircleCenter c0 c1 t)
      (AffineCircleRadius r0 r1 t) θ using 1
    · rfl
    · simp [circleMap, mul_comm, mul_left_comm]
  have hv : HasDerivAt (AffineCircleVelocity c0 c1 r0 r1)
      (Complex.I * ((r1 - r0 : ℝ) : ℂ) * circleMap 0 1 θ) θ := by
    convert ((hasDerivAt_circleMap 0 1 θ).const_mul
      ((r1 - r0 : ℝ) : ℂ)).const_add (c1 - c0) using 1
    · funext α
      simp [AffineCircleVelocity]
    · simp [mul_comm, mul_left_comm, mul_assoc]
  exact ⟨ht, hθ, hv⟩

-- [TABLET NODE: AffineCircleAngularPrimitive]
noncomputable def AffineCircleAngularPrimitive (f : ℂ → ℂ) (c0 c1 : ℂ)
    (r0 r1 t θ : ℝ) : ℂ :=
-- BODY
  f (AffineCirclePoint c0 c1 r0 r1 t θ) * AffineCircleVelocity c0 c1 r0 r1 θ

-- [TABLET NODE: AffineCircleMixedDerivative]
theorem AffineCircleMixedDerivative {f : ℂ → ℂ} {c0 c1 : ℂ} {r0 r1 t θ : ℝ}
    (hf : AnalyticAt ℂ f (AffineCirclePoint c0 c1 r0 r1 t θ)) :
    HasDerivAt (fun s : ℝ => AffineCirclePullback f c0 c1 r0 r1 s θ)
      (AffineCircleCommonDerivative f c0 c1 r0 r1 t θ) t ∧
    HasDerivAt (AffineCircleAngularPrimitive f c0 c1 r0 r1 t)
      (AffineCircleCommonDerivative f c0 c1 r0 r1 t θ) θ := by
-- BODY
  obtain ⟨hzT, hzθ, hv⟩ := AffineCircleCurveDerivatives c0 c1 r0 r1 t θ
  have hft := hf.differentiableAt.hasDerivAt.scomp t hzT
  have hfθ := hf.differentiableAt.hasDerivAt.scomp θ hzθ
  simp only [smul_eq_mul, Function.comp_def] at hft hfθ
  have hr : HasDerivAt (AffineCircleRadius r0 r1) (r1 - r0) t := by
    convert (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).mul_const r0).add
      ((hasDerivAt_id t).mul_const r1) using 1
    · rfl
    · simp [sub_eq_add_neg, add_comm]
  have hcoeff := (hr.ofReal_comp.const_mul Complex.I).mul_const (circleMap 0 1 θ)
  constructor
  · convert hcoeff.mul hft using 1
    · rfl
    · dsimp only [AffineCircleCommonDerivative]
      ring
  · convert hfθ.mul hv using 1
    · rfl
    · dsimp only [AffineCircleCommonDerivative]
      ring

-- [TABLET NODE: AffineCirclePeriodicity]
theorem AffineCirclePeriodicity (f : ℂ → ℂ) (c0 c1 : ℂ) (r0 r1 t : ℝ) :
    Function.Periodic (AffineCircleAngularPrimitive f c0 c1 r0 r1 t) (2 * Real.pi) := by
-- BODY
  intro θ
  simp only [AffineCircleAngularPrimitive, AffineCirclePoint, AffineCircleVelocity,
    periodic_circleMap (AffineCircleCenter c0 c1 t) (AffineCircleRadius r0 r1 t) θ,
    periodic_circleMap 0 1 θ]

-- [TABLET NODE: AffineCircleAngularCancellation]
theorem AffineCircleAngularCancellation {Ω : Set ℂ} {f : ℂ → ℂ}
    {c0 c1 : ℂ} {r0 r1 t : ℝ} (hf : AnalyticOnNhd ℂ f Ω)
    (hpath : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      AffineCirclePoint c0 c1 r0 r1 t θ ∈ Ω) :
    (∫ θ in (0 : ℝ)..2 * Real.pi, AffineCircleCommonDerivative f c0 c1 r0 r1 t θ) = 0 := by
-- BODY
  have hint := (AffineCircleRegularity (U := {t})
    (V := Set.Icc (0 : ℝ) (2 * Real.pi)) hf (Set.Subset.refl _)
    (by
      intro s hs θ hθ
      have hst : s = t := hs
      simpa only [hst] using hpath θ hθ)).2.2 t (Set.mem_singleton t)
  have hderiv : ∀ θ ∈ Set.uIcc (0 : ℝ) (2 * Real.pi),
      HasDerivAt (AffineCircleAngularPrimitive f c0 c1 r0 r1 t)
        (AffineCircleCommonDerivative f c0 c1 r0 r1 t θ) θ := by
    intro θ hθ
    rw [Set.uIcc_of_le Real.two_pi_pos.le] at hθ
    exact (AffineCircleMixedDerivative (hf _ (hpath θ hθ))).2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint.2]
  have hp := AffineCirclePeriodicity f c0 c1 r0 r1 t 0
  simp only [zero_add] at hp
  rw [hp, sub_self]

-- [TABLET NODE: AffineCircleLocalBound]
theorem AffineCircleLocalBound {Ω : Set ℂ} {f : ℂ → ℂ}
    {c0 c1 : ℂ} {r0 r1 t0 : ℝ} {U V : Set ℝ}
    (hf : AnalyticOnNhd ℂ f Ω) (hU : IsOpen U) (ht0 : t0 ∈ U)
    (hθV : Set.Icc (0 : ℝ) (2 * Real.pi) ⊆ V)
    (hUV : ∀ t ∈ U, ∀ θ ∈ V, AffineCirclePoint c0 c1 r0 r1 t θ ∈ Ω) :
    ∃ ε B : ℝ, 0 < ε ∧ 0 ≤ B ∧ Metric.closedBall t0 ε ⊆ U ∧
      ∀ s ∈ Metric.closedBall t0 ε, ∀ θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
        ‖AffineCircleCommonDerivative f c0 c1 r0 r1 s θ‖ ≤ B := by
-- BODY
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hU t0 ht0
  have hε : 0 < δ / 2 := half_pos hδ
  have hclosed : Metric.closedBall t0 (δ / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (half_lt_self hδ)).trans hball
  let K : Set (ℝ × ℝ) :=
    Metric.closedBall t0 (δ / 2) ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)
  have hK : IsCompact K := (isCompact_closedBall t0 (δ / 2)).prod isCompact_Icc
  have hKne : K.Nonempty :=
    ⟨(t0, 0), Metric.mem_closedBall_self hε.le, le_rfl, Real.two_pi_pos.le⟩
  have hKUV : K ⊆ U ×ˢ V := fun p hp => ⟨hclosed hp.1, hθV hp.2⟩
  have hD : ContinuousOn
      (fun p : ℝ × ℝ => AffineCircleCommonDerivative f c0 c1 r0 r1 p.1 p.2) K :=
    (AffineCircleRegularity hf hθV hUV).2.1.mono hKUV
  let g : ℝ × ℝ → ℝ :=
    fun p => ‖AffineCircleCommonDerivative f c0 c1 r0 r1 p.1 p.2‖
  have hg : ContinuousOn g K := hD.norm
  obtain ⟨p, hp, hmax⟩ := hK.exists_isMaxOn hKne hg
  refine ⟨δ / 2, g p,
    hε, norm_nonneg _, hclosed, ?_⟩
  intro s hs θ hθ
  have hle : g (s, θ) ≤ g p := hmax (show (s, θ) ∈ K from ⟨hs, hθ⟩)
  exact hle

open MeasureTheory Filter
open scoped Topology

-- [TABLET NODE: AffineCircleParameterDifferentiation]
theorem AffineCircleParameterDifferentiation {Ω : Set ℂ} {f : ℂ → ℂ}
    {c0 c1 : ℂ} {r0 r1 t0 : ℝ} {U V : Set ℝ}
    (hf : AnalyticOnNhd ℂ f Ω) (hU : IsOpen U) (ht0 : t0 ∈ U)
    (hθV : Set.Icc (0 : ℝ) (2 * Real.pi) ⊆ V)
    (hUV : ∀ t ∈ U, ∀ θ ∈ V, AffineCirclePoint c0 c1 r0 r1 t θ ∈ Ω) :
    HasDerivAt
      (fun t : ℝ => ∫ θ in (0 : ℝ)..2 * Real.pi, AffineCirclePullback f c0 c1 r0 r1 t θ)
      (∫ θ in (0 : ℝ)..2 * Real.pi, AffineCircleCommonDerivative f c0 c1 r0 r1 t0 θ) t0 := by
-- BODY
  obtain ⟨ε, B, hε, _, hclosed, hbound⟩ :=
    AffineCircleLocalBound hf hU ht0 hθV hUV
  have hint := (AffineCircleRegularity hf hθV hUV).2.2
  have hmeas : ∀ᶠ s in 𝓝 t0,
      AEStronglyMeasurable (AffineCirclePullback f c0 c1 r0 r1 s)
        (volume.restrict (Set.uIoc (0 : ℝ) (2 * Real.pi))) := by
    filter_upwards [hU.mem_nhds ht0] with s hs
    simpa only [Set.uIoc_of_le Real.two_pi_pos.le] using
      (hint s hs).1.aestronglyMeasurable
  have hθ : ∀ θ ∈ Set.uIoc (0 : ℝ) (2 * Real.pi),
      θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := by
    intro θ h
    rw [Set.uIoc_of_le Real.two_pi_pos.le] at h
    exact ⟨h.1.le, h.2⟩
  have hb : ∀ᵐ θ ∂volume, θ ∈ Set.uIoc (0 : ℝ) (2 * Real.pi) →
      ∀ s ∈ Metric.ball t0 ε,
        ‖AffineCircleCommonDerivative f c0 c1 r0 r1 s θ‖ ≤ B := by
    exact Eventually.of_forall (fun θ h s hs =>
      hbound s (Metric.ball_subset_closedBall hs) θ (hθ θ h))
  have hd : ∀ᵐ θ ∂volume, θ ∈ Set.uIoc (0 : ℝ) (2 * Real.pi) →
      ∀ s ∈ Metric.ball t0 ε,
        HasDerivAt (fun u : ℝ => AffineCirclePullback f c0 c1 r0 r1 u θ)
          (AffineCircleCommonDerivative f c0 c1 r0 r1 s θ) s := by
    exact Eventually.of_forall (fun θ h s hs =>
      (AffineCircleMixedDerivative
        (hf _ (hUV s (hclosed (Metric.ball_subset_closedBall hs)) θ
          (hθV (hθ θ h))))).1)
  have hDmeas : AEStronglyMeasurable
      (AffineCircleCommonDerivative f c0 c1 r0 r1 t0)
      (volume.restrict (Set.uIoc (0 : ℝ) (2 * Real.pi))) := by
    simpa only [Set.uIoc_of_le Real.two_pi_pos.le] using
      (hint t0 ht0).2.aestronglyMeasurable
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds t0 hε) hmeas (hint t0 ht0).1
    hDmeas hb
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => B) volume 0
      (2 * Real.pi)) hd).2

end AffineCircleDeformation

open AffineCircleDeformation in
-- [TABLET NODE: circleIntegral_eq_of_affine_circle_homotopy]
theorem circleIntegral_eq_of_affine_circle_homotopy
    {Ω : Set ℂ} {f : ℂ → ℂ} {c0 c1 : ℂ} {r0 r1 : ℝ}
    (hΩ : IsOpen Ω) (hf : AnalyticOnNhd ℂ f Ω)
    (hr0 : 0 < r0) (hr1 : 0 < r1)
    (hsphere : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Metric.sphere (((1 - t) : ℝ) • c0 + t • c1) ((1 - t) * r0 + t * r1) ⊆ Ω) :
    CircleIntegrable f c0 r0 ∧ CircleIntegrable f c1 r1 ∧
      circleIntegral f c0 r0 = circleIntegral f c1 r1 := by
-- BODY
  have hs : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Metric.sphere (AffineCircleCenter c0 c1 t) (AffineCircleRadius r0 r1 t) ⊆ Ω := hsphere
  have hci := AffineCircleIntegrability hf hr0 hr1 hs
  obtain ⟨U, V, hU, _, htU, hθV, hUV⟩ := AffineCircleDomainTube hΩ hr0 hr1 hs
  let F : ℝ → ℂ := fun t =>
    ∫ θ in (0 : ℝ)..2 * Real.pi, AffineCirclePullback f c0 c1 r0 r1 t θ
  have hd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt F 0 t := by
    intro t ht
    have hdiff := AffineCircleParameterDifferentiation hf hU (htU ht) hθV hUV
    have hzero := AffineCircleAngularCancellation hf
      (fun θ hθ => hUV t (htU ht) θ (hθV hθ))
    simpa only [F, hzero] using hdiff
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hnorm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := F) (f' := fun _ => (0 : ℂ)) (C := 0)
    (fun t ht => (hd t ht).hasDerivWithinAt)
    (by intro t ht; simp) (convex_Icc (0 : ℝ) 1) h0 h1
  have hF : F 0 = F 1 := by
    have hsub : F 1 - F 0 = 0 := norm_eq_zero.mp
      (le_antisymm (by simpa only [zero_mul] using hnorm) (norm_nonneg _))
    exact (sub_eq_zero.mp hsub).symm
  have hc0 : CircleIntegrable f c0 r0 := by
    simpa [AffineCircleCenter, AffineCircleRadius] using hci 0 h0
  have hc1 : CircleIntegrable f c1 r1 := by
    simpa [AffineCircleCenter, AffineCircleRadius] using hci 1 h1
  have hb0 : F 0 = circleIntegral f c0 r0 := by
    simpa [F, AffineCircleCenter, AffineCircleRadius] using
      (AffineCirclePullbackIntegral (hci 0 h0)).2
  have hb1 : F 1 = circleIntegral f c1 r1 := by
    simpa [F, AffineCircleCenter, AffineCircleRadius] using
      (AffineCirclePullbackIntegral (hci 1 h1)).2
  exact ⟨hc0, hc1, hb0.symm.trans (hF.trans hb1)⟩

end NlsGge.Analysis
