import NlsGge.GK38.Lib.WeaklyAnalytic
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity

/-!
Real-interval integration with complex normed-space parameters.

The real integration variable is never treated as a complex analytic variable.
Local domination is derived from joint continuity over compact real fibers;
the parameter neighborhood itself is not asserted to be compact. Taking the
parameter space to be a potential/spectral product gives neighborhoods local
to an interior spectral basepoint, without a bound on the entire open disc.

This is conditional supporting infrastructure. Its hypotheses are pointwise
complex derivatives and joint continuity of the density and derivative density,
not analyticity of either integral. Root owns compilation and integration.
-/

set_option autoImplicit false

open Set Metric Filter MeasureTheory
open scoped Topology Interval

namespace NlsGge.GK38.Lib
noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

omit [NormedSpace ℂ H] in
private theorem intervalParam_sliceContinuous38
    {Y : Type*} [NormedAddCommGroup Y]
    {V : Set H} {G : H → ℝ → Y}
    (hG : ∀ x ∈ V, ∀ t : ℝ,
      ContinuousAt (Function.uncurry G) (x, t))
    {x : H} (hx : x ∈ V) : Continuous (G x) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hp : ContinuousAt (fun u : ℝ => (x, u)) t := by fun_prop
  exact (hG x hx t).comp hp

/-- One parameter neighborhood controls a continuous density over a compact
real interval. The normed parameter space need not be finite dimensional. -/
theorem parametricInterval_common_bound38
    {Y : Type*} [NormedAddCommGroup Y]
    {V : Set H} {G : H → ℝ → Y}
    (hV : IsOpen V)
    (hG : ∀ x ∈ V, ∀ t : ℝ,
      ContinuousAt (Function.uncurry G) (x, t))
    (a b : ℝ) {x₀ : H} (hx₀ : x₀ ∈ V) :
    ∃ ε > 0, ∃ B : ℝ, 0 ≤ B ∧ ball x₀ ε ⊆ V ∧
      ∀ x ∈ ball x₀ ε, ∀ t ∈ uIcc a b, ‖G x t‖ ≤ B := by
  have hc : Continuous (G x₀) := intervalParam_sliceContinuous38 hG hx₀
  obtain ⟨A, hA⟩ :=
    (isCompact_uIcc : IsCompact (uIcc a b)).exists_bound_of_continuousOn hc.continuousOn
  let B : ℝ := max 0 A + 1
  have hAB : A + 1 ≤ B := by
    dsimp [B]
    simpa only [add_comm] using (add_le_add_right (le_max_right 0 A) 1)
  have hlocal : ∀ t ∈ uIcc a b,
      ∀ᶠ p : H × ℝ in 𝓝 (x₀, t), ‖G p.1 p.2‖ ≤ B := by
    intro t ht
    have he := (hG x₀ hx₀ t).norm.eventually
      (gt_mem_nhds (lt_add_one ‖G x₀ t‖))
    filter_upwards [he] with p hp
    change ‖G p.1 p.2‖ < ‖G x₀ t‖ + 1 at hp
    calc
      ‖G p.1 p.2‖ ≤ ‖G x₀ t‖ + 1 := hp.le
      _ ≤ A + 1 := by
        simpa only [add_comm] using (add_le_add_right (hA t ht) 1)
      _ ≤ B := hAB
  have hu := (isCompact_uIcc : IsCompact (uIcc a b)).eventually_forall_of_forall_eventually
      (P := fun x t => ‖G x t‖ ≤ B) hlocal
  obtain ⟨ε, hε, he⟩ :=
    Metric.eventually_nhds_iff_ball.mp (hu.and (hV.mem_nhds hx₀))
  refine ⟨ε, hε, B, ?_, fun x hx => (he x hx).2, ?_⟩
  · dsimp [B]
    positivity
  · intro x hx t ht
    exact (he x hx).1 t ht

/-- Complex Fréchet differentiation of an integral over a real interval.
Measurability, both genuine integrabilities and local domination are derived
from the displayed continuity assumptions before the derivative identity is used. -/
theorem parametricInterval_hasFDerivAt38
    {V : Set H} {F : H → ℝ → ℂ} {F' : H → ℝ → H →L[ℂ] ℂ}
    (hV : IsOpen V)
    (hF : ∀ x ∈ V, ∀ t : ℝ,
      ContinuousAt (Function.uncurry F) (x, t))
    (hF' : ∀ x ∈ V, ∀ t : ℝ,
      ContinuousAt (Function.uncurry F') (x, t))
    (hder : ∀ x ∈ V, ∀ t : ℝ,
      HasFDerivAt (fun y => F y t) (F' x t) x)
    (a b : ℝ) {x₀ : H} (hx₀ : x₀ ∈ V) :
    IntervalIntegrable (F x₀) volume a b ∧
      IntervalIntegrable (F' x₀) volume a b ∧
      HasFDerivAt (fun x => ∫ t in a..b, F x t)
        (∫ t in a..b, F' x₀ t) x₀ := by
  have hFc : ∀ x ∈ V, Continuous (F x) :=
    fun x hx => intervalParam_sliceContinuous38 hF hx
  have hF'c : ∀ x ∈ V, Continuous (F' x) :=
    fun x hx => intervalParam_sliceContinuous38 hF' hx
  have hi : IntervalIntegrable (F x₀) volume a b :=
    (hFc x₀ hx₀).intervalIntegrable a b
  have hi' : IntervalIntegrable (F' x₀) volume a b :=
    (hF'c x₀ hx₀).intervalIntegrable a b
  obtain ⟨ε, hε, B, _hB, hsub, hb⟩ :=
    parametricInterval_common_bound38 hV hF' a b hx₀
  have hm : ∀ᶠ x in 𝓝 x₀,
      AEStronglyMeasurable (F x) (volume.restrict (Ι a b)) := by
    filter_upwards [ball_mem_nhds x₀ hε] with x hx
    exact ((hFc x (hsub hx)).intervalIntegrable a b).aestronglyMeasurable_restrict_uIoc
  have hm' : AEStronglyMeasurable (F' x₀) (volume.restrict (Ι a b)) :=
    hi'.aestronglyMeasurable_restrict_uIoc
  have hbound : ∀ᵐ t ∂volume, t ∈ Ι a b →
      ∀ x ∈ ball x₀ ε, ‖F' x t‖ ≤ B :=
    Filter.Eventually.of_forall
      (fun t ht x hx => hb x hx t (uIoc_subset_uIcc ht))
  have hbi : IntervalIntegrable (fun _t : ℝ => B) volume a b :=
    (continuous_const : Continuous (fun _t : ℝ => B)).intervalIntegrable a b
  have hd : ∀ᵐ t ∂volume, t ∈ Ι a b → ∀ x ∈ ball x₀ ε,
      HasFDerivAt (fun y => F y t) (F' x t) x :=
    Filter.Eventually.of_forall (fun t _ht x hx => hder x (hsub hx) t)
  refine ⟨hi, hi', ?_⟩
  exact intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (𝕜 := ℂ) (s := ball x₀ ε) (bound := fun _t : ℝ => B)
    (ball_mem_nhds x₀ hε) hm hi hm' hbound hbi hd

/-- Analyticity in a complex normed parameter of a real-interval integral.
There is no analyticity assumption in the real integration variable. -/
theorem parametricInterval_analytic38
    {V : Set H} {F : H → ℝ → ℂ} {F' : H → ℝ → H →L[ℂ] ℂ}
    (hV : IsOpen V)
    (hF : ∀ x ∈ V, ∀ t : ℝ,
      ContinuousAt (Function.uncurry F) (x, t))
    (hF' : ∀ x ∈ V, ∀ t : ℝ,
      ContinuousAt (Function.uncurry F') (x, t))
    (hder : ∀ x ∈ V, ∀ t : ℝ,
      HasFDerivAt (fun y => F y t) (F' x t) x)
    (a b : ℝ) :
    AnalyticOnNhd ℂ (fun x => ∫ t in a..b, F x t) V := by
  apply analyticOnNhd_of_differentiableOn hV
  intro x hx
  exact ((parametricInterval_hasFDerivAt38 hV hF hF' hder a b hx).2.2).differentiableAt.differentiableWithinAt

/-- Continuity of a moving real primitive in its parameter subtype and real
upper endpoint. This also applies to continuous-linear-map valued densities. -/
theorem parametricPrimitive_continuous38
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {V : Set H} {G : H → ℝ → Y}
    (hG : ∀ x ∈ V, ∀ t : ℝ,
      ContinuousAt (Function.uncurry G) (x, t))
    (a : ℝ) :
    Continuous (fun p : V × ℝ => ∫ t in a..p.2, G p.1.val t) := by
  apply intervalIntegral.continuous_parametric_primitive_of_continuous
    (f := fun (x : V) (t : ℝ) => G x.val t) (a₀ := a) (μ := volume)
  change Continuous (fun p : V × ℝ => G p.1.val p.2)
  apply continuous_iff_continuousAt.mpr
  intro p
  have hp : ContinuousAt (fun q : V × ℝ => (q.1.val, q.2)) p := by fun_prop
  exact ContinuousAt.comp
    (f := fun q : V × ℝ => (q.1.val, q.2))
    (g := Function.uncurry G) (x := p)
    (hG p.1.val p.1.property p.2) hp

/-- The moving primitive is jointly continuous on the ambient open parameter
domain, not only on its subtype. This is the continuity needed to apply the
interval theorem again to a nested outer density. -/
theorem parametricPrimitive_continuousAt38
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {V : Set H} {G : H → ℝ → Y}
    (hV : IsOpen V)
    (hG : ∀ x ∈ V, ∀ t : ℝ,
      ContinuousAt (Function.uncurry G) (x, t))
    (a : ℝ) {x : H} (hx : x ∈ V) (b : ℝ) :
    ContinuousAt (fun p : H × ℝ => ∫ t in a..p.2, G p.1 t) (x, b) := by
  have hc : Continuous (fun p : V × ℝ => ∫ t in a..p.2, G p.1.val t) :=
    parametricPrimitive_continuous38 hG a
  have hm : Continuous (fun p : (V ×ˢ (univ : Set ℝ)) =>
      ((⟨p.val.1, p.property.1⟩ : V), p.val.2)) := by fun_prop
  have hcont : ContinuousOn
      (fun p : H × ℝ => ∫ t in a..p.2, G p.1 t) (V ×ˢ (univ : Set ℝ)) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact hc.comp hm
  exact hcont.continuousAt ((hV.prod isOpen_univ).mem_nhds ⟨hx, mem_univ b⟩)

/-- A moving primitive has genuine integrability, complex parameter derivatives
at every fixed real upper endpoint, analytic parameter dependence, and jointly
continuous value and derivative primitives. Apply the same interval theorem a
second time to a nested Cauchy density built from these primitives. -/
theorem parametricPrimitive_regular38
    {V : Set H} {F : H → ℝ → ℂ} {F' : H → ℝ → H →L[ℂ] ℂ}
    (hV : IsOpen V)
    (hF : ∀ x ∈ V, ∀ t : ℝ,
      ContinuousAt (Function.uncurry F) (x, t))
    (hF' : ∀ x ∈ V, ∀ t : ℝ,
      ContinuousAt (Function.uncurry F') (x, t))
    (hder : ∀ x ∈ V, ∀ t : ℝ,
      HasFDerivAt (fun y => F y t) (F' x t) x)
    (a : ℝ) :
    (∀ x ∈ V, ∀ b : ℝ,
      IntervalIntegrable (F x) volume a b ∧
        IntervalIntegrable (F' x) volume a b) ∧
    (∀ b : ℝ, AnalyticOnNhd ℂ (fun x => ∫ t in a..b, F x t) V) ∧
    (∀ x ∈ V, ∀ b : ℝ,
      HasFDerivAt (fun y => ∫ t in a..b, F y t)
        (∫ t in a..b, F' x t) x) ∧
    (∀ x ∈ V, ∀ b : ℝ,
      ContinuousAt (fun p : H × ℝ => ∫ t in a..p.2, F p.1 t) (x, b)) ∧
    (∀ x ∈ V, ∀ b : ℝ,
      ContinuousAt (fun p : H × ℝ => ∫ t in a..p.2, F' p.1 t) (x, b)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x hx b
    have h := parametricInterval_hasFDerivAt38 hV hF hF' hder a b hx
    exact ⟨h.1, h.2.1⟩
  · intro b
    exact parametricInterval_analytic38 hV hF hF' hder a b
  · intro x hx b
    exact (parametricInterval_hasFDerivAt38 hV hF hF' hder a b hx).2.2
  · intro x hx b
    exact parametricPrimitive_continuousAt38 hV hF a hx b
  · intro x hx b
    exact parametricPrimitive_continuousAt38 hV hF' a hx b

end
end NlsGge.GK38.Lib
