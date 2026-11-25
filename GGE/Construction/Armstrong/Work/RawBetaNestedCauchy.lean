import Armstrong.Work.RawBetaParametricInterval
import NlsGge.GK38.Lib.ParamCircleAnalyticBounds
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
Nested real-interval integration in complex normed-space parameters.

The inner primitive is differentiated in the complex parameter at each fixed
real upper endpoint. Its derivative primitive is jointly continuous in the
parameter and real endpoint, which supplies the outer density's derivative
continuity. No complex structure is imposed on the real integration variable.

The final adapter starts with genuine joint complex analyticity of boundary
functions before evaluation on a fixed circle. It does not assume the real
boundary primitive has a holomorphic extension in the circle variable.

Root owns compilation and integration. This module proves generic supporting
statements only, with no new same-W/F source theorem or frozen-anchor claim.
-/

set_option autoImplicit false

open Set Metric Filter MeasureTheory
open scoped Topology Interval

namespace NlsGge.GK38.Lib
noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- A nested real primitive/product has genuine outer integrability, an explicit
complex parameter derivative, and analytic parameter dependence. Density and
derivative-density continuity are input data; integral regularity is proved. -/
theorem parametricNestedInterval_regular38
    {V : Set H} {A B : H → ℝ → ℂ}
    {A' B' : H → ℝ → H →L[ℂ] ℂ}
    (hV : IsOpen V)
    (hA : ∀ x ∈ V, ∀ t : ℝ,
      ContinuousAt (Function.uncurry A) (x, t))
    (hA' : ∀ x ∈ V, ∀ t : ℝ,
      ContinuousAt (Function.uncurry A') (x, t))
    (hAder : ∀ x ∈ V, ∀ t : ℝ,
      HasFDerivAt (fun y => A y t) (A' x t) x)
    (hB : ∀ x ∈ V, ∀ t : ℝ,
      ContinuousAt (Function.uncurry B) (x, t))
    (hB' : ∀ x ∈ V, ∀ t : ℝ,
      ContinuousAt (Function.uncurry B') (x, t))
    (hBder : ∀ x ∈ V, ∀ t : ℝ,
      HasFDerivAt (fun y => B y t) (B' x t) x)
    (a l u : ℝ) :
    (∀ x ∈ V, IntervalIntegrable
      (fun t => (∫ s in a..t, A x s) * B x t) volume l u) ∧
    (∀ x ∈ V, HasFDerivAt
      (fun y => ∫ t in l..u, (∫ s in a..t, A y s) * B y t)
      (∫ t in l..u,
        (∫ s in a..t, A x s) • B' x t +
          B x t • (∫ s in a..t, A' x s)) x) ∧
    AnalyticOnNhd ℂ
      (fun x => ∫ t in l..u, (∫ s in a..t, A x s) * B x t) V := by
  let U : H → ℝ → ℂ := fun x t => ∫ s in a..t, A x s
  let U' : H → ℝ → H →L[ℂ] ℂ := fun x t => ∫ s in a..t, A' x s
  let C : H → ℝ → ℂ := fun x t => U x t * B x t
  let C' : H → ℝ → H →L[ℂ] ℂ := fun x t =>
    U x t • B' x t + B x t • U' x t
  have hUc : ∀ x ∈ V, ∀ t : ℝ,
      ContinuousAt (Function.uncurry U) (x, t) := by
    intro x hx t
    exact parametricPrimitive_continuousAt38 hV hA a hx t
  have hU'c : ∀ x ∈ V, ∀ t : ℝ,
      ContinuousAt (Function.uncurry U') (x, t) := by
    intro x hx t
    exact parametricPrimitive_continuousAt38 hV hA' a hx t
  have hUd : ∀ x ∈ V, ∀ t : ℝ,
      HasFDerivAt (fun y => U y t) (U' x t) x := by
    intro x hx t
    exact (parametricInterval_hasFDerivAt38 hV hA hA' hAder a t hx).2.2
  have hC : ∀ x ∈ V, ∀ t : ℝ,
      ContinuousAt (Function.uncurry C) (x, t) := by
    intro x hx t
    exact (hUc x hx t).mul (hB x hx t)
  have hC' : ∀ x ∈ V, ∀ t : ℝ,
      ContinuousAt (Function.uncurry C') (x, t) := by
    intro x hx t
    exact ((hUc x hx t).smul (hB' x hx t)).add
      ((hB x hx t).smul (hU'c x hx t))
  have hCd : ∀ x ∈ V, ∀ t : ℝ,
      HasFDerivAt (fun y => C y t) (C' x t) x := by
    intro x hx t
    exact (hUd x hx t).mul (hBder x hx t)
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact (parametricInterval_hasFDerivAt38 hV hC hC' hCd l u hx).1
  · intro x hx
    exact (parametricInterval_hasFDerivAt38 hV hC hC' hCd l u hx).2.2
  · exact parametricInterval_analytic38 hV hC hC' hCd l u

/-- Evaluation of a genuinely jointly complex analytic boundary function on a
fixed real circle parameter gives the value/derivative continuity and actual
complex parameter derivative required by the interval integration theorem. -/
theorem parametricCircleEval_regular38
    {V : Set H} {center : ℂ} {radius : ℝ} {F : H → ℂ → ℂ}
    (hr : 0 < radius)
    (hF : AnalyticOnNhd ℂ (Function.uncurry F)
      (V ×ˢ sphere center radius)) :
    (∀ x ∈ V, ∀ t : ℝ,
      ContinuousAt (fun p : H × ℝ => F p.1 (circleMap center radius p.2)) (x, t)) ∧
    (∀ x ∈ V, ∀ t : ℝ,
      ContinuousAt (fun p : H × ℝ =>
        paramCircleDerivative38 F p.1 (circleMap center radius p.2)) (x, t)) ∧
    (∀ x ∈ V, ∀ t : ℝ,
      HasFDerivAt (fun y => F y (circleMap center radius t))
        (paramCircleDerivative38 F x (circleMap center radius t)) x) := by
  have hp : Continuous (fun p : H × ℝ => (p.1, circleMap center radius p.2)) := by
    fun_prop
  refine ⟨?_, ?_, ?_⟩
  · intro x hx t
    have ha := hF (x, circleMap center radius t)
      ⟨hx, circleMap_mem_sphere center hr.le t⟩
    exact ContinuousAt.comp
      (f := fun p : H × ℝ => (p.1, circleMap center radius p.2))
      (g := Function.uncurry F) (x := (x, t))
      ha.continuousAt hp.continuousAt
  · intro x hx t
    have ha := hF (x, circleMap center radius t)
      ⟨hx, circleMap_mem_sphere center hr.le t⟩
    have hJ : ContinuousAt
        (fun p : H × ℝ => fderiv ℂ (Function.uncurry F)
          (p.1, circleMap center radius p.2)) (x, t) :=
      ContinuousAt.comp
        (f := fun p : H × ℝ => (p.1, circleMap center radius p.2))
        (g := fderiv ℂ (Function.uncurry F)) (x := (x, t))
        ha.fderiv.continuousAt hp.continuousAt
    dsimp only [paramCircleDerivative38]
    exact hJ.clm_comp continuousAt_const
  · intro x hx t
    exact paramCircle_hasFDerivAt38
      (hF (x, circleMap center radius t)
        ⟨hx, circleMap_mem_sphere center hr.le t⟩)

/-- The literal two-real-parameter nested integral of two jointly complex
analytic fixed-circle boundary functions is analytic in its ambient parameter.
The real primitive does not need a complex-circle-variable extension. -/
theorem parametricNestedCircle_analytic38
    {V : Set H} {center : ℂ} {radius : ℝ} {A B : H → ℂ → ℂ}
    (hV : IsOpen V) (hr : 0 < radius)
    (hA : AnalyticOnNhd ℂ (Function.uncurry A) (V ×ˢ sphere center radius))
    (hB : AnalyticOnNhd ℂ (Function.uncurry B) (V ×ˢ sphere center radius))
    (a l u : ℝ) :
    AnalyticOnNhd ℂ (fun x =>
      ∫ θ in l..u,
        (∫ t in a..θ, A x (circleMap center radius t)) *
          B x (circleMap center radius θ)) V := by
  obtain ⟨hAc, hA'c, hAd⟩ := parametricCircleEval_regular38 hr hA
  obtain ⟨hBc, hB'c, hBd⟩ := parametricCircleEval_regular38 hr hB
  exact (parametricNestedInterval_regular38
    (A := fun x t => A x (circleMap center radius t))
    (A' := fun x t => paramCircleDerivative38 A x (circleMap center radius t))
    (B := fun x t => B x (circleMap center radius t))
    (B' := fun x t => paramCircleDerivative38 B x (circleMap center radius t))
    hV hAc hA'c hAd hBc hB'c hBd a l u).2.2

end
end NlsGge.GK38.Lib
