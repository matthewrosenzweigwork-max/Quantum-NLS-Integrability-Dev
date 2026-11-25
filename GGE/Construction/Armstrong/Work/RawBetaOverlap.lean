import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! Internal ordinary helpers for the reviewed scalar raw-beta route.

The full-characteristic invariant compares two genuine coefficient ODEs on
one open preconnected overlap.  Neither the characteristic nor the terminal
square root is divided out.  Ambient extension is only an existential witness;
its value away from the prescribed open set has no source-object semantics.
-/

set_option autoImplicit false
open Set Filter
open scoped Topology

namespace NlsGge.GK38

/-- Coefficients of the same full-characteristic ODE have the same normalized
terminal value when the overlap contains a characteristic zero. -/
theorem rawBetaTerminalEqualityOfSharedODE38
    (U : Set ℂ) (hU : IsOpen U) (hUc : IsPreconnected U)
    (Q R S Ψ : ℂ → ℂ)
    (hQ : DifferentiableOn ℂ Q U)
    (hR : DifferentiableOn ℂ R U)
    (hS : DifferentiableOn ℂ S U)
    (hRode : ∀ w ∈ U,
      Q w * deriv R w + (deriv Q w / 2) * R w = Ψ w)
    (hSode : ∀ w ∈ U,
      Q w * deriv S w + (deriv Q w / 2) * S w = Ψ w)
    (a z δ : ℂ) (ha : a ∈ U) (hz : z ∈ U)
    (hQa : Q a = 0) (hδ : δ ^ 2 = Q z) :
    δ * R z = δ * S z := by
  let H : ℂ → ℂ := fun w => Q w * (R w - S w) ^ 2
  have hH : DifferentiableOn ℂ H U := hQ.mul ((hR.sub hS).pow 2)
  have hHderiv : U.EqOn (deriv H) 0 := by
    intro w hw
    have hQw := (hQ w hw).differentiableAt (hU.mem_nhds hw)
    have hRw := (hR w hw).differentiableAt (hU.mem_nhds hw)
    have hSw := (hS w hw).differentiableAt (hU.mem_nhds hw)
    have hd : HasDerivAt H
        (deriv Q w * (R w - S w) ^ 2 +
          Q w * (2 * (R w - S w) * (deriv R w - deriv S w))) w := by
      apply (hQw.hasDerivAt.mul
        ((hRw.hasDerivAt.sub hSw.hasDerivAt).pow 2)).congr_deriv
      change deriv Q w * (R w - S w) ^ 2 +
        Q w * (2 * (R w - S w) ^ (2 - 1) * (deriv R w - deriv S w)) = _
      ring
    change deriv H w = 0
    rw [hd.deriv]
    have h1 := hRode w hw
    have h2 := hSode w hw
    linear_combination 2 * (R w - S w) * (h1 - h2)
  have hc : H z = H a := hU.is_const_of_deriv_eq_zero hUc hH hHderiv hz ha
  have hz0 : Q z * (R z - S z) ^ 2 = 0 := by
    simpa only [H, hQa, zero_mul] using hc
  have hp : δ * (R z - S z) = 0 := by
    apply sq_eq_zero_iff.mp
    rw [mul_pow, hδ]
    exact hz0
  exact sub_eq_zero.mp (by simpa only [mul_sub] using hp)

/-- Local analytic representatives of a scalar function on an open set give
one ambient analytic witness on that entire same set. -/
theorem rawBetaAmbientAnalyticOfLocal38
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (W : Set E) (hW : IsOpen W) (f : W → ℂ)
    (hlocal : ∀ x : W, ∃ V : Set E, IsOpen V ∧ x.1 ∈ V ∧
      ∃ g : E → ℂ, AnalyticOnNhd ℂ g V ∧
        ∀ y : W, y.1 ∈ V → g y.1 = f y) :
    ∃ b : E → ℂ, AnalyticOnNhd ℂ b W ∧ ∀ x : W, b x.1 = f x := by
  classical
  let b : E → ℂ := fun x => if h : x ∈ W then f ⟨x, h⟩ else 0
  have hb : ∀ x : W, b x.1 = f x := by
    intro x
    simp only [b, dite_eq_left x.property]
  refine ⟨b, ?_, hb⟩
  intro x hx
  obtain ⟨V, hV, hxV, g, hg, hgf⟩ := hlocal ⟨x, hx⟩
  apply (hg x hxV).congr
  filter_upwards [hV.mem_nhds hxV, hW.mem_nhds hx] with y hyV hyW
  exact (hgf ⟨y, hyW⟩ hyV).trans (hb ⟨y, hyW⟩).symm

end NlsGge.GK38
