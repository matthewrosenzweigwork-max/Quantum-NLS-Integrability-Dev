import Mathlib
import NlsGge.Hierarchy.RiccatiRealQ6Formula38

set_option autoImplicit false

/- F-033 PRODUCTION01 (proof development, AUTHOR; target NlsGge/Atomic/F/F033.lean, namespace NlsGge.ThirdConsultation.F as landed F035).
   Head verbatim from followup2 STATEMENTS/F.md F-033. Proof: clause 1 = realQ6_evaluation38 with iteratedDeriv_ofReal38 casts;
   clauses 2-4 = periodic integral of an explicit derivative (u^3 u''', u^2 u' u'', u (u')^3 fluxes); clause 5 = realQ6_local_formula38. -/

open MeasureTheory
open scoped Topology ContDiff Interval
open NlsGge.HierarchyRiccati.Core

namespace NlsGge.ThirdConsultation.F
noncomputable section
namespace F033Aux

theorem contDiff_iter (u : ℝ → ℝ) (hu : ContDiff ℝ ∞ u) (n : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv n u) := by
  rw [iteratedDeriv_eq_iterate]
  exact ContDiff.iterate_deriv n hu

theorem periodic_deriv_aux (f : ℝ → ℝ) (h : Function.Periodic f 1) :
    Function.Periodic (deriv f) 1 := by
  intro x
  have e : (fun y => f (y + 1)) = f := funext h
  rw [← deriv_comp_add_const, e]

theorem periodic_iter (u : ℝ → ℝ) (hper : Function.Periodic u 1) (n : ℕ) :
    Function.Periodic (iteratedDeriv n u) 1 := by
  induction n with
  | zero => simpa using hper
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact periodic_deriv_aux _ ih

theorem ibp_zero (g g' : ℝ → ℝ) (hg : ∀ x, HasDerivAt g (g' x) x) (hc : Continuous g')
    (hp : Function.Periodic g 1) : (∫ x in (0 : ℝ)..1, g' x) = 0 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hg x) (hc.intervalIntegrable 0 1)]
  have := hp 0
  rw [zero_add] at this
  rw [this, sub_self]

end F033Aux

open F033Aux in
theorem f033 (u : ℝ → ℝ) (hu : ContDiff ℝ ∞ u)
    (hper : Function.Periodic u 1) :
    (∀ x : ℝ,
      riccatiJetEvaluation (fun y => (u y : ℂ)) x (formalChargeIntegrand 3) =
        ((5 * (u x) ^ 8 - 38 * (u x) ^ 5 * iteratedDeriv 2 u x -
          120 * (u x) ^ 4 * (deriv u x) ^ 2 +
          11 * (u x) ^ 3 * iteratedDeriv 4 u x +
          58 * (u x) ^ 2 * deriv u x * iteratedDeriv 3 u x +
          39 * (u x) ^ 2 * (iteratedDeriv 2 u x) ^ 2 +
          71 * u x * (deriv u x) ^ 2 * iteratedDeriv 2 u x -
          u x * iteratedDeriv 6 u x : ℝ) : ℂ)) ∧
    (∫ x in (0 : ℝ)..1, (u x) ^ 3 * iteratedDeriv 4 u x) =
      3 * (∫ x in (0 : ℝ)..1, (u x) ^ 2 * (iteratedDeriv 2 u x) ^ 2) -
        2 * (∫ x in (0 : ℝ)..1, (deriv u x) ^ 4) ∧
    (∫ x in (0 : ℝ)..1, (u x) ^ 2 * deriv u x * iteratedDeriv 3 u x) =
      -(∫ x in (0 : ℝ)..1, (u x) ^ 2 * (iteratedDeriv 2 u x) ^ 2) +
        (2 / 3 : ℝ) * (∫ x in (0 : ℝ)..1, (deriv u x) ^ 4) ∧
    (∫ x in (0 : ℝ)..1, u x * (deriv u x) ^ 2 * iteratedDeriv 2 u x) =
      -(1 / 3 : ℝ) * (∫ x in (0 : ℝ)..1, (deriv u x) ^ 4) ∧
    (∫ x in (0 : ℝ)..1,
      riccatiJetEvaluation (fun y => (u y : ℂ)) x (formalChargeIntegrand 3)) =
        ((∫ x in (0 : ℝ)..1,
          (iteratedDeriv 3 u x) ^ 2 + 14 * (u x) ^ 2 * (iteratedDeriv 2 u x) ^ 2 -
          7 * (deriv u x) ^ 4 + 70 * (u x) ^ 4 * (deriv u x) ^ 2 + 5 * (u x) ^ 8 : ℝ) : ℂ) := by
  have hc : ∀ k : ℕ, Continuous (iteratedDeriv k u) := fun k => (contDiff_iter u hu k).continuous
  have hp : ∀ k : ℕ, Function.Periodic (iteratedDeriv k u) 1 := periodic_iter u hper
  have hd : ∀ (k : ℕ) (x : ℝ), HasDerivAt (iteratedDeriv k u) (iteratedDeriv (k + 1) u x) x := by
    intro k x
    have hdf : DifferentiableAt ℝ (iteratedDeriv k u) x :=
      ((contDiff_iter u hu k).differentiable (by simp)).differentiableAt
    have h := hdf.hasDerivAt
    rwa [← iteratedDeriv_succ] at h
  have c0 : Continuous u := by simpa using hc 0
  have c1 : Continuous (deriv u) := by simpa using hc 1
  have c2 := hc 2
  have c3 := hc 3
  have c4 := hc 4
  have p0 : Function.Periodic u 1 := hper
  have p1 : Function.Periodic (deriv u) 1 := by simpa using hp 1
  have p2 := hp 2
  have p3 := hp 3
  have h0 : ∀ x, HasDerivAt u (deriv u x) x := by
    intro x; simpa using hd 0 x
  have h1 : ∀ x, HasDerivAt (deriv u) (iteratedDeriv 2 u x) x := by
    intro x; simpa using hd 1 x
  have h2 : ∀ x, HasDerivAt (iteratedDeriv 2 u) (iteratedDeriv 3 u x) x := fun x => hd 2 x
  have h3 : ∀ x, HasDerivAt (iteratedDeriv 3 u) (iteratedDeriv 4 u x) x := fun x => hd 3 x
  -- integrals of the building blocks
  have i4 : IntervalIntegrable (fun x => (deriv u x) ^ 4) volume 0 1 :=
    (by fun_prop : Continuous fun x => (deriv u x) ^ 4).intervalIntegrable 0 1
  have iA : IntervalIntegrable (fun x => u x * (deriv u x) ^ 2 * iteratedDeriv 2 u x) volume 0 1 :=
    (by fun_prop : Continuous fun x => u x * (deriv u x) ^ 2 * iteratedDeriv 2 u x).intervalIntegrable 0 1
  have iB : IntervalIntegrable (fun x => (u x) ^ 2 * (iteratedDeriv 2 u x) ^ 2) volume 0 1 :=
    (by fun_prop : Continuous fun x => (u x) ^ 2 * (iteratedDeriv 2 u x) ^ 2).intervalIntegrable 0 1
  have iC : IntervalIntegrable (fun x => (u x) ^ 2 * deriv u x * iteratedDeriv 3 u x) volume 0 1 :=
    (by fun_prop : Continuous fun x => (u x) ^ 2 * deriv u x * iteratedDeriv 3 u x).intervalIntegrable 0 1
  have iD : IntervalIntegrable (fun x => (u x) ^ 3 * iteratedDeriv 4 u x) volume 0 1 :=
    (by fun_prop : Continuous fun x => (u x) ^ 3 * iteratedDeriv 4 u x).intervalIntegrable 0 1
  -- (4): d/dx (u u'^3) = u'^4 + 3 u u'^2 u''
  have e4 : (∫ x in (0 : ℝ)..1, ((deriv u x) ^ 4 + 3 * (u x * (deriv u x) ^ 2 * iteratedDeriv 2 u x))) = 0 := by
    refine ibp_zero (fun x => u x * (deriv u x) ^ 3) _ (fun x => ?_) (by fun_prop) ?_
    · have h := (h0 x).mul ((h1 x).pow 3)
      refine h.congr_deriv ?_
      simp only [Nat.cast_ofNat, Nat.reduceSub, Nat.reduceAdd, pow_one, Pi.pow_apply, Pi.mul_apply]
      ring
    · intro x
      simp only [p0 x, p1 x]
  rw [intervalIntegral.integral_add i4 (iA.const_mul 3), intervalIntegral.integral_const_mul] at e4
  -- (3): d/dx (u^2 u' u'') = 2 u u'^2 u'' + u^2 u''^2 + u^2 u' u'''
  have e3 : (∫ x in (0 : ℝ)..1, (2 * (u x * (deriv u x) ^ 2 * iteratedDeriv 2 u x) +
      (u x) ^ 2 * (iteratedDeriv 2 u x) ^ 2 + (u x) ^ 2 * deriv u x * iteratedDeriv 3 u x)) = 0 := by
    refine ibp_zero (fun x => (u x) ^ 2 * deriv u x * iteratedDeriv 2 u x) _ (fun x => ?_)
      (by fun_prop) ?_
    · have h := (((h0 x).pow 2).mul (h1 x)).mul (h2 x)
      refine h.congr_deriv ?_
      simp only [Nat.cast_ofNat, Nat.reduceSub, Nat.reduceAdd, pow_one, Pi.pow_apply, Pi.mul_apply]
      ring
    · intro x
      simp only [p0 x, p1 x, p2 x]
  rw [intervalIntegral.integral_add ((iA.const_mul 2).add iB) iC,
    intervalIntegral.integral_add (iA.const_mul 2) iB, intervalIntegral.integral_const_mul] at e3
  -- (2): d/dx (u^3 u''') = 3 u^2 u' u''' + u^3 u''''
  have e2 : (∫ x in (0 : ℝ)..1, (3 * ((u x) ^ 2 * deriv u x * iteratedDeriv 3 u x) +
      (u x) ^ 3 * iteratedDeriv 4 u x)) = 0 := by
    refine ibp_zero (fun x => (u x) ^ 3 * iteratedDeriv 3 u x) _ (fun x => ?_) (by fun_prop) ?_
    · have h := ((h0 x).pow 3).mul (h3 x)
      refine h.congr_deriv ?_
      simp only [Nat.cast_ofNat, Nat.reduceSub, Nat.reduceAdd, pow_one, Pi.pow_apply, Pi.mul_apply]
      ring
    · intro x
      simp only [p0 x, p3 x]
  rw [intervalIntegral.integral_add (iC.const_mul 3) iD, intervalIntegral.integral_const_mul] at e2
  refine ⟨?_, by linarith, by linarith, by linarith, ?_⟩
  · intro x
    rw [realQ6_evaluation38 u x]
    have e := fun k : ℕ => congrFun (iteratedDeriv_ofReal38 u hu k) x
    simp only [e, iteratedDeriv_zero, iteratedDeriv_one]
    push_cast
    ring
  · exact realQ6_local_formula38 u hu hper

end
end NlsGge.ThirdConsultation.F
