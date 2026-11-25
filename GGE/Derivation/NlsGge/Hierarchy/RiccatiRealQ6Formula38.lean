import NlsGge.Hierarchy.RiccatiQ4RecurrenceExpansionAfterNatCastPrerequisite
import NlsGge.Hierarchy.RiccatiSmoothJetDerivativeAfterProductPrerequisite
import NlsGge.Hierarchy.RiccatiPeriodicIteratedDerivClosurePrerequisite
import NlsGge.Hierarchy.RiccatiSpatialDerivationNatCastCoefficientPrerequisite
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! Claim A01.01: the explicit real `Q₆` local formula (paper/v2.tex, proof of
`C:prop:negative`, eq. `C:eq:Q6real`, lines 2434-2453).

Route: compute `p 6`, `p 7` from the Riccati recurrence; identify the formal
density `formalChargeIntegrand 3` evaluated on a real field with the paper's
pre-integration-by-parts density; then the difference with the final density is
the derivative of one explicit periodic flux (the sum of the paper's IBP steps),
whose integral over the unit period vanishes. -/

noncomputable section

namespace NlsGge.HierarchyRiccati.Core

open scoped ContDiff Interval
open MeasureTheory

local notation "𝐮" k:max => (MvPolynomial.X (false, k) : Poly)
local notation "𝐯" k:max => (MvPolynomial.X (true, k) : Poly)

private theorem spatialD_ofNat38 (n : ℕ) [n.AtLeastTwo] :
    spatialD (no_index (OfNat.ofNat n : Poly)) = 0 := by
  have h := spatialD_natCast_eq_zero (OfNat.ofNat n)
  rwa [Nat.cast_ofNat] at h

private theorem attachedIcc14_sum_nat38 {α : Type*} [AddCommMonoid α] (f : ℕ → α) :
    (Finset.Icc 1 4).attach.sum (fun l => f l.1) = f 1 + f 2 + f 3 + f 4 := by
  rw [Finset.sum_attach]
  rw [show Finset.Icc (1 : ℕ) 4 = {1, 2, 3, 4} by decide]
  simp [add_assoc]

private theorem attachedIcc15_sum_nat38 {α : Type*} [AddCommMonoid α] (f : ℕ → α) :
    (Finset.Icc 1 5).attach.sum (fun l => f l.1) = f 1 + f 2 + f 3 + f 4 + f 5 := by
  rw [Finset.sum_attach]
  rw [show Finset.Icc (1 : ℕ) 5 = {1, 2, 3, 4, 5} by decide]
  simp [add_assoc]

theorem p_six_formula38 :
    p 6 = -(𝐯 5) + (𝐮 3) * (𝐯 0) ^ 2 + 8 * (𝐮 2) * (𝐯 0) * (𝐯 1)
      + 12 * (𝐮 1) * (𝐯 0) * (𝐯 2) + 11 * (𝐮 1) * (𝐯 1) ^ 2
      + 18 * (𝐮 0) * (𝐯 1) * (𝐯 2) + 8 * (𝐮 0) * (𝐯 0) * (𝐯 3)
      - 6 * (𝐮 0) * (𝐮 1) * (𝐯 0) ^ 3 - 16 * (𝐮 0) ^ 2 * (𝐯 0) ^ 2 * (𝐯 1) := by
  rw [p_recurrence 4]
  rw [attachedIcc14_sum_nat38 (f := fun l : ℕ => p (4 + 1 - l) * p l)]
  simp only [Nat.reduceAdd, Nat.reduceSub]
  rw [p_five_after_natCast_prerequisite, p_four_after_natCast_prerequisite, p_three,
    p_two, p_one]
  simp only [spatialD.map_add, spatialD.map_sub, spatialD.map_neg, spatialD.map_smul,
    spatialD.leibniz, spatialD.leibniz_pow, spatialD_jet, spatialD_ofNat38,
    spatialD_four_eq_zero]
  simp only [smul_eq_mul, Nat.add_one_sub_one, Nat.reduceAdd]
  ring

theorem p_seven_formula38 :
    p 7 = -(𝐯 6) + (𝐮 4) * (𝐯 0) ^ 2 + 10 * (𝐮 3) * (𝐯 0) * (𝐯 1)
      + 20 * (𝐮 2) * (𝐯 0) * (𝐯 2) + 19 * (𝐮 2) * (𝐯 1) ^ 2
      + 20 * (𝐮 1) * (𝐯 0) * (𝐯 3) + 52 * (𝐮 1) * (𝐯 1) * (𝐯 2)
      + 10 * (𝐮 0) * (𝐯 0) * (𝐯 4) + 28 * (𝐮 0) * (𝐯 1) * (𝐯 3)
      + 19 * (𝐮 0) * (𝐯 2) ^ 2
      - 6 * (𝐮 1) ^ 2 * (𝐯 0) ^ 3 - 8 * (𝐮 0) * (𝐮 2) * (𝐯 0) ^ 3
      - 64 * (𝐮 0) * (𝐮 1) * (𝐯 0) ^ 2 * (𝐯 1)
      - 50 * (𝐮 0) ^ 2 * (𝐯 0) * (𝐯 1) ^ 2 - 30 * (𝐮 0) ^ 2 * (𝐯 0) ^ 2 * (𝐯 2)
      + 5 * (𝐮 0) ^ 3 * (𝐯 0) ^ 4 := by
  rw [p_recurrence 5]
  rw [attachedIcc15_sum_nat38 (f := fun l : ℕ => p (5 + 1 - l) * p l)]
  simp only [Nat.reduceAdd, Nat.reduceSub]
  rw [p_six_formula38, p_five_after_natCast_prerequisite, p_four_after_natCast_prerequisite,
    p_three, p_two, p_one]
  simp only [spatialD.map_add, spatialD.map_sub, spatialD.map_neg, spatialD.map_smul,
    spatialD.leibniz, spatialD.leibniz_pow, spatialD_jet, spatialD_ofNat38,
    spatialD_four_eq_zero]
  simp only [smul_eq_mul, Nat.add_one_sub_one, Nat.reduceAdd]
  ring


/-! ### Analytic part -/

private theorem iteratedDeriv_contDiff38 (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv n f) := by
  rw [iteratedDeriv_eq_iterate]
  exact ContDiff.iterate_deriv n hf

private theorem iteratedDeriv_contDiffC38 (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv n f) := by
  rw [iteratedDeriv_eq_iterate]
  exact ContDiff.iterate_deriv n hf

/-- Iterated derivatives commute with the real-to-complex coercion. -/
theorem iteratedDeriv_ofReal38 (u : ℝ → ℝ) (hu : ContDiff ℝ ∞ u) (n : ℕ) :
    iteratedDeriv n (fun x => (u x : ℂ)) = fun x => ((iteratedDeriv n u x : ℝ) : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      funext x
      rw [iteratedDeriv_succ, iteratedDeriv_succ, ih]
      have hd : DifferentiableAt ℝ (iteratedDeriv n u) x :=
        ((iteratedDeriv_contDiff38 u hu n).differentiable (by simp)).differentiableAt
      exact hd.hasDerivAt.ofReal_comp.deriv

/-- For a real field the conjugate jets coincide with the unconjugated jets, and the
evaluated formal density `u p_7` is the paper's pre-integration-by-parts density. -/
theorem realQ6_evaluation38 (u : ℝ → ℝ) (x : ℝ) :
    riccatiJetEvaluation (fun y => (u y : ℂ)) x (formalChargeIntegrand 3) =
      5 * (iteratedDeriv 0 (fun y => (u y : ℂ)) x) ^ 8
      - 38 * (iteratedDeriv 0 (fun y => (u y : ℂ)) x) ^ 5
          * iteratedDeriv 2 (fun y => (u y : ℂ)) x
      - 120 * (iteratedDeriv 0 (fun y => (u y : ℂ)) x) ^ 4
          * (iteratedDeriv 1 (fun y => (u y : ℂ)) x) ^ 2
      + 11 * (iteratedDeriv 0 (fun y => (u y : ℂ)) x) ^ 3
          * iteratedDeriv 4 (fun y => (u y : ℂ)) x
      + 58 * (iteratedDeriv 0 (fun y => (u y : ℂ)) x) ^ 2
          * iteratedDeriv 1 (fun y => (u y : ℂ)) x * iteratedDeriv 3 (fun y => (u y : ℂ)) x
      + 39 * (iteratedDeriv 0 (fun y => (u y : ℂ)) x) ^ 2
          * (iteratedDeriv 2 (fun y => (u y : ℂ)) x) ^ 2
      + 71 * iteratedDeriv 0 (fun y => (u y : ℂ)) x
          * (iteratedDeriv 1 (fun y => (u y : ℂ)) x) ^ 2
          * iteratedDeriv 2 (fun y => (u y : ℂ)) x
      - iteratedDeriv 0 (fun y => (u y : ℂ)) x * iteratedDeriv 6 (fun y => (u y : ℂ)) x := by
  have hstar : (fun y => star ((u y : ℝ) : ℂ)) = fun y => (u y : ℂ) := by
    funext y
    simp
  have hv : ∀ v : Jet, riccatiJetFunction (fun y => (u y : ℂ)) v x =
      iteratedDeriv v.2 (fun y => (u y : ℂ)) x := by
    rintro ⟨b, n⟩
    cases b
    · simp [riccatiJetFunction]
    · simp [riccatiJetFunction, hstar]
  unfold riccatiJetEvaluation formalChargeIntegrand
  rw [show 2 * 3 + 1 = 7 from rfl, p_seven_formula38]
  simp only [map_mul, map_add, map_sub, map_neg, map_pow, polynomialEvaluation_X,
    polynomialEvaluation_C, hv, map_ofNat]
  push_cast
  norm_num
  ring

private theorem hasDerivAt_iteratedDeriv38 (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (k : ℕ) (x : ℝ) :
    HasDerivAt (iteratedDeriv k U) (iteratedDeriv (k + 1) U x) x := by
  have hd : DifferentiableAt ℝ (iteratedDeriv k U) x :=
    ((iteratedDeriv_contDiffC38 U hU k).differentiable (by simp)).differentiableAt
  have h := hd.hasDerivAt
  rwa [← iteratedDeriv_succ] at h

/-- The complex-valued unit-period flux whose derivative is the difference between
the pre-IBP density and the final real `Q₆` density. -/
private def flux38 (U : ℝ → ℂ) (x : ℝ) : ℂ :=
  - (iteratedDeriv 0 U x * iteratedDeriv 5 U x)
    + iteratedDeriv 1 U x * iteratedDeriv 4 U x
    - iteratedDeriv 2 U x * iteratedDeriv 3 U x
    + 11 * iteratedDeriv 0 U x ^ 3 * iteratedDeriv 3 U x
    + 25 * iteratedDeriv 0 U x ^ 2 * iteratedDeriv 1 U x * iteratedDeriv 2 U x
    + 7 * iteratedDeriv 0 U x * iteratedDeriv 1 U x ^ 3
    - 38 * iteratedDeriv 0 U x ^ 5 * iteratedDeriv 1 U x

private def preDensity38 (U : ℝ → ℂ) (x : ℝ) : ℂ :=
  5 * (iteratedDeriv 0 U x) ^ 8
      - 38 * (iteratedDeriv 0 U x) ^ 5 * iteratedDeriv 2 U x
      - 120 * (iteratedDeriv 0 U x) ^ 4 * (iteratedDeriv 1 U x) ^ 2
      + 11 * (iteratedDeriv 0 U x) ^ 3 * iteratedDeriv 4 U x
      + 58 * (iteratedDeriv 0 U x) ^ 2 * iteratedDeriv 1 U x * iteratedDeriv 3 U x
      + 39 * (iteratedDeriv 0 U x) ^ 2 * (iteratedDeriv 2 U x) ^ 2
      + 71 * iteratedDeriv 0 U x * (iteratedDeriv 1 U x) ^ 2 * iteratedDeriv 2 U x
      - iteratedDeriv 0 U x * iteratedDeriv 6 U x

private def finalDensity38 (U : ℝ → ℂ) (x : ℝ) : ℂ :=
  (iteratedDeriv 3 U x) ^ 2 + 14 * (iteratedDeriv 0 U x) ^ 2 * (iteratedDeriv 2 U x) ^ 2
    - 7 * (iteratedDeriv 1 U x) ^ 4 + 70 * (iteratedDeriv 0 U x) ^ 4 * (iteratedDeriv 1 U x) ^ 2
    + 5 * (iteratedDeriv 0 U x) ^ 8

private theorem flux38_hasDerivAt (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (x : ℝ) :
    HasDerivAt (flux38 U) (preDensity38 U x - finalDensity38 U x) x := by
  have h0 := hasDerivAt_iteratedDeriv38 U hU 0 x
  have h1 := hasDerivAt_iteratedDeriv38 U hU 1 x
  have h2 := hasDerivAt_iteratedDeriv38 U hU 2 x
  have h3 := hasDerivAt_iteratedDeriv38 U hU 3 x
  have h4 := hasDerivAt_iteratedDeriv38 U hU 4 x
  have h5 := hasDerivAt_iteratedDeriv38 U hU 5 x
  have h := ((((((h0.mul h5).neg.add (h1.mul h4)).sub (h2.mul h3)).add
    (((h0.pow 3).const_mul 11).mul h3)).add
    ((((h0.pow 2).const_mul 25).mul h1).mul h2)).add
    ((h0.const_mul 7).mul (h1.pow 3))).sub
    (((h0.pow 5).const_mul 38).mul h1)
  refine HasDerivAt.congr_deriv (h.congr_of_eventuallyEq ?_) ?_
  · refine Filter.Eventually.of_forall fun y => ?_
    simp only [flux38, Pi.add_apply, Pi.mul_apply, Pi.sub_apply, Pi.neg_apply, Pi.pow_apply]
  · simp only [preDensity38, finalDensity38, Pi.add_apply, Pi.mul_apply, Pi.sub_apply,
      Pi.neg_apply, Pi.pow_apply, Nat.reduceAdd, Nat.reduceSub, Nat.cast_ofNat]
    ring

private theorem flux38_periodic (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U)
    (hper : Function.Periodic U 1) : Function.Periodic (flux38 U) 1 := by
  intro x
  have hp := fun k : ℕ => NlsGge.HierarchyRiccati.periodic_iteratedDeriv_of_contDiff U hU hper k x
  simp only [flux38, hp]

/-- Claim A01.01: the explicit real `Q₆` local formula. -/
theorem realQ6_local_formula38 (u : ℝ → ℝ) (hu : ContDiff ℝ ∞ u)
    (hper : Function.Periodic u 1) :
    (∫ x in (0 : ℝ)..1,
        riccatiJetEvaluation (fun y => (u y : ℂ)) x (formalChargeIntegrand 3)) =
      ((∫ x in (0 : ℝ)..1,
        ((iteratedDeriv 3 u x) ^ 2 + 14 * (u x) ^ 2 * (iteratedDeriv 2 u x) ^ 2
          - 7 * (deriv u x) ^ 4 + 70 * (u x) ^ 4 * (deriv u x) ^ 2 + 5 * (u x) ^ 8) : ℝ) : ℂ) := by
  set U : ℝ → ℂ := fun y => (u y : ℂ) with hUdef
  have hU : ContDiff ℝ ∞ U := Complex.ofRealCLM.contDiff.comp hu
  have hUper : Function.Periodic U 1 := by
    intro x
    simp only [hUdef, hper x]
  have hcontk : ∀ k : ℕ, Continuous (iteratedDeriv k U) := fun k =>
    (iteratedDeriv_contDiffC38 U hU k).continuous
  have hpre : Continuous (preDensity38 U) := by
    unfold preDensity38
    have := hcontk 0; have := hcontk 1; have := hcontk 2; have := hcontk 3
    have := hcontk 4; have := hcontk 6
    fun_prop
  have hfin : Continuous (finalDensity38 U) := by
    unfold finalDensity38
    have := hcontk 0; have := hcontk 1; have := hcontk 2; have := hcontk 3
    fun_prop
  have hint : IntervalIntegrable (fun x => preDensity38 U x - finalDensity38 U x)
      MeasureTheory.volume 0 1 := (hpre.sub hfin).intervalIntegrable 0 1
  have hzero : (∫ x in (0 : ℝ)..1, (preDensity38 U x - finalDensity38 U x)) = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => flux38_hasDerivAt U hU x) hint]
    have := flux38_periodic U hU hUper 0
    rw [zero_add] at this
    rw [this, sub_self]
  have hsplit : (∫ x in (0 : ℝ)..1, preDensity38 U x) =
      ∫ x in (0 : ℝ)..1, finalDensity38 U x := by
    rw [intervalIntegral.integral_sub (hpre.intervalIntegrable 0 1)
      (hfin.intervalIntegrable 0 1)] at hzero
    exact sub_eq_zero.mp hzero
  have hlhs : (fun x => riccatiJetEvaluation U x (formalChargeIntegrand 3)) =
      preDensity38 U := by
    funext x
    exact realQ6_evaluation38 u x
  have hrhs : (fun x => finalDensity38 U x) = fun x =>
      ((((iteratedDeriv 3 u x) ^ 2 + 14 * (u x) ^ 2 * (iteratedDeriv 2 u x) ^ 2
          - 7 * (deriv u x) ^ 4 + 70 * (u x) ^ 4 * (deriv u x) ^ 2 + 5 * (u x) ^ 8 : ℝ)) : ℂ) := by
    funext x
    have e := fun k : ℕ => congrFun (iteratedDeriv_ofReal38 u hu k) x
    simp only [finalDensity38, hUdef, e]
    rw [← iteratedDeriv_one]
    push_cast
    simp only [iteratedDeriv_zero]
  rw [hlhs, hsplit, hrhs]
  exact intervalIntegral.integral_ofReal

end NlsGge.HierarchyRiccati.Core

end
