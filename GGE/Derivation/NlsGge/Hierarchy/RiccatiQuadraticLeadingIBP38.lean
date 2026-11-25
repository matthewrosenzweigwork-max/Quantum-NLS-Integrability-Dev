import NlsGge.Hierarchy.RiccatiChargeRemainderNoQuadraticSupportSecond
import NlsGge.Hierarchy.RiccatiSmoothJetDerivativeAfterProductPrerequisite
import NlsGge.Hierarchy.RiccatiQ4IteratedDerivStarPrerequisiteThird
import NlsGge.Hierarchy.RiccatiPeriodicIteratedDerivClosurePrerequisite
import NlsGge.Hierarchy.PeriodicIntegrationByParts
import Mathlib.Tactic

/-! Batch 38, E06.03/E06.04: the leading quadratic term of the formal charge
integrates to `‖∂^j u‖²` on the unit circle.

Source: paper/v2.tex line 624 ("The leading quadratic term of `Q_{2j}` is
`‖∂_x^j u‖_2^2`") with the recursion of lines 956-959. The checked formal
quadratic component is `formalChargeQuadraticMainTerm j = (-1)^j u ∂^{2j} ū`
(`formalChargeIntegrand_degreeTwoComponent`). Here we perform the `j` periodic
integrations by parts with explicit boundary cancellation. -/

set_option autoImplicit false
noncomputable section

namespace NlsGge.HierarchyRiccati.Core

open scoped ContDiff ComplexConjugate

private theorem iteratedDeriv_hasDerivAt38 (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (k : ℕ) (x : ℝ) :
    HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k + 1) f x) x := by
  have hd : Differentiable ℝ (iteratedDeriv k f) :=
    hf.differentiable_iteratedDeriv k (by exact_mod_cast WithTop.coe_lt_top _)
  rw [iteratedDeriv_succ]
  exact (hd x).hasDerivAt

private theorem iteratedDeriv_continuous38 (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (k : ℕ) : Continuous (iteratedDeriv k f) :=
  hf.continuous_iteratedDeriv k (by exact_mod_cast le_top)

private theorem contDiff_star38 (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (fun x => star (u x)) := by
  have hstar : ContDiff ℝ ∞ (fun z : ℂ => star z) :=
    ((starL ℝ : ℂ ≃L⋆[ℝ] ℂ).toContinuousLinearMap).contDiff
  exact hstar.comp hu

private theorem periodic_star38 (u : ℝ → ℂ) (hper : Function.Periodic u 1) :
    Function.Periodic (fun x => star (u x)) 1 := by
  intro x
  simp [hper x]

/-- One periodic integration by parts between two smooth periodic functions'
iterated derivatives. -/
theorem iteratedDeriv_pair_ibp38 (f g : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (hfper : Function.Periodic f 1)
    (hgper : Function.Periodic g 1) (a b : ℕ) :
    (∫ x in (0 : ℝ)..1, iteratedDeriv a f x * iteratedDeriv (b + 1) g x) =
      -(∫ x in (0 : ℝ)..1, iteratedDeriv (a + 1) f x * iteratedDeriv b g x) :=
  NlsGge.HierarchyRiccati.unitPeriod_integral_mul_deriv_eq_neg_deriv_mul
    (NlsGge.HierarchyRiccati.periodic_iteratedDeriv_of_contDiff f hf hfper a)
    (NlsGge.HierarchyRiccati.periodic_iteratedDeriv_of_contDiff g hg hgper b)
    (fun x _ => iteratedDeriv_hasDerivAt38 f hf a x)
    (fun x _ => iteratedDeriv_hasDerivAt38 g hg b x)
    ((iteratedDeriv_continuous38 f hf (a + 1)).intervalIntegrable _ _)
    ((iteratedDeriv_continuous38 g hg (b + 1)).intervalIntegrable _ _)

/-- `k` periodic integrations by parts. -/
theorem iteratedDeriv_pair_ibp_iter38 (f g : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (hfper : Function.Periodic f 1)
    (hgper : Function.Periodic g 1) (a b k : ℕ) :
    (∫ x in (0 : ℝ)..1, iteratedDeriv a f x * iteratedDeriv (b + k) g x) =
      (-1 : ℂ) ^ k *
        (∫ x in (0 : ℝ)..1, iteratedDeriv (a + k) f x * iteratedDeriv b g x) := by
  induction k generalizing a with
  | zero => simp
  | succ k ih =>
      have hstep := iteratedDeriv_pair_ibp38 f g hf hg hfper hgper a (b + k)
      rw [show b + (k + 1) = b + k + 1 by omega, hstep, ih (a + 1),
        show a + 1 + k = a + (k + 1) by omega, pow_succ]
      ring

/-- E06.03/E06.04 leading quadratic term: for every smooth period-one field,
the period integral of the formal quadratic main term `(-1)^j u ∂^{2j} ū`
equals `∫₀¹ |u^{(j)}|²`. -/
theorem formalChargeQuadraticMainTerm_integral_eq38 (j : ℕ) (u : ℝ → ℂ)
    (hu : ContDiff ℝ ∞ u) (hper : Function.Periodic u 1) :
    (∫ x in (0 : ℝ)..1,
        riccatiJetEvaluation u x (formalChargeQuadraticMainTerm j)) =
      ∫ x in (0 : ℝ)..1, ((‖iteratedDeriv j u x‖ ^ 2 : ℝ) : ℂ) := by
  set ub : ℝ → ℂ := fun x => star (u x) with hub
  have hub_smooth : ContDiff ℝ ∞ ub := contDiff_star38 u hu
  have hub_per : Function.Periodic ub 1 := periodic_star38 u hper
  have heval : ∀ x : ℝ,
      riccatiJetEvaluation u x (formalChargeQuadraticMainTerm j) =
        (-1 : ℂ) ^ j * (iteratedDeriv 0 u x * iteratedDeriv (j + j) ub x) := by
    intro x
    simp [formalChargeQuadraticMainTerm, riccatiJetEvaluation, riccatiJetFunction,
      polynomialEvaluation, hub, two_mul]
    ring
  have hibp := iteratedDeriv_pair_ibp_iter38 u ub hu hub_smooth hper hub_per 0 j j
  have hstar : ∀ x : ℝ, iteratedDeriv j ub x = star (iteratedDeriv j u x) := by
    intro x
    rw [hub, iteratedDeriv_star_prerequisite]
  calc
    (∫ x in (0 : ℝ)..1,
        riccatiJetEvaluation u x (formalChargeQuadraticMainTerm j)) =
        (-1 : ℂ) ^ j *
          (∫ x in (0 : ℝ)..1, iteratedDeriv 0 u x * iteratedDeriv (j + j) ub x) := by
      simp_rw [heval]
      exact intervalIntegral.integral_const_mul _ _
    _ = (-1 : ℂ) ^ j * ((-1 : ℂ) ^ j *
          (∫ x in (0 : ℝ)..1, iteratedDeriv (0 + j) u x * iteratedDeriv j ub x)) := by
      rw [hibp]
    _ = ∫ x in (0 : ℝ)..1, iteratedDeriv j u x * iteratedDeriv j ub x := by
      rw [← mul_assoc, ← mul_pow, show ((-1 : ℂ) * -1) = 1 by norm_num, one_pow,
        one_mul, zero_add]
    _ = ∫ x in (0 : ℝ)..1, ((‖iteratedDeriv j u x‖ ^ 2 : ℝ) : ℂ) := by
      apply intervalIntegral.integral_congr
      intro x _
      simp only
      rw [hstar x]
      change iteratedDeriv j u x * (starRingEnd ℂ) (iteratedDeriv j u x) = _
      rw [Complex.mul_conj']
      push_cast
      ring

end NlsGge.HierarchyRiccati.Core

end
