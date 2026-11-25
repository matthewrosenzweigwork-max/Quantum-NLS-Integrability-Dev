import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! A continuous nonzero square-root lift inherits its parameter derivative.
The last lemma identifies the primitive supplied by an analytic coefficient
solving the source differential equation. No endpoint derivative is assumed.

REVIEW_ONLY: prospective source, pending the root compiler queue.
-/

set_option autoImplicit false
open Filter
open scoped Topology

namespace NlsGge.GK38
noncomputable section

theorem rawBetaHasDerivAtOfComplexCompLeft38
    {f : ℂ → ℂ} {g h : ℝ → ℂ} {f' h' : ℂ} {t : ℝ}
    (hg : ContinuousAt g t) (hf : HasDerivAt f f' (g t))
    (hh : HasDerivAt h h' t) (hf' : f' ≠ 0)
    (hcomp : f ∘ g =ᶠ[nhds t] h) :
    HasDerivAt g (h' / f') t := by
  have hinv : Function.LeftInverse
      ((ContinuousLinearMap.toSpanSingleton ℂ f'⁻¹).restrictScalars ℝ)
      ((ContinuousLinearMap.toSpanSingleton ℂ f').restrictScalars ℝ) := by
    intro z
    simp [hf']
  have hd := HasFDerivAt.of_comp_of_leftInverse hg
    (hf.hasFDerivAt.restrictScalars ℝ) hh.hasFDerivAt hcomp hinv
  simpa [div_eq_mul_inv] using hd.hasDerivAt

theorem rawBetaContinuousRootHasDerivAt38
    {s : ℝ → ℂ} {t : ℝ} {q : ℂ}
    (hsc : ContinuousAt s t) (hsn : s t ≠ 0)
    (hsq : HasDerivAt (fun u => s u ^ 2) q t) :
    HasDerivAt s (q / (2 * s t)) t := by
  have hpow : HasDerivAt (fun z : ℂ => z ^ 2) (2 * s t) (s t) := by
    simpa using hasDerivAt_pow 2 (s t)
  exact rawBetaHasDerivAtOfComplexCompLeft38 hsc hpow hsq
    (mul_ne_zero (by norm_num) hsn) Filter.EventuallyEq.rfl

theorem rawBetaContinuousRootHasDerivAtOfEq38
    {P : ℂ → ℂ} {γ s : ℝ → ℂ} {t : ℝ} {P' γ' : ℂ}
    (hγ : HasDerivAt γ γ' t) (hP : HasDerivAt P P' (γ t))
    (hsc : ContinuousAt s t) (hsn : s t ≠ 0)
    (he : (fun u => s u ^ 2) =ᶠ[nhds t] P ∘ γ) :
    HasDerivAt s ((P' * γ') / (2 * s t)) t :=
  rawBetaContinuousRootHasDerivAt38 hsc hsn
    ((hP.comp t hγ).congr_of_eventuallyEq he)

/-- The analytic coefficient is still an explicit hypothesis here. Its
actual construction from the same numerator's zero contour period is a
separate obligation. -/
theorem rawBetaSheetPrimitiveHasDerivAt38
    {P Ψ R : ℂ → ℂ} {γ s : ℝ → ℂ} {t : ℝ} {P' R' γ' : ℂ}
    (hγ : HasDerivAt γ γ' t) (hP : HasDerivAt P P' (γ t))
    (hR : HasDerivAt R R' (γ t))
    (hsc : ContinuousAt s t) (hsn : s t ≠ 0)
    (he : (fun u => s u ^ 2) =ᶠ[nhds t] P ∘ γ)
    (hODE : P (γ t) * R' + (P' / 2) * R (γ t) = Ψ (γ t)) :
    HasDerivAt (fun u => s u * R (γ u))
      ((Ψ (γ t) / s t) * γ') t := by
  have hs := rawBetaContinuousRootHasDerivAtOfEq38 hγ hP hsc hsn he
  have hsq : s t ^ 2 = P (γ t) := he.self_of_nhds
  apply (hs.mul (hR.comp t hγ)).congr_deriv
  calc
    ((P' * γ') / (2 * s t)) * R (γ t) + s t * (R' * γ')
        = ((s t ^ 2 * R' + (P' / 2) * R (γ t)) / s t) * γ' := by
            field_simp [hsn]
            ring
    _ = ((Ψ (γ t) / s t) * γ') := by rw [hsq, hODE]

#print axioms rawBetaHasDerivAtOfComplexCompLeft38
#print axioms rawBetaContinuousRootHasDerivAt38
#print axioms rawBetaContinuousRootHasDerivAtOfEq38
#print axioms rawBetaSheetPrimitiveHasDerivAt38

end
end NlsGge.GK38
