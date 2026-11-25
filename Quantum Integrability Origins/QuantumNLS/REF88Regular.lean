import Mathlib
import QuantumNLS.L2Flow
import QuantumNLS.F04Global

/-!
# REF88Regular: a regular solution is the physical flow (R-EF8C2837, "Physical rotations on finite
action supports")

Source: `source-text/chapters/global/physical_cubic.tex`, proof, paragraph "Physical rotations on finite
action supports", lines 142 to 175 (printed): "The coordinate curve is continuous in every `h^s`, and its
inverse image is continuous in every `H^s` ... It is differentiable in `L²` by the full analytic inverse.
Consequently it is a regular solution of the physical NLS equation.  The physical uniqueness from
Theorem `thm:root-L2-flow` identifies it with `S^t u`."

This module proves exactly the italicised implication, for a curve in `H²`:

* `regular_isDistSol`: a curve `g : ℝ → h^2` (F04 weights, `h04 L 2`) that is continuous into `h^1` and
  `L²`-differentiable with derivative `i∂_x²u - 2iκ|u|²u` (the F04 field `Gder` at `s = 2`) is a
  `C_tH¹` distributional solution (`IsDistSol`), by the coefficientwise weak form of the scalar ODE;
* `regular_eq_flow`: such a curve, started at `g 0`, is the physical `L²` flow `S^t` of the accepted
  R-AEE17FD6 / `L2Flow` (`flowMap`), through the accepted F04 `thm_global` uniqueness among `C_tH¹`
  distributional solutions and the accepted agreement of the `H¹` flow with `flowMap`.

Everything used is accepted and read-only (`LocalWellPosednessFull`, `F04Global.thm_global`,
`L2Flow.flowMap_H1`).  No chart, no REG-015, no quantum input is used here.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open scoped ComplexConjugate ContDiff
open MeasureTheory Filter Topology Set

namespace QuantumNLS.REF88Regular

open QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight QuantumNLS.Fourier QuantumNLS.LocalWellPosedness
  QuantumNLS.LocalWellPosednessFull QuantumNLS.H1Bridge QuantumNLS.L2Flow

variable {L : ℝ} [Fact (0 < L)]

/-- Weak form of a linear ODE: if `A' = -i(λA + μB)` with `A, B` continuous, then tested against a
`C_c^∞` function `-i ∫ φ' A = ∫ φ (λA + μB)`.  (Same elementary integration by parts as in the
non-promoted DEF-024 stage `Def024CubicUnique.weak_of_ode`; re-proved here to avoid importing it.) -/
theorem weak_of_ode {A B : ℝ → ℂ} {lam mu : ℂ}
    (hA : ∀ t, HasDerivAt A (-Complex.I * (lam * A t + mu * B t)) t)
    (hAc : Continuous A) (hBc : Continuous B) {φ : ℝ → ℝ} (hφ : IsTest univ φ) :
    -Complex.I * ∫ t, deriv φ t • A t = ∫ t, φ t • (lam * A t + mu * B t) := by
  have hφd : ∀ t, HasDerivAt (fun t => (φ t : ℂ)) ((deriv φ t : ℝ) : ℂ) t := fun t =>
    ((hφ.1.differentiable (by simp) t).hasDerivAt).ofReal_comp
  have hφc : Continuous fun t => (φ t : ℂ) := Complex.continuous_ofReal.comp hφ.1.continuous
  have hdφ := hφ.deriv
  have hφ'c : Continuous fun t => ((deriv φ t : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp hdφ.1.continuous
  have hφs : HasCompactSupport fun t => (φ t : ℂ) :=
    hφ.2.1.comp_left Complex.ofReal_zero
  have hφ's : HasCompactSupport fun t => ((deriv φ t : ℝ) : ℂ) :=
    hdφ.2.1.comp_left Complex.ofReal_zero
  have hX : Continuous fun t => -Complex.I * (lam * A t + mu * B t) :=
    continuous_const.mul ((continuous_const.mul hAc).add (continuous_const.mul hBc))
  have hint1 : Integrable fun t => (φ t : ℂ) * (-Complex.I * (lam * A t + mu * B t)) :=
    (hφc.mul hX).integrable_of_hasCompactSupport (hφs.mul_right)
  have hint2 : Integrable fun t => ((deriv φ t : ℝ) : ℂ) * A t :=
    (hφ'c.mul hAc).integrable_of_hasCompactSupport (hφ's.mul_right)
  have hint3 : Integrable fun t => (φ t : ℂ) * A t :=
    (hφc.mul hAc).integrable_of_hasCompactSupport (hφs.mul_right)
  have ibp := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun t => (φ t : ℂ)) (u' := fun t => ((deriv φ t : ℝ) : ℂ)) (v := A)
    (v' := fun t => -Complex.I * (lam * A t + mu * B t))
    (fun t _ => hφd t) (fun t _ => hA t) hint1 hint2 hint3
  beta_reduce at ibp
  have key : ∫ t, ((deriv φ t : ℝ) : ℂ) * A t =
      -(∫ t, (φ t : ℂ) * (-Complex.I * (lam * A t + mu * B t))) := by
    rw [ibp, neg_neg]
  have e1 : ∫ t, (φ t : ℂ) * (-Complex.I * (lam * A t + mu * B t)) =
      -Complex.I * ∫ t, (φ t : ℂ) * (lam * A t + mu * B t) := by
    rw [← integral_const_mul]
    congr 1
    funext t
    ring
  simp only [Complex.real_smul]
  rw [key, e1]
  linear_combination (-(∫ t, (φ t : ℂ) * (lam * A t + mu * B t))) * Complex.I_sq

/-- The inclusion `h^2 ↪ h^1`. -/
abbrev m21 : h04 L 2 →L[ℂ] h04 L 1 := h04_mono L (by norm_num : (1 : ℝ) ≤ 2)

lemma m21_val (a : h04 L 2) : (m21 a).val = a.val := incl_val _ _ _ _ a

lemma ι2_val (a : h04 L 2) : (ι2 2 a).val = a.val := incl_val _ _ _ _ a

lemma Fh_m21 (a : h04 L 2) (n : ℤ) :
    (Fh (le_refl (1 : ℝ)) (m21 a)).val n = (Fh (by norm_num : (1 : ℝ) ≤ 2) a).val n := by
  show coeff L (nlRep L (m21 a).val) n = coeff L (nlRep L a.val) n
  rw [m21_val]

/-- **A regular solution is a `C_tH¹` distributional solution.**  `g : ℝ → h^2` is continuous into
`h^1`, and `t ↦ ι g(t) ∈ L²` (here `h04 L (2-2)`) is differentiable with derivative the F04 field
`Gder = i∂_x²u - 2iκ|u|²u` at every time. -/
theorem regular_isDistSol {κ : ℝ} {g : ℝ → h04 L 2}
    (hcont : Continuous fun t => m21 (g t))
    (hder : ∀ t, HasDerivAt (fun t => ι2 2 (g t)) (Gder (by norm_num : (1 : ℝ) ≤ 2) κ (g t)) t) :
    IsDistSol κ Set.univ (fun t => m21 (g t)) := by
  refine ⟨isOpen_univ, Set.ordConnected_univ, hcont.continuousOn, fun n φ hφ => ?_⟩
  have hAc : Continuous fun t => (m21 (g t)).val n := by
    have := (coefL 1 n).continuous.comp hcont
    simpa only [Function.comp_def, coefL_apply] using this
  have hBc : Continuous fun t => (Fh (le_refl (1 : ℝ)) (m21 (g t))).val n := by
    have := (coefL 1 n).continuous.comp ((continuous_Fh (le_refl (1 : ℝ))).comp hcont)
    simpa only [Function.comp_def, coefL_apply] using this
  have hAd : ∀ t, HasDerivAt (fun t => (m21 (g t)).val n)
      (-Complex.I * (((freq L n ^ 2 : ℝ) : ℂ) * (m21 (g t)).val n +
        ((2 * κ : ℝ) : ℂ) * (Fh (le_refl (1 : ℝ)) (m21 (g t))).val n)) t := by
    intro t
    have h1 := ((coefL (2 - 2) n).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t (hder t)
    have hfun : (fun t => (m21 (g t)).val n) =
        (⇑((coefL (2 - 2) n).restrictScalars ℝ) ∘ fun t => ι2 2 (g t)) := by
      funext s
      simp only [Function.comp_apply, ContinuousLinearMap.coe_restrictScalars', coefL_apply]
      rw [m21_val, ι2_val]
    rw [hfun]
    refine h1.congr_deriv ?_
    simp only [ContinuousLinearMap.coe_restrictScalars', coefL_apply]
    rw [Gder_val, m21_val, Fh_m21]
    push_cast
    ring
  exact weak_of_ode (A := fun t => (m21 (g t)).val n)
    (B := fun t => (Fh (le_refl (1 : ℝ)) (m21 (g t))).val n)
    (lam := ((freq L n ^ 2 : ℝ) : ℂ)) (mu := ((2 * κ : ℝ) : ℂ)) hAd hAc hBc hφ

/-- **The regular solution is the physical flow.**  A regular `h²` curve with
`g 0 = a₀` satisfies `u(t) = S^t u(0)`, where `S^t` is the accepted `L²` physical flow `flowMap` of
`thm:root-L2-flow` and `u(t)` is the `L²` function with Fourier coefficients `g(t)`. -/
theorem regular_eq_flow {κ : ℝ} (hκ : 0 ≤ κ) {g : ℝ → h04 L 2}
    (hcont : Continuous fun t => m21 (g t))
    (hder : ∀ t, HasDerivAt (fun t => ι2 2 (g t)) (Gder (by norm_num : (1 : ℝ) ≤ 2) κ (g t)) t)
    (t : ℝ) :
    emb (m21 (g t)) = flowMap hκ (emb (m21 (g 0))) t := by
  have hD := regular_isDistSol (κ := κ) hcont hder
  have huniq := (QuantumNLS.F04Global.thm_global (L := L) hκ (m21 (g 0))).2.2.2.2.2.1
    (fun t => m21 (g t)) hD rfl t
  rw [flowMap_H1 hκ (m21 (g 0)) t, huniq]

#print axioms regular_isDistSol
#print axioms regular_eq_flow

end QuantumNLS.REF88Regular
