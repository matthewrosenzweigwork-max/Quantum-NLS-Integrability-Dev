import NlsGge.Hierarchy.RiccatiSmoothJetDerivativeAfterProductPrerequisite
import NlsGge.Hierarchy.RiccatiPeriodicIteratedDerivClosurePrerequisite
import Mathlib.Data.Finsupp.Weight
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

namespace NlsGge.HierarchyRiccati.Core

open scoped ContDiff

/-- The finite excess above the normal-form cutoff `j - 1`. -/
def riccatiJetDerivativeExcessNativeRecovery (j : ℕ) (m : Jet →₀ ℕ) : ℕ :=
  m.weight (fun v : Jet => v.2 - (j - 1))

/-- Replacing a selected order-`r` factor by order `r-1` and a residual
factor of order at most `j-2` by its order-`s+1` derivative lowers the actual
finite derivative excess by exactly one. This is the well-founded measure
step for the periodic IBP normalizer. -/
theorem riccatiJetDerivativeExcess_rebalance_strictly_decreasesNativeRecovery
    {j : ℕ} (hj : 2 ≤ j) (m : Jet →₀ ℕ) (v w : Jet)
    (hv : v ∈ m.support) (hmv : m v = 1) (horder : j ≤ v.2)
    (hw : w ∈ (m - Finsupp.single v 1).support)
    (hresOrder : w.2 ≤ j - 2) :
    riccatiJetDerivativeExcessNativeRecovery j
        ((m - Finsupp.single v 1) - Finsupp.single w 1 +
          Finsupp.single (v.1, v.2 - 1) 1 +
          Finsupp.single (w.1, w.2 + 1) 1) <
      riccatiJetDerivativeExcessNativeRecovery j m := by
  let e : Jet → ℕ := fun z => z.2 - (j - 1)
  let W : (Jet →₀ ℕ) → ℕ := Finsupp.weight e
  let r : Jet →₀ ℕ := m - Finsupp.single v 1
  let n : Jet →₀ ℕ :=
    (r - Finsupp.single w 1) + Finsupp.single (v.1, v.2 - 1) 1 +
      Finsupp.single (w.1, w.2 + 1) 1
  have hvm : m v ≠ 0 := by rw [hmv]; decide
  have hsplitV : W r + e v = W m :=
    Finsupp.weight_sub_single_add (w := e) hvm
  have hwne : r w ≠ 0 := Finsupp.mem_support_iff.mp hw
  have hsplitW : W (r - Finsupp.single w 1) + e w = W r :=
    Finsupp.weight_sub_single_add (w := e) hwne
  have hwExcess : e w = 0 := by
    dsimp [e]
    omega
  have hwShiftExcess : e (w.1, w.2 + 1) = 0 := by
    dsimp [e]
    omega
  have hvShiftExcess : e v = e (v.1, v.2 - 1) + 1 := by
    dsimp [e]
    omega
  have hremoveW : W (r - Finsupp.single w 1) = W r := by
    omega
  have hweightN : W n =
      W (r - Finsupp.single w 1) + e (v.1, v.2 - 1) +
        e (w.1, w.2 + 1) := by
    change Finsupp.weight e
        ((r - Finsupp.single w 1 + Finsupp.single (v.1, v.2 - 1) 1) +
          Finsupp.single (w.1, w.2 + 1) 1) = _
    simp only [W, map_add, Finsupp.weight_single, one_smul]
  have hdecrease : W n + 1 = W m := by
    calc
      W n + 1 =
          W (r - Finsupp.single w 1) + e (v.1, v.2 - 1) +
            e (w.1, w.2 + 1) + 1 := by rw [hweightN]
      _ = W r + e (v.1, v.2 - 1) + 1 := by
        rw [hremoveW, hwShiftExcess]
      _ = W r + e v := by omega
      _ = W m := hsplitV
  change W n < W m
  omega

/-- Smooth periodicity passes from the field to each actual jet. The source
convention is explicit: `true` selects `star ∘ u`, while `false` selects `u`.
-/
theorem riccatiJetFunction_periodic_of_smooth_periodicNativeRecovery
    (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
    (hper : Function.Periodic u 1) (v : Jet) :
    Function.Periodic (riccatiJetFunction u v) 1 := by
  have hstar : ContDiff ℝ ∞ (fun x => star (u x)) :=
    ((starL ℝ : ℂ ≃L⋆[ℝ] ℂ).toContinuousLinearMap).contDiff.comp hu
  have hstarPer : Function.Periodic (fun x => star (u x)) 1 := by
    intro x
    change star (u (x + 1)) = star (u x)
    exact congrArg star (hper x)
  have hperAll : ∀ n : ℕ, Function.Periodic (iteratedDeriv n u) 1 :=
    fun n => periodic_iteratedDeriv_of_contDiff u hu hper n
  have hstarPerAll : ∀ n : ℕ,
      Function.Periodic (iteratedDeriv n (fun x => star (u x))) 1 :=
    fun n => periodic_iteratedDeriv_of_contDiff
      (fun x => star (u x)) hstar hstarPer n
  rcases v with ⟨b, n⟩
  cases b with
  | false =>
      simpa [riccatiJetFunction] using hperAll n
  | true =>
      simpa [riccatiJetFunction] using hstarPerAll n

/-- Periodicity of every evaluated jet gives periodicity of evaluation of any
actual polynomial in the jet variables. -/
theorem riccatiJetEvaluation_periodic_of_periodic_jetsNativeRecovery
    (u : ℝ → ℂ) (P : Poly)
    (hjets : ∀ v : Jet, Function.Periodic (riccatiJetFunction u v) 1) :
    Function.Periodic (fun x => riccatiJetEvaluation u x P) 1 := by
  intro x
  change polynomialEvaluation
      (fun v => riccatiJetFunction u v (x + 1)) P =
    polynomialEvaluation (fun v => riccatiJetFunction u v x) P
  apply congrArg (fun values : Jet → ℂ => polynomialEvaluation values P)
  funext v
  exact hjets v x

/-- The generic smooth-periodic polynomial evaluator package, specialized to
the source's actual Boolean jet convention. -/
theorem riccatiJetEvaluation_periodic_of_smooth_periodicNativeRecovery
    (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
    (hper : Function.Periodic u 1) (P : Poly) :
    Function.Periodic (fun x => riccatiJetEvaluation u x P) 1 := by
  apply riccatiJetEvaluation_periodic_of_periodic_jetsNativeRecovery
  intro v
  exact riccatiJetFunction_periodic_of_smooth_periodicNativeRecovery
    u hu hper v

end NlsGge.HierarchyRiccati.Core

end
