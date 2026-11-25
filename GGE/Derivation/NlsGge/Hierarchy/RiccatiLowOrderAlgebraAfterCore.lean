import NlsGge.Hierarchy.RiccatiAttachedRecursionCore
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic

set_option autoImplicit false

/-! Minimal post-core low-order algebra. This node contains no analytic jet
evaluation; the polynomial-evaluation bridge is isolated separately. -/

namespace NlsGge.HierarchyRiccati.Core

open scoped ComplexConjugate

theorem p_one : p 1 = -MvPolynomial.X (true, 0) := by
  simp [p]

private theorem attachedIcc_1_0_empty : (Finset.Icc 1 0).attach = ∅ := by
  rw [Finset.Icc_eq_empty_of_lt (by decide : (0 : ℕ) < 1), Finset.attach_empty]

theorem p_two : p 2 = -MvPolynomial.X (true, 1) := by
  rw [p_recurrence 0, p_one]
  simp [spatialD_jet, attachedIcc_1_0_empty]

private theorem attachedIcc_1_1_singleton :
    (Finset.Icc 1 1).attach = {⟨1, by simp⟩} := by
  ext l
  simp only [Finset.mem_attach, Finset.mem_singleton, true_iff]
  apply Subtype.ext
  change l.val = 1
  exact le_antisymm (Finset.mem_Icc.mp l.property).2
    (Finset.mem_Icc.mp l.property).1

theorem p_three :
    p 3 = -MvPolynomial.X (true, 2) +
      MvPolynomial.X (false, 0) *
        (MvPolynomial.X (true, 0) * MvPolynomial.X (true, 0)) := by
  rw [p_recurrence 1, p_two, attachedIcc_1_1_singleton]
  simp [p_one, spatialD_jet]

noncomputable section

/-- Formal mass density; its unit-circle integral is Q₀. -/
def formalQ0Density : Poly :=
  MvPolynomial.X (false, 0) * MvPolynomial.X (true, 0)

/-- The signed formal density `(-1)^(j+1) u p_(2j+1)`, before integration. -/
def formalChargeIntegrand (j : ℕ) : Poly :=
  MvPolynomial.C ((-1 : ℤ) ^ (j + 1)) *
    MvPolynomial.X (false, 0) * p (2 * j + 1)

theorem formalQ2Density_formula :
    formalChargeIntegrand 1 =
      -MvPolynomial.X (false, 0) * MvPolynomial.X (true, 2) +
        MvPolynomial.X (false, 0) *
          (MvPolynomial.X (false, 0) *
            (MvPolynomial.X (true, 0) * MvPolynomial.X (true, 0))) := by
  unfold formalChargeIntegrand
  rw [p_three]
  norm_num
  ring

end

end NlsGge.HierarchyRiccati.Core
