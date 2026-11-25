import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Data.Finset.Interval
import Mathlib.Tactic

set_option autoImplicit false

/-! Isolated E06.01–.02 core: independent jet variables, spatial derivation,
and the actual finite attached convolution in the source Riccati recursion.
This file deliberately omits support invariants, low-order calculations,
integration, and spectral-charge claims. -/

namespace NlsGge.HierarchyRiccati.Core

abbrev Jet := Bool × ℕ
abbrev Poly := MvPolynomial Jet ℤ

noncomputable def spatialD : Derivation ℤ Poly Poly :=
  MvPolynomial.mkDerivation ℤ (fun v : Jet => MvPolynomial.X (v.1, v.2 + 1))

@[simp] theorem spatialD_jet (v : Jet) :
    spatialD (MvPolynomial.X v) = MvPolynomial.X (v.1, v.2 + 1) := by
  change MvPolynomial.mkDerivation ℤ
    (fun w : Jet => MvPolynomial.X (w.1, w.2 + 1)) (MvPolynomial.X v) = _
  exact MvPolynomial.mkDerivation_X (R := ℤ) (σ := Jet) (A := Poly)
    (fun w => MvPolynomial.X (w.1, w.2 + 1)) v

/-- Natural bounds carried by an attached convolution index. -/
theorem attachedIcc_bounds (k : ℕ) (l : {n : ℕ // n ∈ Finset.Icc 1 k}) :
    1 ≤ l.1 ∧ l.1 ≤ k :=
  Finset.mem_Icc.mp l.2

/-- The totalized Riccati sequence.  The index 0 is assigned zero; the source
recursion starts at index 1 and never uses that value in its convolution. -/
noncomputable def p : ℕ → Poly
  | 0 => 0
  | 1 => -MvPolynomial.X (true, 0)
  | k + 2 =>
      spatialD (p (k + 1)) +
        MvPolynomial.X (false, 0) *
          (Finset.Icc 1 k).attach.sum fun l => p (k + 1 - l.1) * p l.1
termination_by n => n
decreasing_by
  all_goals
    try omega
    all_goals
      have hl := Finset.mem_Icc.mp l.2
      omega

/-- Exact attached-finset form of the paper's finite-sum recursion. -/
theorem p_recurrence (k : ℕ) :
    p (k + 2) = spatialD (p (k + 1)) +
      MvPolynomial.X (false, 0) *
        (Finset.Icc 1 k).attach.sum fun l => p (k + 1 - l.1) * p l.1 := by
  simp [p]

end NlsGge.HierarchyRiccati.Core
