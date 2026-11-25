import NlsGge.Hierarchy.RiccatiAttachedRecursionCore
import Mathlib.Data.Finsupp.Order
import Mathlib.Data.Finsupp.Weight
import Mathlib.Tactic

set_option autoImplicit false

namespace NlsGge.HierarchyRiccati.Core

/-- Total derivative order counted with the actual source jet indices. -/
noncomputable def riccatiJetDerivativeOrderWeightNativeRecovery
    (m : Jet →₀ ℕ) : ℕ :=
  m.weight (fun v : Jet => v.2)

/-- Each supported coordinate contributes its own indexed derivative order
to the total weight. The index remains inside the summand throughout. -/
theorem riccatiJetDerivativeOrderWeight_coordinate_leNativeRecovery
    (m : Jet →₀ ℕ) (v : Jet) (hv : v ∈ m.support) :
    m v * v.2 ≤ riccatiJetDerivativeOrderWeightNativeRecovery m := by
  simpa [riccatiJetDerivativeOrderWeightNativeRecovery,
    Finsupp.weight_apply, smul_eq_mul] using
    (Finsupp.single_le_sum (f := m)
      (g := fun w (e : ℕ) => e * w.2)
      (by intro w e; exact Nat.zero_le _)
      v)

/-- Under the source excess bound, a jet factor at or above order `j` has
multiplicity exactly one. -/
theorem riccatiJet_high_factor_multiplicity_eq_oneNativeRecovery {j : ℕ}
    (hj : 2 ≤ j) (m : Jet →₀ ℕ) (v : Jet)
    (hcount : riccatiJetDerivativeOrderWeightNativeRecovery m ≤ 2 * j - 2)
    (hv : v ∈ m.support) (horder : j ≤ v.2) :
    m v = 1 := by
  have hne : m v ≠ 0 := Finsupp.mem_support_iff.mp hv
  have hpos : 0 < m v := Nat.pos_of_ne_zero hne
  have hterm : m v * v.2 ≤ riccatiJetDerivativeOrderWeightNativeRecovery m :=
    riccatiJetDerivativeOrderWeight_coordinate_leNativeRecovery m v hv
  by_contra hnot
  have hmult : 2 ≤ m v := by omega
  have hlarge : 2 * j ≤ m v * v.2 := Nat.mul_le_mul hmult horder
  omega

end NlsGge.HierarchyRiccati.Core
