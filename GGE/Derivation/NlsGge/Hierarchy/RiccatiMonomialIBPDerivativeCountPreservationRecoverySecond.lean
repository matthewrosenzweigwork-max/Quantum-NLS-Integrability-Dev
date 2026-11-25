import NlsGge.Hierarchy.RiccatiDerivativeExcessAndPeriodicEvaluatorRecoverySecond
import NlsGge.Hierarchy.RiccatiHighJetIndexedWeightMinimumRecovery
import Mathlib.Data.Finsupp.Weight
import Mathlib.Tactic

set_option autoImplicit false

namespace NlsGge.HierarchyRiccati.Core

/-- The finite monomial branch in one IBP step preserves total derivative
count: the selected jet drops one order while a residual jet rises one. -/
theorem riccatiJetDerivativeOrderWeight_rebalance_eqNativeRecoverySecond
    (m : Jet →₀ ℕ) (v w : Jet)
    (hv : v ∈ m.support) (hw : w ∈ (m - Finsupp.single v 1).support)
    (horder : 0 < v.2) :
    riccatiJetDerivativeOrderWeightNativeRecovery
        ((m - Finsupp.single v 1) - Finsupp.single w 1 +
          Finsupp.single (v.1, v.2 - 1) 1 +
          Finsupp.single (w.1, w.2 + 1) 1) =
      riccatiJetDerivativeOrderWeightNativeRecovery m := by
  let d : Jet → ℕ := fun z => z.2
  let W : (Jet →₀ ℕ) → ℕ := Finsupp.weight d
  let r : Jet →₀ ℕ := m - Finsupp.single v 1
  let n : Jet →₀ ℕ :=
    (r - Finsupp.single w 1) + Finsupp.single (v.1, v.2 - 1) 1 +
      Finsupp.single (w.1, w.2 + 1) 1
  have hneV : m v ≠ 0 := Finsupp.mem_support_iff.mp hv
  have hsplitV : W r + d v = W m :=
    Finsupp.weight_sub_single_add (w := d) hneV
  have hneW : r w ≠ 0 := Finsupp.mem_support_iff.mp hw
  have hsplitW : W (r - Finsupp.single w 1) + d w = W r :=
    Finsupp.weight_sub_single_add (w := d) hneW
  have hweightN : W n =
      W (r - Finsupp.single w 1) + d (v.1, v.2 - 1) +
        d (w.1, w.2 + 1) := by
    change Finsupp.weight d
        ((r - Finsupp.single w 1 + Finsupp.single (v.1, v.2 - 1) 1) +
          Finsupp.single (w.1, w.2 + 1) 1) = _
    simp only [W, map_add, Finsupp.weight_single, one_smul]
  have hvSub : v.2 - 1 + 1 = v.2 :=
    Nat.sub_add_cancel (Nat.succ_le_iff.mpr horder)
  have hbranches :
      W (r - Finsupp.single w 1) + d (v.1, v.2 - 1) +
          d (w.1, w.2 + 1) = W r + d v := by
    dsimp [d] at hsplitW ⊢
    omega
  change W n = W m
  rw [hweightN, hbranches]
  exact hsplitV

end NlsGge.HierarchyRiccati.Core
