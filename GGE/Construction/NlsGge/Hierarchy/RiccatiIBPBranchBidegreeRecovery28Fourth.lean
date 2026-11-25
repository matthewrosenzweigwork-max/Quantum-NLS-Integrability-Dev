import NlsGge.Hierarchy.RiccatiFinitePeriodicIBPBranchesRecovery28Second
import NlsGge.Hierarchy.RiccatiMonomialIBPDerivativeCountPreservationRecoverySecond
import NlsGge.Hierarchy.RiccatiChargeRemainderSupportOrderBoundsAfterBidegreeThirdRecoveryThird
import Mathlib.Data.Finsupp.Weight
import Mathlib.Tactic

set_option autoImplicit false

namespace NlsGge.HierarchyRiccati.Core

/-- The concrete finite branch retains the total number of field factors.
The derivative shifts affect only the jet order coordinates. -/
theorem riccatiJetIBPBranch_degree_eqNativeRecovery28Fourth
    (m : Jet →₀ ℕ) (v w : Jet)
    (hv : v ∈ m.support)
    (hw : w ∈ (m - Finsupp.single v 1).support) :
    (riccatiIBPBranchExponentNativeRecovery28Second
      (m - Finsupp.single v 1) v w).degree = m.degree := by
  classical
  let r : Jet →₀ ℕ := m - Finsupp.single v 1
  have hneV : m v ≠ 0 := Finsupp.mem_support_iff.mp hv
  have hsplitV : r.degree + 1 = m.degree := by
    have h := Finsupp.weight_sub_single_add (w := fun _ : Jet => 1) hneV
    simpa [r, Finsupp.degree_eq_weight_one] using h
  have hneW : r w ≠ 0 := Finsupp.mem_support_iff.mp hw
  have hsplitW : (r - Finsupp.single w 1).degree + 1 = r.degree := by
    have h := Finsupp.weight_sub_single_add (w := fun _ : Jet => 1) hneW
    simpa [Finsupp.degree_eq_weight_one] using h
  change (r - Finsupp.single w 1 +
      Finsupp.single (v.1, v.2 - 1) 1 +
      Finsupp.single (w.1, w.2 + 1) 1).degree = m.degree
  simp only [map_add, Finsupp.degree_single, one_smul]
  omega

/-- The concrete branch preserves the signed field gauge because the Boolean
jet labels are unchanged by both order shifts. -/
theorem riccatiJetIBPBranch_gauge_eqNativeRecovery28Fourth
    (m : Jet →₀ ℕ) (v w : Jet)
    (hv : v ∈ m.support)
    (hw : w ∈ (m - Finsupp.single v 1).support) :
    riccatiJetGaugeHomAfterComponents
        (riccatiIBPBranchExponentNativeRecovery28Second
          (m - Finsupp.single v 1) v w) =
      riccatiJetGaugeHomAfterComponents m := by
  classical
  let r : Jet →₀ ℕ := m - Finsupp.single v 1
  let g : Jet → ℤ := fun z => if z.1 then 1 else -1
  have hneV : m v ≠ 0 := Finsupp.mem_support_iff.mp hv
  have hdecompV : m = r + Finsupp.single v 1 := by
    exact (Finsupp.sub_add_single_one_cancel hneV).symm
  have hsplitV :
      riccatiJetGaugeHomAfterComponents r + g v =
        riccatiJetGaugeHomAfterComponents m := by
    have h := congrArg riccatiJetGaugeHomAfterComponents hdecompV
    rw [map_add, riccatiJetGaugeHomAfterComponents_single] at h
    simpa [g, add_comm] using h.symm
  have hneW : r w ≠ 0 := Finsupp.mem_support_iff.mp hw
  have hdecompW : r = (r - Finsupp.single w 1) + Finsupp.single w 1 :=
    (Finsupp.sub_add_single_one_cancel hneW).symm
  have hsplitW :
      riccatiJetGaugeHomAfterComponents (r - Finsupp.single w 1) + g w =
        riccatiJetGaugeHomAfterComponents r := by
    have h := congrArg riccatiJetGaugeHomAfterComponents hdecompW
    rw [map_add, riccatiJetGaugeHomAfterComponents_single] at h
    simpa [g, add_comm] using h.symm
  have hbranch :
      riccatiJetGaugeHomAfterComponents
          (riccatiIBPBranchExponentNativeRecovery28Second r v w) =
        riccatiJetGaugeHomAfterComponents (r - Finsupp.single w 1) +
          g (v.1, v.2 - 1) + g (w.1, w.2 + 1) := by
    simp [riccatiIBPBranchExponentNativeRecovery28Second, map_add,
      riccatiJetGaugeHomAfterComponents_single, g]
  have hvshift : g (v.1, v.2 - 1) = g v := by
    cases v with
    | mk b k => cases b <;> simp [g]
  have hwshift : g (w.1, w.2 + 1) = g w := by
    cases w with
    | mk b k => cases b <;> simp [g]
  dsimp [r] at hsplitV hsplitW hbranch ⊢
  rw [hbranch, hvshift, hwshift]
  omega

/-- Full source bidegree is invariant on each exact finite periodic-IBP
branch, including both field degree and signed gauge. -/
theorem riccatiJetIBPBranch_bidegree_eqNativeRecovery28Fourth
    (m : Jet →₀ ℕ) (v w : Jet)
    (hv : v ∈ m.support)
    (hw : w ∈ (m - Finsupp.single v 1).support)
    (horder : 0 < v.2) :
    riccatiJetBidegreeAfterComponents
        (riccatiIBPBranchExponentNativeRecovery28Second
          (m - Finsupp.single v 1) v w) =
      riccatiJetBidegreeAfterComponents m := by
  apply Prod.ext
  · change riccatiJetWeightHomAfterComponents
        (riccatiIBPBranchExponentNativeRecovery28Second
          (m - Finsupp.single v 1) v w) =
      riccatiJetWeightHomAfterComponents m
    rw [riccatiJetWeight_eq_degree_add_derivativeOrderSumNativeRecovery,
      riccatiJetWeight_eq_degree_add_derivativeOrderSumNativeRecovery,
      riccatiJetIBPBranch_degree_eqNativeRecovery28Fourth m v w hv hw]
    have hD := riccatiJetDerivativeOrderWeight_rebalance_eqNativeRecoverySecond
      m v w hv hw horder
    have hDsum :
        riccatiJetDerivativeOrderSumNativeRecovery
            (riccatiIBPBranchExponentNativeRecovery28Second
              (m - Finsupp.single v 1) v w) =
          riccatiJetDerivativeOrderSumNativeRecovery m := by
      simpa [riccatiJetDerivativeOrderSumNativeRecovery,
        riccatiJetDerivativeOrderWeightNativeRecovery,
        Finsupp.weight_apply, Finsupp.sum, smul_eq_mul,
        riccatiIBPBranchExponentNativeRecovery28Second] using hD
    exact congrArg (fun d : ℕ => m.degree + d) hDsum
  · exact riccatiJetIBPBranch_gauge_eqNativeRecovery28Fourth m v w hv hw

end NlsGge.HierarchyRiccati.Core
