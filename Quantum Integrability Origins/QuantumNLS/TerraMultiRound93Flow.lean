import QuantumNLS.TerraMultiRound92Bridge
import QuantumNLS.Bind7BR300B8640A01

/-! Compare any two hierarchy witnesses on their actual smooth trajectories.
The structures need not be equal away from smooth data, nor at unused orders. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.TerraMultiRound93Flow
open QuantumNLS.Def033HierarchyR24m QuantumNLS.ActualModelTargetR53a
variable {L κ : ℝ} [Fact (0 < L)]

theorem step_eq (F G : HigherFlows L κ) (R : Finset ℕ) (r : ℕ) (s : ℝ)
    (u : Smooth L) : smoothStep (hamFlows F R) r s u = smoothStep (hamFlows G R) r s u := by
  by_cases hr : r ∈ R
  · apply Subtype.ext
    simp only [smoothStep, hr, dif_pos]
    exact (flow_unique G r) (flowMap F r) (flow_isHam F r) u.val u.property s
  · simp [smoothStep, hr]

theorem fold_eq (F G : HigherFlows L κ) (R : Finset ℕ) (t : ℕ → ℝ)
    (l : List ℕ) (u : Smooth L) :
    l.foldr (fun r v => smoothStep (hamFlows F R) r (t r) v) u =
      l.foldr (fun r v => smoothStep (hamFlows G R) r (t r) v) u := by
  induction l with
  | nil => rfl
  | cons r l ih =>
    simp only [List.foldr_cons, ih]
    exact step_eq F G R r (t r) _

theorem joint_eq (F G : HigherFlows L κ) (R : Finset ℕ) (t : ℕ → ℝ) (u : Smooth L) :
    jointSmooth (hamFlows F R) t u = jointSmooth (hamFlows G R) t u :=
  fold_eq F G R t _ u

theorem selected_orbit_eq (hκ : 0 < κ)
    (w : QuantumNLS.PhysicalTensor.L2T L → QuantumNLS.REF88Chart.K)
    (hw : QuantumNLS.REF88PrintedChart.PrintedChart hκ w)
    (u : Smooth L) (R : Finset ℕ) (t : ℕ → ℝ) :
    QuantumNLS.DynSeedInputR47b.classicalOrbit hκ (QuantumNLS.Bind7BR300B8640A01.hierFlow hκ w hw) u R t =
    QuantumNLS.DynSeedInputR47b.classicalOrbit hκ
      (higher (QuantumNLS.ActualModelBindingR53a.hierarchy_intermediate hκ
        (QuantumNLS.RB7BindFinal.hierarchyInputR25m_unconditional hκ))) u R t := by
  exact congrArg physical (joint_eq _ _ R t u)

#print axioms step_eq
#print axioms joint_eq
#print axioms selected_orbit_eq
end QuantumNLS.TerraMultiRound93Flow
