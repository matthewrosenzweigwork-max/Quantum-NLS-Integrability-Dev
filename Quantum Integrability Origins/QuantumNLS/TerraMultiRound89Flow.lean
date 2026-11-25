import QuantumNLS.TerraMultiRound88Input
import QuantumNLS.RB7BindFinal
import QuantumNLS.RB7Conserve

/-! R-B2E70586: actual chart moduli are preserved by the actual selected
finite-family physical joint flow, including the low orders. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open QuantumNLS.Def033HierarchyR24m QuantumNLS.ActualModelTargetR53a
open QuantumNLS.HierarchyFlow
namespace QuantumNLS.TerraMultiRound89Flow
variable {L κ : ℝ} [Fact (0 < L)]

/-- Uniform-in-time cutoff along the actual selected smooth hierarchy flow. -/
theorem actual_flow_cutoff (hκ : 0 < κ) (u : Smooth L) (Rorders : Finset ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℕ, ∀ (t : ℕ → ℝ) (θ φ : ℤ → Circle),
      (∀ n : ℤ, |n| ≤ (R : ℤ) → θ n = φ n) →
      dist ((ActualModelBindingR53a.chart (L := L) hκ).Ψ
        (ActionTorus.rotate θ ((ActualModelBindingR53a.chart (L := L) hκ).Φ
          (physical (jointSmooth (hamFlows (higher (ActualModelBindingR53a.hierarchy_intermediate hκ
            (RB7BindFinal.hierarchyInputR25m_unconditional hκ))) Rorders) t u)))))
      ((ActualModelBindingR53a.chart (L := L) hκ).Ψ
        (ActionTorus.rotate φ ((ActualModelBindingR53a.chart (L := L) hκ).Φ
          (physical (jointSmooth (hamFlows (higher (ActualModelBindingR53a.hierarchy_intermediate hκ
            (RB7BindFinal.hierarchyInputR25m_unconditional hκ))) Rorders) t u))))) < ε := by
  let C := ActualModelBindingR53a.chart (L := L) hκ
  let F : HamFlows L κ Rorders := hamFlows (higher (ActualModelBindingR53a.hierarchy_intermediate hκ
    (RB7BindFinal.hierarchyInputR25m_unconditional (L := L) hκ))) Rorders
  obtain ⟨R, hR⟩ := TerraMultiRound88Input.actual_chart_cutoff hκ (physical u) ε hε
  refine ⟨R, fun t θ φ hθ => hR _ ?_ θ φ hθ⟩
  intro n
  have hj : QuantumNLS.ClassicalCharges.SmoothPeriodic L (jointClassicalFlow F t u.val) := by
    rw [← RB7BindTopology.jointSmooth_val F t u]
    exact (jointSmooth F t u).property
  have hn := RB7.joint_norm_const (Reg015HFinal.REG015_final (L := L) hκ)
    (RB7BindChart.chartFactsOf C) F t u.property hj n
  simpa only [RB7BindChart.chartFactsOf_Φ, physical,
    PhysicalProductPreparation.smoothClass, SmoothScalarMomentsPhysical.smoothL2,
    RB7BindTopology.jointSmooth_val] using hn

#print axioms actual_flow_cutoff
end QuantumNLS.TerraMultiRound89Flow
