import QuantumNLS.TerraMultiRound91Mixed
import QuantumNLS.RB7Commute

/-! Commutation of the selected physical hierarchy with finite angle rotation,
using its chart-frequency law and the invariance of frequencies on modulus
tori. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open scoped NNReal
open QuantumNLS.Def033HierarchyR24m QuantumNLS.ActualModelTargetR53a
open QuantumNLS.HierarchyFlow QuantumNLS.SmoothScalarMomentsPhysical
namespace QuantumNLS.TerraMultiRound91FlowRotation
variable {L κ : ℝ} [Fact (0 < L)]

theorem target_eq_rotation_after_flow (hκ : 0 < κ) (I : Finset ℤ) (orders : Finset ℕ)
    (θ : ℤ → ℝ) (t : ℕ → ℝ) (u : Smooth L) :
    let C := ActualModelBindingR53a.chart (L := L) hκ
    let F := higher (ActualModelBindingR53a.hierarchy_intermediate hκ
      (RB7BindFinal.hierarchyInputR25m_unconditional hκ))
    target C F I orders θ t u = rotate C I θ (physical (jointSmooth (hamFlows F orders) t u)) := by
  let C := ActualModelBindingR53a.chart (L := L) hκ
  let F : HigherFlows L κ := higher (ActualModelBindingR53a.hierarchy_intermediate hκ
    (RB7BindFinal.hierarchyInputR25m_unconditional (L := L) hκ))
  let G := hamFlows F orders
  let C' := RB7BindChart.chartFactsOf C
  let hR := Reg015HFinal.REG015_final (L := L) hκ
  let v := rotateSmooth C I θ u
  have hv (n : ℤ) : C.Φ (physical v) n = (angle I θ n : ℂ) * C.Φ (physical u) n := by
    rw [show physical v = rotate C I θ (physical u) from rotateSmooth_physical C I θ u]
    rw [rotate, C.right_inverse, ActionTorus.rotate_apply]
  have hfreq (r : ℕ) (n : ℤ) :
      RB7.FreqSeq ((RB7.SOf r : ℝ≥0) : ℝ) (RB7.Fd hR C' r)
        (fun m => C.Φ (physical v) m) n =
      RB7.FreqSeq ((RB7.SOf r : ℝ≥0) : ℝ) (RB7.Fd hR C' r)
        (fun m => C.Φ (physical u) m) n := by
    have hh := RB7.omegaOf_congr hR C' r u.property v.property (angle I θ) (by
      intro m
      simpa only [C', RB7BindChart.chartFactsOf_Φ, physical,
        PhysicalProductPreparation.smoothClass, SmoothScalarMomentsPhysical.smoothL2] using hv m) n
    have hvf := RB7.omegaOf_eq_FreqSeq hR C' r v.property n
    have huf := RB7.omegaOf_eq_FreqSeq hR C' r u.property n
    have hf := hvf.symm.trans (hh.trans huf)
    simpa only [C', RB7BindChart.chartFactsOf_Φ, physical,
      PhysicalProductPreparation.smoothClass, SmoothScalarMomentsPhysical.smoothL2] using hf
  have hflow (w : Smooth L) (n : ℤ) :
      C.Φ (physical (jointSmooth G t w)) n =
      Complex.exp (((-(∑ r ∈ orders, t r * RB7.FreqSeq ((RB7.SOf r : ℝ≥0) : ℝ)
        (RB7.Fd hR C' r) (fun m => C.Φ (physical w) m) n) : ℝ) : ℂ) * Complex.I) *
        C.Φ (physical w) n := by
    have hj : ClassicalCharges.SmoothPeriodic L (jointClassicalFlow G t w.val) := by
      rw [← RB7BindTopology.jointSmooth_val G t w]
      exact (jointSmooth G t w).property
    have hh := RB7.joint_rotation_form hR C' G t w.property hj n
    simpa only [C', RB7BindChart.chartFactsOf_Φ, physical,
      PhysicalProductPreparation.smoothClass, SmoothScalarMomentsPhysical.smoothL2,
      RB7BindTopology.jointSmooth_val] using hh
  change physical (jointSmooth G t v) = rotate C I θ (physical (jointSmooth G t u))
  apply (Function.LeftInverse.injective C.left_inverse)
  apply lp.ext
  funext n
  rw [hflow v n, rotate, C.right_inverse, ActionTorus.rotate_apply, hflow u n, hv n]
  have hsum : (∑ r ∈ orders, t r * RB7.FreqSeq ((RB7.SOf r : ℝ≥0) : ℝ)
        (RB7.Fd hR C' r) (fun m => C.Φ (physical v) m) n) =
      ∑ r ∈ orders, t r * RB7.FreqSeq ((RB7.SOf r : ℝ≥0) : ℝ)
        (RB7.Fd hR C' r) (fun m => C.Φ (physical u) m) n := by
    apply Finset.sum_congr rfl
    intro r hr
    rw [hfreq r n]
  rw [hsum]
  ring

#print axioms target_eq_rotation_after_flow
end QuantumNLS.TerraMultiRound91FlowRotation
