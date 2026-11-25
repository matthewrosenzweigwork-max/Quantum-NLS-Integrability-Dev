import QuantumNLS.TerraMultiRound89Flow
import QuantumNLS.TerraMultiRound88Tensor

/-! Uniform classical projector cutoff for the selected actual hierarchy. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open QuantumNLS.Def033HierarchyR24m QuantumNLS.ActualModelTargetR53a
open QuantumNLS.HierarchyFlow QuantumNLS.PhysicalTensor
namespace QuantumNLS.TerraMultiRound91ClassicalCutoff
variable {L κ : ℝ} [Fact (0 < L)]

theorem rotate_norm (hκ : 0 < κ) (x : L2T L) (θ : ℤ → Circle) :
    let C := ActualModelBindingR53a.chart (L := L) hκ
    ‖C.Ψ (ActionTorus.rotate θ (C.Φ x))‖ = ‖x‖ := by
  let C := ActualModelBindingR53a.chart (L := L) hκ
  have hh : ‖C.Φ (C.Ψ (ActionTorus.rotate θ (C.Φ x)))‖ = ‖C.Φ x‖ := by
    rw [C.right_inverse]
    apply ResetNormalizationUniqueness.norm_eq_of_norm_apply_eq
    intro n
    rw [ActionTorus.rotate_apply, norm_mul, Circle.norm_coe, one_mul]
  have h1 := C.norm (C.Ψ (ActionTorus.rotate θ (C.Φ x)))
  have h2 := C.norm x
  rw [hh] at h1
  nlinarith [norm_nonneg (C.Ψ (ActionTorus.rotate θ (C.Φ x))), norm_nonneg x]

theorem selected_flow_norm (hκ : 0 < κ) (u : Smooth L) (orders : Finset ℕ) (t : ℕ → ℝ) :
    let C := ActualModelBindingR53a.chart (L := L) hκ
    let F := higher (ActualModelBindingR53a.hierarchy_intermediate hκ
      (RB7BindFinal.hierarchyInputR25m_unconditional hκ))
    ‖physical (jointSmooth (hamFlows F orders) t u)‖ = ‖physical u‖ := by
  let C := ActualModelBindingR53a.chart (L := L) hκ
  let F : HigherFlows L κ := higher (ActualModelBindingR53a.hierarchy_intermediate hκ
    (RB7BindFinal.hierarchyInputR25m_unconditional (L := L) hκ))
  let G := hamFlows F orders
  have hj : ClassicalCharges.SmoothPeriodic L (jointClassicalFlow G t u.val) := by
    rw [← RB7BindTopology.jointSmooth_val G t u]
    exact (jointSmooth G t u).property
  have hh : ‖C.Φ (physical (jointSmooth G t u))‖ = ‖C.Φ (physical u)‖ := by
    apply ResetNormalizationUniqueness.norm_eq_of_norm_apply_eq
    intro n
    have hn := RB7.joint_norm_const (Reg015HFinal.REG015_final (L := L) hκ)
      (RB7BindChart.chartFactsOf C) G t u.property hj n
    simpa only [RB7BindChart.chartFactsOf_Φ, physical,
      PhysicalProductPreparation.smoothClass, SmoothScalarMomentsPhysical.smoothL2,
      RB7BindTopology.jointSmooth_val] using hn
  have h1 := C.norm (physical (jointSmooth G t u))
  have h2 := C.norm (physical u)
  rw [hh] at h1
  nlinarith [norm_nonneg (physical (jointSmooth G t u)), norm_nonneg (physical u)]

/-- Uniform over all times and circle angles, including k=0. -/
theorem classical_projector_cutoff (hκ : 0 < κ) (u : Smooth L) (hu : ‖physical u‖ = 1)
    (orders : Finset ℕ) (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℕ, ∀ (t : ℕ → ℝ) (θ φ : ℤ → Circle),
      (∀ n : ℤ, |n| ≤ (R : ℤ) → θ n = φ n) →
      let C := ActualModelBindingR53a.chart (L := L) hκ
      let F := higher (ActualModelBindingR53a.hierarchy_intermediate hκ
        (RB7BindFinal.hierarchyInputR25m_unconditional hκ))
      let x := physical (jointSmooth (hamFlows F orders) t u)
      TraceClass.traceNorm (Prop025OInputs.tensorProj k (C.Ψ (ActionTorus.rotate θ (C.Φ x))) -
        Prop025OInputs.tensorProj k (C.Ψ (ActionTorus.rotate φ (C.Φ x)))) ≤ ENNReal.ofReal ε := by
  let δ := ε / (2 * (k : ℝ) + 1)
  have hden : 0 < 2 * (k : ℝ) + 1 := by positivity
  have hδ : 0 < δ := div_pos hε hden
  obtain ⟨R, hR⟩ := TerraMultiRound89Flow.actual_flow_cutoff hκ u orders δ hδ
  refine ⟨R, ?_⟩
  intro t θ φ heq
  let C := ActualModelBindingR53a.chart (L := L) hκ
  let F : HigherFlows L κ := higher (ActualModelBindingR53a.hierarchy_intermediate hκ
    (RB7BindFinal.hierarchyInputR25m_unconditional (L := L) hκ))
  let x := physical (jointSmooth (hamFlows F orders) t u)
  have hx : ‖x‖ = 1 := by rw [selected_flow_norm hκ u orders t, hu]
  have hnθ : ‖C.Ψ (ActionTorus.rotate θ (C.Φ x))‖ = 1 := by rw [rotate_norm hκ x θ, hx]
  have hnφ : ‖C.Ψ (ActionTorus.rotate φ (C.Φ x))‖ = 1 := by rw [rotate_norm hκ x φ, hx]
  have hdist := hR t θ φ heq
  rw [dist_eq_norm] at hdist
  refine (TerraMultiRound88Tensor.tensor_projector_lipschitz k _ _ hnθ hnφ).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have hk : 0 ≤ 2 * (k : ℝ) := by positivity
  have hd : 2 * (k : ℝ) * δ ≤ ε := by
    dsimp [δ]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hden).2
    nlinarith
  exact (mul_le_mul_of_nonneg_left hdist.le hk).trans hd

#print axioms rotate_norm
#print axioms selected_flow_norm
#print axioms classical_projector_cutoff
end QuantumNLS.TerraMultiRound91ClassicalCutoff
