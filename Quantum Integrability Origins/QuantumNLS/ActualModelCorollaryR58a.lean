import QuantumNLS.Prop025OLow

/-! Bind the fixed-box PROP-025 proof to the rebound R-E679E41D intermediate. -/
set_option autoImplicit false
noncomputable section

namespace QuantumNLS.ActualModelCorollaryR58a
open Def033HierarchyR24m BetheCoefficientTransform
open ActualModelTargetR53a ActualModelCorollaryR53a

variable {L κ : ℝ} [Fact (0 < L)]

/-- The fixed-box estimate at the printed DEF-044 interface. -/
theorem mixed_interface_intermediate (hκ : 0 < κ)
    (Prop021Input : Prop025OInputs.Prop021Input (L := L))
    (WindowInput : Prop025OInputs.WindowInput (L := L) hκ)
    (u : Smooth L) (hu : ‖physical u‖ = 1)
    (MixedInterface : Def044BindingR26m.MixedInterface hκ u hu)
    (I : Finset ℤ) (R : Finset ℕ) (k : ℕ) (Θ : ℤ → ℝ) (T : ℕ → ℝ)
    (hΘ : ∀ n ∈ I, 0 ≤ Θ n) (hT : ∀ r ∈ R, 0 ≤ T r) :
    MainEstimate hκ MixedInterface.chart.chart (higher MixedInterface.dynamics.hierarchy)
      u I R k Θ T :=
  Prop025OLow.prop025 hκ Prop021Input WindowInput u hu MixedInterface I R k Θ T hΘ hT

/-- The estimate on the actual chart and hierarchy, with DEF-044 realized by the R56a binding. -/
theorem cor_MP_actual_model_intermediate (hκ : 0 < κ)
    (Prop021Input : Prop025OInputs.Prop021Input (L := L))
    (WindowInput : Prop025OInputs.WindowInput (L := L) hκ)
    (HierarchyInput : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ)
    (u : Smooth L) (hu : ‖physical u‖ = 1)
    (I : Finset ℤ) (R : Finset ℕ) (k : ℕ) (Θ : ℤ → ℝ) (T : ℕ → ℝ)
    (hΘ : ∀ n ∈ I, 0 ≤ Θ n) (hT : ∀ r ∈ R, 0 ≤ T r) :
    MainEstimate hκ (ActualModelBindingR53a.chart (L := L) hκ)
      (higher (ActualModelBindingR53a.hierarchy_intermediate hκ HierarchyInput)) u I R k Θ T :=
  ActualModelCorollaryR56a.cor_MP_actual_model_intermediate hκ
    (Prop025OLow.prop025 hκ Prop021Input WindowInput) HierarchyInput u hu I R k Θ T hΘ hT

/-- The same estimate and the R56a window verification on the same hierarchy. -/
theorem actual_model_intermediate (hκ : 0 < κ)
    (Prop021Input : Prop025OInputs.Prop021Input (L := L))
    (WindowInput : Prop025OInputs.WindowInput (L := L) hκ)
    (HierarchyInput : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ)
    (u : Smooth L) (hu : ‖physical u‖ = 1)
    (I : Finset ℤ) (R : Finset ℕ) (k : ℕ) (Θ : ℤ → ℝ) (T : ℕ → ℝ)
    (hΘ : ∀ n ∈ I, 0 ≤ Θ n) (hT : ∀ r ∈ R, 0 ≤ T r) :
    let F := higher (ActualModelBindingR53a.hierarchy_intermediate hκ HierarchyInput)
    WindowEstimate F ∧ MainEstimate hκ (ActualModelBindingR53a.chart (L := L) hκ)
      F u I R k Θ T :=
  ActualModelCorollaryR56a.actual_model_intermediate hκ
    (Prop025OLow.prop025 hκ Prop021Input WindowInput) HierarchyInput WindowInput u hu I R k Θ T hΘ hT

end QuantumNLS.ActualModelCorollaryR58a
