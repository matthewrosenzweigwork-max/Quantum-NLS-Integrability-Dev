import QuantumNLS.ActualModelCorollaryR58a
import QuantumNLS.Prop025FinalR01

/-! Final binding of R-E679E41D, cor:MP-actual-model. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Filter Topology

namespace QuantumNLS.ActualModelCorollaryR60a

open Def033HierarchyR24m (Smooth physical)
open BetheCoefficientTransform (HN)
open ActualModelTargetR53a (higher)
open ActualModelCorollaryR53a (MainEstimate EstimateWithZeta WindowEstimate boxError preparationError)

variable {L κ : ℝ} [Fact (0 < L)]

/-- The higher flows of the accepted hierarchy on the actual canonical chart. -/
abbrev actualFlows (hκ : 0 < κ) :=
  higher (ActualModelBindingR53a.hierarchy_intermediate hκ
    (RB7BindFinal.hierarchyInputR25m_unconditional (L := L) hκ))

/-- Mixed propagation on the actual periodic model, with the realized DEF-044 interface. -/
theorem cor_MP_actual_model (hκ : 0 < κ) (u : Smooth L) (hu : ‖physical u‖ = 1)
    (I : Finset ℤ) (R : Finset ℕ) (k : ℕ) (Θ : ℤ → ℝ) (T : ℕ → ℝ)
    (hΘ : ∀ n ∈ I, 0 ≤ Θ n) (hT : ∀ r ∈ R, 0 ≤ T r) :
    MainEstimate hκ (ActualModelBindingR53a.chart (L := L) hκ) (actualFlows hκ)
      u I R k Θ T :=
  Prop025FinalR01.prop025_at_DEF044 hκ u hu I R k Θ T hΘ hT

/-- The actual-model error sequence comes from the fixed finite-action packet. -/
theorem cor_MP_actual_model_packet (hκ : 0 < κ) (u : Smooth L) (hu : ‖physical u‖ = 1)
    (I : Finset ℤ) :
    Tendsto (Prop025ProvenanceR59a.fixedZeta hκ u hu I) atTop (𝓝 0) ∧
    (I = ∅ → ∀ N, Prop025ProvenanceR59a.fixedZeta hκ u hu I N = 0) ∧
    ∀ (R : Finset ℕ) (k : ℕ) (Θ : ℤ → ℝ) (T : ℕ → ℝ),
      (∀ n ∈ I, 0 ≤ Θ n) → (∀ r ∈ R, 0 ≤ T r) →
      ∃ A : ℝ, 0 ≤ A ∧ EstimateWithZeta hκ
        (ActualModelBindingR53a.chart (L := L) hκ) (actualFlows hκ)
        u I R k Θ T A (Prop025ProvenanceR59a.fixedZeta hκ u hu I) :=
  Prop025FinalR01.prop025_at_DEF044_packet hκ u hu I

/-- The box error tends to zero for every normalized norm-close preparation. -/
theorem cor_MP_actual_model_convergence (hκ : 0 < κ) (u : Smooth L) (hu : ‖physical u‖ = 1)
    (I : Finset ℤ) (R : Finset ℕ) (k : ℕ) (Θ : ℤ → ℝ) (T : ℕ → ℝ)
    (hΘ : ∀ n ∈ I, 0 ≤ Θ n) (hT : ∀ r ∈ R, 0 ≤ T r)
    (ψ : ∀ N : ℕ, HN L (N + 1)) (hψ : ∀ N, ‖ψ N‖ = 1)
    (hprep : Tendsto (fun N => preparationError u N (ψ N)) atTop (𝓝 0)) :
    Tendsto (fun N => if hk : k ≤ N + 1 then
      boxError hκ (ActualModelBindingR53a.chart (L := L) hκ) (actualFlows hκ)
        u I R Θ T k N hk (ψ N) else 0) atTop (𝓝 0) :=
  ActualModelCorollaryR53a.convergence hκ _ _ u I R k Θ T
    (cor_MP_actual_model hκ u hu I R k Θ T hΘ hT) ψ hψ hprep

/-- The same estimate together with the window verification on the actual flows. -/
theorem actual_model (hκ : 0 < κ) (u : Smooth L) (hu : ‖physical u‖ = 1)
    (I : Finset ℤ) (R : Finset ℕ) (k : ℕ) (Θ : ℤ → ℝ) (T : ℕ → ℝ)
    (hΘ : ∀ n ∈ I, 0 ≤ Θ n) (hT : ∀ r ∈ R, 0 ≤ T r) :
    WindowEstimate (actualFlows (L := L) hκ) ∧
    MainEstimate hκ (ActualModelBindingR53a.chart (L := L) hκ) (actualFlows hκ)
      u I R k Θ T :=
  ⟨ActualModelCorollaryR53a.actual_window_intermediate hκ (Bind7BE59628C9H01.window_bound hκ) _,
    cor_MP_actual_model hκ u hu I R k Θ T hΘ hT⟩

end QuantumNLS.ActualModelCorollaryR60a
