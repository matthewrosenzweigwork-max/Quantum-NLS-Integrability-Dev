import QuantumNLS.ActualModelCorollaryR60a
/-! integrator-authored trusted spec for R-E679E41D cor:MP-actual-model (final, no named inputs): headline statement(s) copied verbatim from ActualModelCorollaryR60a (QuantumNLS.ActualModelCorollaryR60a). -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Filter Topology
namespace QuantumNLS.RE679Spec
open QuantumNLS.ActualModelCorollaryR60a
open Def033HierarchyR24m (Smooth physical)
open BetheCoefficientTransform (HN)
open ActualModelTargetR53a (higher)
open ActualModelCorollaryR53a (MainEstimate EstimateWithZeta WindowEstimate boxError preparationError)
variable {L κ : ℝ} [Fact (0 < L)]

set_option maxHeartbeats 8000000 in
theorem cor_MP_actual_model_spec (hκ : 0 < κ) (u : Smooth L) (hu : ‖physical u‖ = 1)
    (I : Finset ℤ) (R : Finset ℕ) (k : ℕ) (Θ : ℤ → ℝ) (T : ℕ → ℝ)
    (hΘ : ∀ n ∈ I, 0 ≤ Θ n) (hT : ∀ r ∈ R, 0 ≤ T r) :
    MainEstimate hκ (ActualModelBindingR53a.chart (L := L) hκ) (actualFlows hκ)
      u I R k Θ T := by
  first
  | exact QuantumNLS.ActualModelCorollaryR60a.cor_MP_actual_model
  | (apply QuantumNLS.ActualModelCorollaryR60a.cor_MP_actual_model <;> assumption)

set_option maxHeartbeats 8000000 in
theorem cor_MP_actual_model_packet_spec (hκ : 0 < κ) (u : Smooth L) (hu : ‖physical u‖ = 1)
    (I : Finset ℤ) :
    Tendsto (Prop025ProvenanceR59a.fixedZeta hκ u hu I) atTop (𝓝 0) ∧
    (I = ∅ → ∀ N, Prop025ProvenanceR59a.fixedZeta hκ u hu I N = 0) ∧
    ∀ (R : Finset ℕ) (k : ℕ) (Θ : ℤ → ℝ) (T : ℕ → ℝ),
      (∀ n ∈ I, 0 ≤ Θ n) → (∀ r ∈ R, 0 ≤ T r) →
      ∃ A : ℝ, 0 ≤ A ∧ EstimateWithZeta hκ
        (ActualModelBindingR53a.chart (L := L) hκ) (actualFlows hκ)
        u I R k Θ T A (Prop025ProvenanceR59a.fixedZeta hκ u hu I) := by
  first
  | exact QuantumNLS.ActualModelCorollaryR60a.cor_MP_actual_model_packet
  | (apply QuantumNLS.ActualModelCorollaryR60a.cor_MP_actual_model_packet <;> assumption)

set_option maxHeartbeats 8000000 in
theorem cor_MP_actual_model_convergence_spec (hκ : 0 < κ) (u : Smooth L) (hu : ‖physical u‖ = 1)
    (I : Finset ℤ) (R : Finset ℕ) (k : ℕ) (Θ : ℤ → ℝ) (T : ℕ → ℝ)
    (hΘ : ∀ n ∈ I, 0 ≤ Θ n) (hT : ∀ r ∈ R, 0 ≤ T r)
    (ψ : ∀ N : ℕ, HN L (N + 1)) (hψ : ∀ N, ‖ψ N‖ = 1)
    (hprep : Tendsto (fun N => preparationError u N (ψ N)) atTop (𝓝 0)) :
    Tendsto (fun N => if hk : k ≤ N + 1 then
      boxError hκ (ActualModelBindingR53a.chart (L := L) hκ) (actualFlows hκ)
        u I R Θ T k N hk (ψ N) else 0) atTop (𝓝 0) := by
  first
  | exact QuantumNLS.ActualModelCorollaryR60a.cor_MP_actual_model_convergence
  | (apply QuantumNLS.ActualModelCorollaryR60a.cor_MP_actual_model_convergence <;> assumption)

end QuantumNLS.RE679Spec
#print axioms QuantumNLS.RE679Spec.cor_MP_actual_model_spec
#print axioms QuantumNLS.RE679Spec.cor_MP_actual_model_packet_spec
#print axioms QuantumNLS.RE679Spec.cor_MP_actual_model_convergence_spec
