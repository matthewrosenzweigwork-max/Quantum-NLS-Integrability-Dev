import QuantumNLS.Loss
/-! integrator-authored trusted spec for R-8C922B25 lem:loss (review record r16 FULL ACCEPT): headline statement(s) copied verbatim from Loss (QuantumNLS.Loss). -/
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option linter.unusedSectionVars false
open scoped ContDiff NNReal
open Filter Topology Set Metric
noncomputable section
namespace QuantumNLS.R8C92Spec
open QuantumNLS.Loss
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

set_option maxHeartbeats 8000000 in
theorem loss_spec (𝒴 : InterpScale) [CompleteSpace X] {U : Set X} (hU : IsOpen U) {k : ℕ} (hk : 1 ≤ k)
    {q S : ℝ≥0} (hq : 0 < q) (hS : ((k : ℝ) + 1) * q < S) (hqS : q ≤ S)
    (f : X → 𝒴.Y 0) (hf : ContDiffOn ℝ ((k + 1 : ℕ) : ℕ∞ω) f U)
    (g : X → 𝒴.Y S) (hfg : ∀ x ∈ U, f x = 𝒴.emb S 0 (nn_zero_le S) (g x))
    (hg : ∀ x ∈ U, ∃ r > 0, ∃ M : ℝ, ∀ y ∈ U, dist y x < r → ‖g y‖ ≤ M) :
    ContDiffOn ℝ ((k : ℕ) : ℕ∞ω) (fun x => 𝒴.emb S q hqS (g x)) U ∧
      (∀ j ≤ k, ∀ x ∈ U, ∀ v : Fin j → X,
        𝒴.emb q 0 (nn_zero_le q) (iteratedFDeriv ℝ j (fun x => 𝒴.emb S q hqS (g x)) x v) =
          iteratedFDeriv ℝ j f x v) ∧
      (∀ x0 ∈ U, ∃ r > 0, ∃ B : ℝ, ∀ x ∈ ball x0 r, ∀ j ≤ k,
        ‖iteratedFDeriv ℝ j (fun x => 𝒴.emb S q hqS (g x)) x‖ ≤ B) := by
  exact QuantumNLS.Loss.loss 𝒴 hU hk hq hS hqS f hf g hfg hg

set_option maxHeartbeats 8000000 in
theorem loss_uniform_spec (𝒴 : InterpScale) [CompleteSpace X] {U : Set X} (hU : IsOpen U) {k : ℕ} (hk : 1 ≤ k)
    {q S : ℝ≥0} (hq : 0 < q) (hS : ((k : ℝ) + 1) * q < S) (hqS : q ≤ S)
    (f : X → 𝒴.Y 0) (hf : ContDiffOn ℝ ((k + 1 : ℕ) : ℕ∞ω) f U)
    (g : X → 𝒴.Y S) (hfg : ∀ x ∈ U, f x = 𝒴.emb S 0 (nn_zero_le S) (g x))
    (hg : ∀ x ∈ U, ∃ r > 0, ∃ M : ℝ, ∀ y ∈ U, dist y x < r → ‖g y‖ ≤ M)
    {K : Set X} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ V : Set X, IsOpen V ∧ K ⊆ V ∧ ∃ B : ℝ, ∀ x ∈ V, ∀ j ≤ k,
      ‖iteratedFDeriv ℝ j (fun x => 𝒴.emb S q hqS (g x)) x‖ ≤ B := by
  exact QuantumNLS.Loss.loss_uniform 𝒴 hU hk hq hS hqS f hf g hfg hg hK hKU

end QuantumNLS.R8C92Spec
#print axioms QuantumNLS.R8C92Spec.loss_spec
#print axioms QuantumNLS.R8C92Spec.loss_uniform_spec
