import QuantumNLS.HilbertL1CompactLiteral

/-! integrator-authored trusted spec for R-1D98F7EC `lem:global-Hilbert-l1-compact`
(global/product_torus.tex:70-75). H a separable complex Hilbert space viewed as real; ℓ¹ = ℓ¹(ℤ; 𝕜).
(1) every bounded real-linear A : H → ℓ¹ is compact; (2) if P_N are the coordinate projections onto
increasing finite sets S_N exhausting ℤ, then ‖(1 − P_N) A‖ → 0; (3) uniformly over any norm-compact
family of such operators. P_N is specified by its coordinate action, not by the author's definition. -/

open Filter Topology

namespace QuantumNLS.R1D98Spec

def Spec : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (𝕜 : Type) [RCLike 𝕜]
    (S : ℕ → Finset ℤ), Monotone S → (∀ m : ℤ, ∃ N, m ∈ S N) →
    ∀ P : ℕ → (lp (fun _ : ℤ => 𝕜) 1 →L[ℝ] lp (fun _ : ℤ => 𝕜) 1),
      (∀ N x m, (P N x : ℤ → 𝕜) m = if m ∈ S N then (x : ℤ → 𝕜) m else 0) →
      letI : InnerProductSpace ℝ H := InnerProductSpace.complexToReal
      (∀ A : H →L[ℝ] lp (fun _ : ℤ => 𝕜) 1, IsCompactOperator A) ∧
      (∀ A : H →L[ℝ] lp (fun _ : ℤ => 𝕜) 1,
        Tendsto (fun N => ‖(ContinuousLinearMap.id ℝ _ - P N).comp A‖) atTop (𝓝 0)) ∧
      (∀ 𝒜 : Set (H →L[ℝ] lp (fun _ : ℤ => 𝕜) 1), IsCompact 𝒜 → ∀ ε > 0, ∃ N₀ : ℕ,
        ∀ N ≥ N₀, ∀ A ∈ 𝒜, ‖(ContinuousLinearMap.id ℝ _ - P N).comp A‖ ≤ ε)

theorem spec : Spec := by
  intro H _ _ _ _ 𝕜 _ S hS hexh P hP
  have hPeq : ∀ N, P N = HilbertL1Compact.restrictCLM (𝕜 := 𝕜) (S N) := by
    intro N
    refine ContinuousLinearMap.ext fun x => ?_
    apply Subtype.ext; funext m
    rw [hP N x m]
    rfl
  simp only [hPeq]
  exact HilbertL1CompactLiteral.hilbert_l1_compact_complex_literal (H := H) (𝕜 := 𝕜) S hS hexh

end QuantumNLS.R1D98Spec

open Lean in
#eval show CoreM Unit from do
  let ax ← Lean.collectAxioms ``QuantumNLS.R1D98Spec.spec
  IO.println s!"R1D98Spec.spec axioms: {ax}"
