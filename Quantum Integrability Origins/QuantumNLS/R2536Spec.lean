import QuantumNLS.OrderedResponse

/-! integrator-authored trusted spec for R-2536C7A6 `CC:F02:ordered-response` (root_response/F02.tex:78).
B is the CC:F02:matrix: B_ii = L + Σ_{j≠i} w_ij, B_ik = −w_ik (k ≠ i), with w_ij = 2c/(c² + (q_i − q_j)²).
For L, c > 0, N > 1 and strictly ordered q: B is invertible, and the vector f = B⁻¹ q, i.e. the
unique solution of B f = q, is strictly increasing in its index. B is written out here. -/

open Finset Matrix

namespace QuantumNLS.R2536Spec

noncomputable def B {N : ℕ} (L c : ℝ) (q : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i k =>
    if i = k then L + ∑ j ∈ univ.erase i, 2 * c / (c ^ 2 + (q i - q j) ^ 2)
    else -(2 * c / (c ^ 2 + (q i - q k) ^ 2))

def Spec : Prop :=
  ∀ (N : ℕ) (L c : ℝ), 0 < L → 0 < c → 1 < N → ∀ q : Fin N → ℝ, StrictMono q →
    IsUnit (B L c q).det ∧ (∃! f : Fin N → ℝ, B L c q *ᵥ f = q) ∧
    ∀ f : Fin N → ℝ, B L c q *ᵥ f = q → StrictMono f

theorem spec : Spec := by
  intro N L c hL hc hN q hq
  have hB : B L c q = QuantumNLS.OrderedResponse.Bmat L c q := rfl
  have hinj := QuantumNLS.OrderedResponse.Bmat_injective hL hc q
  have hsol := QuantumNLS.OrderedResponse.Bmat_respF hL hc q
  have huniq : ∀ f, B L c q *ᵥ f = q → f = QuantumNLS.OrderedResponse.respF L c q := by
    intro f hf; rw [hB] at hf; exact hinj (hf.trans hsol.symm)
  refine ⟨hB ▸ QuantumNLS.OrderedResponse.Bmat_isUnit_det hL hc q,
    ⟨_, hB ▸ hsol, fun f hf => huniq f hf⟩, fun f hf => ?_⟩
  rw [huniq f hf]
  exact QuantumNLS.OrderedResponse.ordered_response hL hc hN q hq

end QuantumNLS.R2536Spec

open Lean in
#eval show CoreM Unit from do
  let ax ← Lean.collectAxioms ``QuantumNLS.R2536Spec.spec
  IO.println s!"R2536Spec.spec axioms: {ax}"
