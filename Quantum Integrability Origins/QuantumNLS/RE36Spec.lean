import QuantumNLS.CubicGaudinIdentity

/-! integrator-authored trusted spec for R-E36CF4CB `adj:lem:cubic-gaudin-identity`
(quantitative/fourth_moments.tex:10). N ≥ 1, c, L > 0, real q; w_jk = 2c/(c² + (q_j − q_k)²),
G = L Id + 𝓛_w ((G f)_j = L f_j + Σ_{k≠j} w_jk (f_j − f_k)), P = Σ q_j, d_j = Σ_{k≠j} w_jk,
b_j = Σ_{k≠j} w_jk (q_j − q_k). Clauses: the exact identity for G q³; |b_j| ≤ N − 1, 0 ≤ d_j ≤ 2(N−1)/c;
and the response-remainder bound for v = G⁻¹δ. All objects written out here. -/

open Finset Matrix

namespace QuantumNLS.RE36Spec

noncomputable def w {N : ℕ} (c : ℝ) (q : Fin N → ℝ) (j k : Fin N) : ℝ := 2 * c / (c ^ 2 + (q j - q k) ^ 2)

noncomputable def G {N : ℕ} (L c : ℝ) (q : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i k => if i = k then L + ∑ j ∈ univ.erase i, w c q i j else -w c q i k

def Spec : Prop :=
  ∀ (N : ℕ) (L c : ℝ), 0 < L → 0 < c → ∀ q : Fin N → ℝ,
    let d : Fin N → ℝ := fun j => ∑ k ∈ univ.erase j, w c q j k
    let b : Fin N → ℝ := fun j => ∑ k ∈ univ.erase j, w c q j k * (q j - q k)
    let P : ℝ := ∑ j, q j
    (∀ j, (G L c q *ᵥ fun i => q i ^ 3) j =
      L * q j ^ 3 + 3 * q j ^ 2 * b j + (-4 * c * (N : ℝ) + 6 * c) * q j
        + 3 * c ^ 2 * q j * d j - 2 * c * P - c ^ 2 * b j) ∧
    (∀ j, |b j| ≤ (N : ℝ) - 1 ∧ 0 ≤ d j ∧ d j ≤ 2 * ((N : ℝ) - 1) / c) ∧
    (1 ≤ N → ∀ (δ v : Fin N → ℝ) (Q W : ℝ), v = (G L c q)⁻¹ *ᵥ δ →
      (∀ j, δ j ≠ 0 → |q j| ≤ Q) → ∑ j, (1 + q j ^ 2) * |v j| ≤ W →
      |∑ j, q j ^ 3 * v j - 2 * c / L * (∑ j, v j) * P|
        ≤ 1 / L * (Q ^ 3 * ∑ j, |δ j|
          + (3 * ((N : ℝ) - 1) + |4 * c * (N : ℝ) - 6 * c| + 6 * c * ((N : ℝ) - 1)
              + c ^ 2 * ((N : ℝ) - 1)) * W))

theorem spec : Spec := by
  intro N L c hL hc q d b P
  have hG : G L c q = QuantumNLS.OrderedResponse.Bmat L c q := rfl
  refine ⟨fun j => ?_, fun j => QuantumNLS.CubicGaudinIdentity.cubic_coefficients hc q j,
    fun hN δ v Q W hv hs hW => ?_⟩
  · have h := QuantumNLS.CubicGaudinIdentity.cubic_gaudin_identity hL hc q j
    rw [QuantumNLS.CubicGaudinIdentity.Gop_eq_mulVec] at h
    rw [hG]; exact h
  · rw [hG] at hv
    exact QuantumNLS.CubicGaudinIdentity.cubic_response_remainder hN hL hc q δ v Q W hv hs hW

end QuantumNLS.RE36Spec

open Lean in
#eval show CoreM Unit from do
  let ax ← Lean.collectAxioms ``QuantumNLS.RE36Spec.spec
  IO.println s!"RE36Spec.spec axioms: {ax}"
