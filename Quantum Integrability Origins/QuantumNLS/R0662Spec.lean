import QuantumNLS.InverseGaudinDecay

/-! integrator-authored trusted spec for R-0662E607 `adj:lem:inverse-decay` (quantitative/fixed_moments.tex:4).
N ≥ 2, c, L > 0, arbitrary real q; G = L Id + 𝓛_w, i.e. G_jj = L + Σ_{k≠j} w_jk and G_jk = −w_jk,
w_jk = 2c/(c² + (q_j − q_k)²) (the weighted-Laplacian convention of block_inverse.tex:13-14);
d = L + 2(N−1)/c, τ = 1 − L/d, B = (2c/d²)(1 + 4τ + τ²)/(1 − τ)⁴. Then 0 ≤ (G⁻¹)_jk ≤ (L⁻¹ + B)/(1 + (q_j − q_k)²).
G is written out here. -/

open Finset Matrix

namespace QuantumNLS.R0662Spec

noncomputable def G {N : ℕ} (L c : ℝ) (q : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i k =>
    if i = k then L + ∑ j ∈ univ.erase i, 2 * c / (c ^ 2 + (q i - q j) ^ 2)
    else -(2 * c / (c ^ 2 + (q i - q k) ^ 2))

def Spec : Prop :=
  ∀ (N : ℕ), 2 ≤ N → ∀ (L c : ℝ), 0 < L → 0 < c → ∀ q : Fin N → ℝ,
    let d := L + 2 * ((N : ℝ) - 1) / c
    let τ := 1 - L / d
    let B := 2 * c / d ^ 2 * (1 + 4 * τ + τ ^ 2) / (1 - τ) ^ 4
    ∀ j k : Fin N, 0 ≤ (G L c q)⁻¹ j k ∧ (G L c q)⁻¹ j k ≤ (L⁻¹ + B) / (1 + (q j - q k) ^ 2)

theorem spec : Spec := by
  intro N hN L c hL hc q d τ B j k
  exact QuantumNLS.InverseGaudinDecay.inverse_gaudin_decay hN hL hc q d τ B rfl rfl rfl j k

end QuantumNLS.R0662Spec

open Lean in
#eval show CoreM Unit from do
  let ax ← Lean.collectAxioms ``QuantumNLS.R0662Spec.spec
  IO.println s!"R0662Spec.spec axioms: {ax}"
