import QuantumNLS.GroundRootBound

/-! integrator-authored trusted spec for R-39906D9E `CC:F01:ground` (root_response/F01.tex:101-106).
For M ≥ 1, L > 0, c > 0: if s_1 < ⋯ < s_M solve the Bose equations (CC:F01:bose)
L s_i − 2 Σ_{j≠i} arctan(c/(s_i − s_j)) = 2π n_i with all labels n_i = 0, then s_i = −s_{M+1−i} and
max_i |s_i| ≤ 2 √(cM/L). Zero-based indices; M+1−i ↦ Fin.rev i. The system is written out here. -/

namespace QuantumNLS.R3990Spec

def Spec : Prop :=
  ∀ (M : ℕ), 1 ≤ M → ∀ (L c : ℝ), 0 < L → 0 < c → ∀ s : Fin M → ℝ, StrictMono s →
    (∀ i : Fin M, L * s i - 2 * ∑ j ∈ Finset.univ.erase i, Real.arctan (c / (s i - s j)) = 0) →
    (∀ i, s i = -s (Fin.rev i)) ∧ ∀ i, |s i| ≤ 2 * Real.sqrt (c * (M : ℝ) / L)

theorem spec : Spec := by
  intro M hM L c hL hc s hs hsys
  refine QuantumNLS.GroundRootBound.ground_root_bound hM hL hc (fun _ => 0) (fun _ => rfl) s hs ?_
  intro i
  simp only [QuantumNLS.GroundRootBound.boseLHS, Int.cast_zero, mul_zero]
  exact hsys i

end QuantumNLS.R3990Spec

open Lean in
#eval show CoreM Unit from do
  let ax ← Lean.collectAxioms ``QuantumNLS.R3990Spec.spec
  IO.println s!"R3990Spec.spec axioms: {ax}"
