import QuantumNLS.SmallClusterBound

/-! integrator-authored trusted spec for R-CFCD5A9D `QG:lem:B3-small-cluster`
(core/QUANTUM_GAUGE_COMPONENTS.tex:25-38). x_1, …, x_k distinct reals, c, L > 0, and for every j with
x_j > 0: L x_j ≤ 2 Σ_{ℓ≠j} arctan(c/(x_j − x_ℓ)). Then max_j (x_j)_+ ≤ 3√(ck/L), with (x)_+ = max{x,0};
stated for every j (equivalent to the max form; vacuous for k = 0, includes k = 1). Distinctness makes every
arctan argument a genuine quotient. -/

namespace QuantumNLS.RCFCDSpec

def Spec : Prop :=
  ∀ (k : ℕ) (x : Fin k → ℝ), Function.Injective x → ∀ (c L : ℝ), 0 < c → 0 < L →
    (∀ j, 0 < x j → L * x j ≤ 2 * ∑ l ∈ Finset.univ.erase j, Real.arctan (c / (x j - x l))) →
    ∀ j, max (x j) 0 ≤ 3 * Real.sqrt (c * k / L)

theorem spec : Spec := fun _k _x hx _c _L hc hL hf =>
  QuantumNLS.SmallClusterBound.small_cluster hx hc hL hf

end QuantumNLS.RCFCDSpec

open Lean in
#eval show CoreM Unit from do
  let ax ← Lean.collectAxioms ``QuantumNLS.RCFCDSpec.spec
  IO.println s!"RCFCDSpec.spec axioms: {ax}"
