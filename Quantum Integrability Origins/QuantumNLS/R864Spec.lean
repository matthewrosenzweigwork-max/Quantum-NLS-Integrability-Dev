import QuantumNLS.F02Round6
/-! integrator-authored trusted spec for R-864F39DE CC:F02:derivative (Terra r157 FULL ACCEPT): headline statement copied verbatim from F02Round6 (QuantumNLS.F02Round6Derivative). -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
namespace QuantumNLS.R864Spec
open QuantumNLS.F02Round6Derivative
open BetheAdmission BetheRoots BetheSmooth Ext025A6 F02Square F02Round6

set_option maxHeartbeats 8000000 in
theorem coupling_derivative_spec {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    {ν : Fin N → ℝ} (hν : Monotone ν) :
    let q := root L (realLabelForce ν) c
    let z := c • deriv (root L (realLabelForce ν)) c
    StrictMono q ∧
    (∀ i, L * q i + 2 * ∑ j ∈ univ.erase i,
      Real.arctan ((q i - q j) / c) =
        2 * Real.pi * ν i + Real.pi * (2 * (i : ℝ) + 1 - N)) ∧
    (∀ p : Fin N → ℝ, (∀ i, L * p i + 2 * ∑ j ∈ univ.erase i,
      Real.arctan ((p i - p j) / c) =
        2 * Real.pi * ν i + Real.pi * (2 * (i : ℝ) + 1 - N)) → p = q) ∧
    AnalyticAt ℝ (fun p : ℝ × (Fin N → ℝ) =>
      root L (realLabelForce p.2) p.1) (c, ν) ∧
    (∀ d : ℝ, 0 < d → ∀ μ : Fin N → ℝ, StrictMono (realLabelForce μ) →
      StrictMono (root L (realLabelForce μ) d)) ∧
    gaudin L c q z = gaudin L c q q - L • q ∧
    (gaudin L c q).inverse q = L⁻¹ • (q - z) ∧
    L * ∑ i, z i ^ 2 +
      ∑ i, ∑ j ∈ univ.filter (fun j => i < j),
        edgeWeight c q i j * (z i - z j - (q i - q j) / 2)^2 =
      (1 / 4 : ℝ) * ∑ i, ∑ j ∈ univ.filter (fun j => i < j),
        edgeWeight c q i j * (q i - q j)^2 ∧
    ∑ i, z i ^ 2 ≤ c * (N : ℝ) * ((N : ℝ) - 1) / (4 * L) := by
  first
  | exact QuantumNLS.F02Round6Derivative.coupling_derivative
  | (apply QuantumNLS.F02Round6Derivative.coupling_derivative <;> assumption)

end QuantumNLS.R864Spec
#print axioms QuantumNLS.R864Spec.coupling_derivative_spec
