import QuantumNLS.F07StepsR6
/-! integrator-authored trusted spec for R-3C2D6BAB prop:finite-coupling-response (Terra r157 FULL ACCEPT): headline statement copied verbatim from F07StepsR6 (QuantumNLS.F07StepsR6). -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Set MeasureTheory
namespace QuantumNLS.R3C2DSpec
open QuantumNLS.F07StepsR6


set_option maxHeartbeats 8000000 in
theorem finite_coupling_response_spec {N : ℕ} (hN : 0 < N) {L K : ℝ}
    (hL : 0 < L) (hK : 0 < K) (b : Fin N → ℝ) :
    let q := BetheSmooth.root L b (K/N)
    let B := BetheRoots.gaudin L (K/N) q
    K * deriv (F07EnergyR6.intensiveEnergy L b) K =
      2 * F07EnergyR6.intensiveEnergy L b K -
        2 * L * (∫ x in Ioc (0 : ℝ) 1, step q x * step (B.inverse q) x) ∧
    0 ≤ K * deriv (F07EnergyR6.intensiveEnergy L b) K ∧
    K * deriv (F07EnergyR6.intensiveEnergy L b) K ≤ 2 * F07EnergyR6.intensiveEnergy L b K := by
  first
  | exact QuantumNLS.F07StepsR6.finite_coupling_response
  | (apply QuantumNLS.F07StepsR6.finite_coupling_response <;> assumption)

end QuantumNLS.R3C2DSpec
#print axioms QuantumNLS.R3C2DSpec.finite_coupling_response_spec
