import QuantumNLS.Def024CubicUnique
import QuantumNLS.Def024LowEquivariance
import QuantumNLS.Def024LowFlows

/-!
# DEF-024, stage D4 (commutation part): the order-2 flow commutes with the order-0 and order-1 flows

Source: `DEFINITIONS_LEDGER.md` DEF-024 (`chapters/definitions.tex:145-149`); the frozen
`HierarchyFlow.IsHamFlow` for `F = Re I_3 = hamiltonian L κ 2`.  Read-only inputs:
`Def024LowEquivariance.comm_low_of_unique` (the review, frozen; the conditional commutation theorem for
every order `r` under the predicate `UniqueHamFlow`), `Def024CubicUnique.unique_two` (own frozen
module f9feb273: the order-2 flow is unique on the smooth periodic class when `κ ≥ 0`),
`Def024LowFlows.phaseFlow` (order 0, `e^{−ia}u`) and `Def024LowFlows.transFlow` (order 1, `u(· − a)`).

Proved here (no assumption beyond `0 ≤ κ` and the frozen `IsHamFlow` of `Re I_3`):
* `cubic_comm_low`: for every Hamiltonian flow `Φ` of `Re I_3` with `κ ≥ 0`, every smooth periodic
  `u` and all real `s, a`, `Φ_s(e^{−ia}u) = e^{−ia}Φ_s u` and `Φ_s(u(· − a)) = (Φ_s u)(· − a)`.
-/

set_option autoImplicit false
noncomputable section

namespace QuantumNLS.Def024CubicLowComm2

open QuantumNLS.ClassicalCharges QuantumNLS.HierarchyFlow QuantumNLS.Def024LowEquivariance
  QuantumNLS.Def024LowFlows QuantumNLS.Def024CubicUnique

variable {L : ℝ} [Fact (0 < L)]

/-- **Commutation of the order-2 (cubic NLS) flow with the order-0 and order-1 flows** on smooth
periodic data, for `κ ≥ 0`: phase and translation commute with `Φ_s`. -/
theorem cubic_comm_low {κ : ℝ} (hκ : 0 ≤ κ) {Φ : ℝ → (ℝ → ℂ) → (ℝ → ℂ)}
    (hΦ : IsHamFlow L (hamiltonian L κ 2) Φ) {u : ℝ → ℂ} (hu : SmoothPeriodic L u) (s a : ℝ) :
    Φ s (phaseFlow a u) = phaseFlow a (Φ s u) ∧ Φ s (transFlow a u) = transFlow a (Φ s u) :=
  comm_low_of_unique κ 2 hΦ (unique_two hκ hΦ) hu s a

/-- Commutation with the order-0 flow alone. -/
theorem cubic_comm_phase {κ : ℝ} (hκ : 0 ≤ κ) {Φ : ℝ → (ℝ → ℂ) → (ℝ → ℂ)}
    (hΦ : IsHamFlow L (hamiltonian L κ 2) Φ) {u : ℝ → ℂ} (hu : SmoothPeriodic L u) (s a : ℝ) :
    Φ s (phaseFlow a u) = phaseFlow a (Φ s u) :=
  (cubic_comm_low hκ hΦ hu s a).1

/-- Commutation with the order-1 flow alone. -/
theorem cubic_comm_trans {κ : ℝ} (hκ : 0 ≤ κ) {Φ : ℝ → (ℝ → ℂ) → (ℝ → ℂ)}
    (hΦ : IsHamFlow L (hamiltonian L κ 2) Φ) {u : ℝ → ℂ} (hu : SmoothPeriodic L u) (s a : ℝ) :
    Φ s (transFlow a u) = transFlow a (Φ s u) :=
  (cubic_comm_low hκ hΦ hu s a).2

#print axioms cubic_comm_low
#print axioms cubic_comm_phase
#print axioms cubic_comm_trans

end QuantumNLS.Def024CubicLowComm2
