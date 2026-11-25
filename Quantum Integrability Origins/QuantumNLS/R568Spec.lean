import QuantumNLS.AllOrderEnergyFinalR60a
/-! integrator-authored trusted spec for R-568BCDF8 thm:energy-allorder-energy (final, no named inputs): headline statement(s) copied verbatim from AllOrderEnergyFinalR60a (QuantumNLS.AllOrderEnergyFinalR60a). -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
namespace QuantumNLS.R568Spec
open QuantumNLS.AllOrderEnergyFinalR60a
open PhysicalTensor (L2T)
open TensorCarrier (HilbertTensorPower htpow)
open EnergyPreparationDef (EnergyPreparation)
open Def033HierarchyR24m (Smooth physical)
open ActualModelTargetR53a (hamFlows)
open AllOrderEnergyInputsR56a (flows)
open AllOrderEnergyPredecessorsR57a
open AllOrderEnergyAssemblyR57a (EnergyLimit)
open AllOrderEnergyPacketsR57a (CommonEnergyPackets)
open RB7BindFinal (hierarchyInputR25m_unconditional)
variable {L κ : ℝ} [Fact (0 < L)]

set_option maxHeartbeats 8000000 in
theorem energy_allorder_energy_spec (hκ : 0 < κ) (u : Smooth L) (hu : ‖physical u‖ = 1)
    (R : Finset ℕ) (K : Set (ℕ → ℝ)) (hK : IsCompact K) :
    let HH := hierarchyInputR25m_unconditional (L := L) hκ
    (∀ (ψ : ∀ N, HilbertTensorPower ℂ (L2T L) N)
      (hψ : EnergyPreparation κ (physical u) ψ) (k : ℕ), 1 ≤ k →
      EnergyLimit hκ HH u (fun n => ⟨ψ (n+1), hψ.mem_sector (n+1)⟩) R K k) ∧
    EnergyPreparation κ (physical u) (fun N => htpow N (physical u)) ∧
    CommonEnergyPackets hκ u ∧
    (∀ T : ℕ → ℝ, (∀ r, 0 ≤ T r) →
      WindowRate (hamFlows (flows hκ HH) R) T {u}) := by
  first
  | exact QuantumNLS.AllOrderEnergyFinalR60a.energy_allorder_energy
  | (apply QuantumNLS.AllOrderEnergyFinalR60a.energy_allorder_energy <;> assumption)

end QuantumNLS.R568Spec
#print axioms QuantumNLS.R568Spec.energy_allorder_energy_spec
