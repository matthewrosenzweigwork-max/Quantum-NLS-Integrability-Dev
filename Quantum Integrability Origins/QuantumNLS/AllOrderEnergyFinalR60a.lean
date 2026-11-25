import QuantumNLS.ActualModelCorollaryR60a
import QuantumNLS.WindowODEBridgeR01
import QuantumNLS.Bind7B115CAA16H02

/-! Final binding of R-568BCDF8, thm:energy-allorder-energy. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section

namespace QuantumNLS.AllOrderEnergyFinalR60a

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

/-- The accepted printed weighted audit supplies the R57a conditional interface. -/
theorem weighted_bound (hκ : 0 < κ) : WeightedR115CAA16Input (L := L) hκ :=
  fun _ _ _ hf hu => Bind7B115CAA16H02.audit_weighted_printed hκ hf hu

/-- Use the accepted window theorem at higher orders and the reviewed all-orders
extension for families containing a low order. Both use the same physical ODE. -/
theorem window_rate (hκ : 0 < κ) (u : Smooth L) (R : Finset ℕ)
    (T : ℕ → ℝ) (hT : ∀ r, 0 ≤ T r) :
    WindowRate (hamFlows (flows hκ (hierarchyInputR25m_unconditional hκ)) R) T {u} := by
  let HH := hierarchyInputR25m_unconditional (L := L) hκ
  classical
  by_cases hR : ∀ r ∈ R, 2 ≤ r
  · exact WindowODEBridgeR01.windowRate_of_windowInput hκ HH
      (Bind7BE59628C9H01.window_bound hκ) R hR T hT {u} isCompact_singleton
  · let d := max 2 (R.sup id)
    have hRd (r : ℕ) (hr : r ∈ R) : r ≤ d :=
      (Finset.le_sup (f := id) hr).trans (le_max_right _ _)
    exact (actual_window_rate hκ HH (WindowODEBridgeR01.windowInput_r57a hκ HH)
      d (le_max_left _ _) R hRd T hT).1 u

/-- Energy trace convergence and convergence for all bounded physical forms,
with the two preparation classes and the physical window application. -/
theorem energy_allorder_energy (hκ : 0 < κ) (u : Smooth L) (hu : ‖physical u‖ = 1)
    (R : Finset ℕ) (K : Set (ℕ → ℝ)) (hK : IsCompact K) :
    let HH := hierarchyInputR25m_unconditional (L := L) hκ
    (∀ (ψ : ∀ N, HilbertTensorPower ℂ (L2T L) N)
      (hψ : EnergyPreparation κ (physical u) ψ) (k : ℕ), 1 ≤ k →
      EnergyLimit hκ HH u (fun n => ⟨ψ (n+1), hψ.mem_sector (n+1)⟩) R K k) ∧
    EnergyPreparation κ (physical u) (fun N => htpow N (physical u)) ∧
    CommonEnergyPackets hκ u ∧
    (∀ T : ℕ → ℝ, (∀ r, 0 ≤ T r) →
      WindowRate (hamFlows (flows hκ HH) R) T {u}) := by
  obtain ⟨hlimit, hproduct, hpackets, _⟩ :=
    WindowODEBridgeR01.energy_allorder_energy_window_bound hκ
      (hierarchyInputR25m_unconditional hκ) (ActualModelCorollaryR60a.cor_MP_actual_model hκ)
      (weighted_bound hκ) u hu R K hK
  exact ⟨hlimit, hproduct, hpackets, window_rate hκ u R⟩

end QuantumNLS.AllOrderEnergyFinalR60a
