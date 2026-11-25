import QuantumNLS.AllOrderEnergyAssemblyR57a
import QuantumNLS.AllOrderEnergyPacketsR57a

/-! Intermediate for thm:energy-allorder-energy at the printed predecessors. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Filter Topology
namespace QuantumNLS.AllOrderEnergyFinalR57a
open PhysicalTensor TensorCarrier PhysicalEnergy EnergyPreparationDef
open Def033HierarchyR24m BetheCoefficientTransform ContactOperator BethePhysicalTransfer
open AllOrderEnergyInputsR56a (flows)
open AllOrderEnergyInputsR57a AllOrderEnergyPredecessorsR57a
open AllOrderEnergyAssemblyR57a AllOrderEnergyPacketsR57a ActualModelTargetR53a
variable {L κ : ℝ} [Fact (0 < L)]

/-- The positive sectors of a DEF-031 preparation are the exact inputs of the
physical trace and form convergence theorem. -/
theorem energy_limit_of_prepared (hκ : 0 < κ)
    (HierarchyR7B122087Input : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ)
    (ActualModelRE679E41DInput : ActualModelRE679E41DInput (L := L) hκ HierarchyR7B122087Input)
    (u : Smooth L) (hu : ‖physical u‖ = 1)
    (ψ : ∀ N, HilbertTensorPower ℂ (L2T L) N)
    (hψ : EnergyPreparation κ (physical u) ψ)
    (R : Finset ℕ) (K : Set (ℕ → ℝ)) (hK : IsCompact K) (k : ℕ) :
    EnergyLimit hκ HierarchyR7B122087Input u
      (fun n => ⟨ψ (n+1), hψ.mem_sector (n+1)⟩) R K k := by
  let ψs (n : ℕ) : HN L (n+1) := ⟨ψ (n+1), hψ.mem_sector (n+1)⟩
  obtain ⟨x, hx, hs, hUpper⟩ := hψ.energy
  let xs (n : ℕ) : VSym L (n+1) := ⟨x (n+1), hs (n+1)⟩
  have hxs (n : ℕ) : valSym (xs n) = symmetricPosition L (n+1) (ψs n) :=
    Subtype.ext (hx (n+1))
  have hupp : limsup (fun n => ((hN κ (n+1) (xs n).val / (n+1 : ℕ) : ℝ) : EReal))
      atTop ≤ (I3 κ (physical u) : EReal) := by
    refine (EnergyPreparationDef.limsup_le_iff _ _).2 fun ε hε => ?_
    exact (tendsto_add_atTop_nat 1).eventually ((EnergyPreparationDef.limsup_le_iff _ _).1 hUpper ε hε)
  exact physical_energy_intermediate hκ HierarchyR7B122087Input ActualModelRE679E41DInput
    u hu ψs (fun n => hψ.normClose.1 (n+1)) xs hxs
    (hψ.normClose.2.comp (tendsto_add_atTop_nat 1)) hupp R K hK k

/-- The conditional physical theorem at every fixed positive marginal rank.
The conclusion also records the actual window application and the two
preparation classes in the source. -/
theorem energy_allorder_energy_intermediate (hκ : 0 < κ)
    (HierarchyR7B122087Input : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ)
    (WindowRE59628C9Input : WindowRE59628C9Input (L := L) hκ)
    (ActualModelRE679E41DInput : ActualModelRE679E41DInput (L := L) hκ HierarchyR7B122087Input)
    (WeightedR115CAA16Input : WeightedR115CAA16Input (L := L) hκ)
    (u : Smooth L) (hu : ‖physical u‖ = 1) (R : Finset ℕ)
    (K : Set (ℕ → ℝ)) (hK : IsCompact K) :
    (∀ (ψ : ∀ N, HilbertTensorPower ℂ (L2T L) N)
      (hψ : EnergyPreparation κ (physical u) ψ) (k : ℕ), 1 ≤ k →
      EnergyLimit hκ HierarchyR7B122087Input u
        (fun n => ⟨ψ (n+1), hψ.mem_sector (n+1)⟩) R K k) ∧
    EnergyPreparation κ (physical u) (fun N => htpow N (physical u)) ∧
    CommonEnergyPackets hκ u ∧
    (∀ T : ℕ → ℝ, (∀ r, 0 ≤ T r) →
      WindowRate (hamFlows (flows hκ HierarchyR7B122087Input) R) T {u}) := by
  refine ⟨fun ψ hψ k _ => energy_limit_of_prepared hκ HierarchyR7B122087Input
      ActualModelRE679E41DInput u hu ψ hψ R K hK k,
    AllOrderEnergyInputsR55a.exact_product_prepared κ u hu,
    common_packets_prepared hκ WeightedR115CAA16Input u hu, ?_⟩
  intro T hT
  let d := max 2 (R.sup id)
  have hR (r : ℕ) (hr : r ∈ R) : r ≤ d :=
    (Finset.le_sup (f := id) hr).trans (le_max_right _ _)
  exact (actual_window_rate hκ HierarchyR7B122087Input WindowRE59628C9Input d
    (le_max_left _ _) R hR T hT).1 u

end QuantumNLS.AllOrderEnergyFinalR57a
