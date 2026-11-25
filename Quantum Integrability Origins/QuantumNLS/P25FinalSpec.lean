import QuantumNLS.Prop025FinalR01
/-! integrator trusted spec for PROP-025 (final binding, no named inputs). -/
set_option autoImplicit false
set_option maxHeartbeats 64000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace QuantumNLS.P25FinalSpec
open QuantumNLS.Prop025ProvenanceR59a
open scoped Topology ENNReal
open Filter
open Def033HierarchyR24m (Smooth physical)
open ActualModelTargetR53a (HigherFlows higher target)
open ActualModelCorollaryR53a (EstimateWithZeta boxError preparationError)
open Prop025OFinal (zeta zeta_tendsto zeta_empty main_of_total)
open Prop025OTarget (enum)
open Prop025OParams (alpha)
open PROP018Probability (cut_bounds)
open Prop017Quantum (eta0)
open Prop025PacketR59a (contourErrors core_at_packet)
variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}
theorem prop025_final_spec (hκ : 0 < κ) : QuantumNLS.Prop025ProvenanceR59a.PROP025WithPacket (L := L) hκ :=
  QuantumNLS.Prop025FinalR01.prop025_final hκ
theorem prop025_R56a_spec (hκ : 0 < κ) : QuantumNLS.ActualModelCorollaryR56a.PROP025Input (L := L) hκ :=
  QuantumNLS.Prop025FinalR01.prop025_final_R56a hκ
theorem pin_PROP025WithPacket (hκ : 0 < κ) :
    QuantumNLS.Prop025ProvenanceR59a.PROP025WithPacket (L := L) hκ ↔
  ∀ (u : Smooth L) (hu : ‖physical u‖ = 1) (M : Def044BindingR26m.MixedInterface hκ u hu)
    (I : Finset ℤ),
    let ζ := fixedZeta hκ u hu I
    Tendsto ζ atTop (𝓝 0) ∧ (I = ∅ → ∀ N, ζ N = 0) ∧
      ∀ (R : Finset ℕ) (k : ℕ) (Θ : ℤ → ℝ) (T : ℕ → ℝ),
        (∀ n ∈ I, 0 ≤ Θ n) → (∀ r ∈ R, 0 ≤ T r) →
        ∃ A : ℝ, 0 ≤ A ∧ EstimateWithZeta hκ M.chart.chart (higher M.dynamics.hierarchy)
          u I R k Θ T A ζ := Iff.rfl
end QuantumNLS.P25FinalSpec
#print axioms QuantumNLS.P25FinalSpec.prop025_final_spec
#print axioms QuantumNLS.P25FinalSpec.prop025_R56a_spec
