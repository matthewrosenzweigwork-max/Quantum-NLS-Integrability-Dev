import QuantumNLS.Ext005PhysicalInstanceR121
/-! integrator-authored trusted spec for EXT-005 FIN-CORE-LNS-01 fixed-j physical instance (review record r61): headline statement(s) copied verbatim from Ext005PhysicalInstanceR121 (QuantumNLS.Ext005PhysicalInstanceR121). -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace Topology ComplexConjugate ContDiff
open ContinuousLinearMap Set Filter MeasureTheory
namespace QuantumNLS.E005Spec
open QuantumNLS.Ext005PhysicalInstanceR121
open BetheCoefficientTransform Ext025B3PhysicalSectors Ext005Moments Ext005MomentEnergyR108
open Ext005MomentDomainR33b Ext005OperatorFormR113 Ext005PhysicalSourceR121
open Ext005SourceIntervalR32b Ext005ContractR39b Ext005ReversalR39b
open Ext005FiniteContractR39b Ext005PatchingR32b Ext005SourceBoundsR36b
open Prop022FactorialCoefficientsR115
variable {L : ℝ} [Fact (0 < L)]
variable (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ) (hM : 0 ≤ M) (hA : 0 ≤ A)
  (hB : FactorialBound B M A) (hs : ∀ m, (B m).adjoint = B m)
  (u₀ : Prop001.Sphere (PhysicalTensor.L2T L))

set_option maxHeartbeats 8000000 in
theorem EXT005_physical_instance_R121_spec (j : ℕ) (hj : 1 ≤ j)
    (l r : ℝ) (hlr : l ≤ r) (s : ℝ) (hs₀ : s ∈ Icc l r)
    (x : Fock L) (hx : x ∈ momentDomain (L := L) j) :
    ∃ v : ℝ → FormDomain (momentPositive (L := L) j),
      Ext005OperatorFormR113.inclusion (momentPositive j) (v s) = x ∧
      (∀ t ∈ Icc l r, Ext005OperatorFormR113.inclusion (momentPositive j) (v t) ∈ momentDomain (L := L) j) ∧
      (∀ t, momentRoot j ⟨Ext005OperatorFormR113.inclusion (momentPositive j) (v t), inclusion_mem_root j (v t)⟩ = completedRoot j (v t)) ∧
      (∃ E : ℝ, 0 ≤ E ∧ ∀ t ∈ Icc l r,
        energy j (Ext005OperatorFormR113.inclusion (momentPositive j) (v t)) ≤ E) ∧
      D3On (momentPositive j) l r (physicalSource B M A hM hA hB hs u₀ j hj l r) (fun t => Ext005OperatorFormR113.inclusion (momentPositive j) (v t)) ∧
      (∀ t ∈ Icc l r, ‖Ext005OperatorFormR113.inclusion (momentPositive j) (v t)‖ = ‖x‖) ∧
      ∀ y : ℝ → Fock L, D3On (momentPositive j) l r (physicalSource B M A hM hA hB hs u₀ j hj l r) y → y s = x →
        ∀ t ∈ Icc l r, y t = Ext005OperatorFormR113.inclusion (momentPositive j) (v t) := by
  exact QuantumNLS.Ext005PhysicalInstanceR121.EXT005_physical_instance_R121 B M A hM hA hB hs u₀ j hj l r hlr s hs₀ x hx

end QuantumNLS.E005Spec
#print axioms QuantumNLS.E005Spec.EXT005_physical_instance_R121_spec
