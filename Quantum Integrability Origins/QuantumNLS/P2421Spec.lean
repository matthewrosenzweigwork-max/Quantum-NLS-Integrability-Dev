import QuantumNLS.Prop021FinalR135
import QuantumNLS.Prop024FinalR135
/-! integrator trusted spec for PROP-024 and PROP-021 (final R135 headlines plus literal Iff.rfl pins of the module-defined statement Props). -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option Elab.async false
set_option synthInstance.maxHeartbeats 200000
open scoped InnerProductSpace
universe uH
namespace QuantumNLS.P2421Spec
open QuantumNLS.Prop024FinalR135
open TensorCarrier PhysicalTensor BetheCoefficientTransform
open Prop022GTensor Prop022GClassical Prop022GLinear Prop022GHilbert Prop022AIsoTensor
open Prop022BClass1 Prop022BClass2 Prop022BClass3 Prop022BExist Prop022BFock3 Prop022AFock
open Prop022CQuad Prop022CWeyl Ext006PhysicalNormBridge.PairTensor
open Prop021ManyBodyTransportR132 Prop021MomentsR132 Prop024WickTransportR133 Prop024FinalH1
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem pin_Represents (a : SymSector ℂ H 1 →L[ℂ] SymSector ℂ H 1) (b : SymSector ℂ H 2)
    (a₀ b₀ : H →L[ℝ] H) :
    QuantumNLS.Prop024FinalR135.Represents a b a₀ b₀ ↔
  (∀ x y, ⟪powerH 1 x, a (powerH 1 y)⟫_ℂ = ⟪x, a₀ y⟫_ℂ) ∧
  (∀ x y, ⟪x, b₀ y⟫_ℂ = ⟪htmul y x, twoIso (E := H) (b : HilbertTensorPower ℂ H 2)⟫_ℂ) := Iff.rfl

theorem pin_RemainderAt (K : Kernels H) (M A : ℝ) (u : H)
    (a : SymSector ℂ H 1 →L[ℂ] SymSector ℂ H 1) (b : SymSector ℂ H 2) :
    QuantumNLS.Prop024FinalR135.RemainderAt K M A u a b ↔
  ∀ (N : ℕ) (Q : ℝ), 1 ≤ Q → 256 * Real.exp 1 * A * Q ≤ N →
  ∀ (x : FockSpace H), NumberMoments Q x →
    QRel a b x (∑' m : ℕ, degree N (m+1) 2 (K m) u x) ∧
    ∃ W : FockSpace H ≃ₗᵢ[ℂ] FockSpace H, IsWeylOp ((Real.sqrt N : ℂ) • u) W ∧
      ∀ W' : FockSpace H ≃ₗᵢ[ℂ] FockSpace H, IsWeylOp ((Real.sqrt N : ℂ) • u) W' →
      ∃ (hd : HamiltonianDomain K N (W' x)) (R : FockSpace H),
        W'.symm (hamiltonian K N (W' x) hd) =
          ((N : ℝ) * symbolH K u : ℂ) • x +
            (∑' m : ℕ, degree N (m+1) 1 (K m) u x) + QPrint a b x + R ∧
        ‖R‖ ≤ printedConstant A * M * (N : ℝ) ^ (-(1/2 : ℝ)) * Q ^ (3/2 : ℝ) := Iff.rfl

theorem pin_PrintedRemainder  :
    QuantumNLS.Prop024FinalR135.PrintedRemainder.{uH} ↔
  ∀ (A : ℝ) (hA : 0 < A),
  ∀ (H : Type uH) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H],
  ∀ (K : Kernels H) (M : ℝ) (hM : 1 ≤ M) (hK : KBound K M A) (hs : KSelfAdj K)
    (u : H) (hu : ‖u‖ = 1),
  letI : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  ∃ (a : SymSector ℂ H 1 →L[ℂ] SymSector ℂ H 1) (b : SymSector ℂ H 2),
    (∀ J : H →ₗᵢ[ℂ] L2T 1, Represents a b
      (aJ J K M A hA.le hK hs u hu 0) (bJ J K M A hA.le hK hs u hu 0)) ∧
    (∀ U : H ≃ₗᵢ[ℂ] L2T 1, Represents a b
      (aH U K M A hA.le hK hs u hu 0) (bH U K M A hA.le hK hs u hu 0)) ∧
    RemainderAt K M A u a b := Iff.rfl

theorem prop024_spec : QuantumNLS.Prop024FinalR135.PrintedRemainder.{uH} := QuantumNLS.Prop024FinalR135.prop024
theorem prop021_final_spec : QuantumNLS.Prop021FinalR135.PrintedConclusion.{uH} := QuantumNLS.Prop021FinalR135.prop021_final
theorem pin_PrintedConclusion : QuantumNLS.Prop021FinalR135.PrintedConclusion.{uH} ↔ (letI : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩; QuantumNLS.Prop021FinalR135.Conclusion.{uH} 1) := Iff.rfl
end QuantumNLS.P2421Spec
namespace QuantumNLS.P2421SpecC
open QuantumNLS.Prop021FinalR135
open TensorCarrier PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors
open Prop022GTensor Prop022GClassical Prop022GLinear Prop022GHilbert Prop022AIsoTensor
open Prop022BClass1 Prop022BClass2 Prop022BExist Prop022BFock1 Prop022BFock2 Prop022BFock3
open Prop022AFock Prop022CWeyl Prop022PositiveDataR126 Prop022OVacuum
open Prop021ManyBodyTransportR132 Prop021MarginalTransportR132 Prop021MomentsR132
open Prop021StatementR132 Prop021UnitaryR132 Prop024FinalR135
open Prop024FinalH1 (printedConstant printedConstant_nonneg)
theorem pin_Conclusion (L : ℝ) [Fact (0 < L)] :
    QuantumNLS.Prop021FinalR135.Conclusion.{uH} L ↔
  ∀ (A : ℝ) (hA : 0 < A), ∃ cA : ℝ, ∀ T : ℝ, 0 < T → ∃ CAT : ℝ,
  ∀ (H : Type uH) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H],
    Nonempty (H →ₗᵢ[ℂ] L2T L) ∧
    ∀ J : H →ₗᵢ[ℂ] L2T L, Prop021GeneralR134.AtConstants J A hA cA T CAT ∧ LinearizationAt J A hA := Iff.rfl
end QuantumNLS.P2421SpecC
#print axioms QuantumNLS.P2421Spec.prop024_spec
#print axioms QuantumNLS.P2421Spec.prop021_final_spec
