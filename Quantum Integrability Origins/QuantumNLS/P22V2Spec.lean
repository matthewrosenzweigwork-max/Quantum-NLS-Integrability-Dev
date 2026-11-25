import QuantumNLS.Prop022DMain
/-! integrator-authored trusted spec for PROP-022 intrinsic (Prop022DMain): headline statement(s) copied verbatim from Prop022DMain (QuantumNLS.Prop022DMain). -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false
noncomputable section
open scoped InnerProductSpace Topology NNReal ENNReal
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
attribute [local instance 2000] InnerProductSpace.complexToReal
namespace QuantumNLS.P22V2Spec
open QuantumNLS.Prop022DMain
open QuantumNLS.TensorCarrier QuantumNLS.Prop022GTensor QuantumNLS.Prop022CCanon QuantumNLS.Prop022CQuad
open QuantumNLS.Prop022CIntrinsic QuantumNLS.Prop022AFock QuantumNLS.Prop022DQuasi
open QuantumNLS.Prop022DNumber
open PhysicalTensor BetheCoefficientTransform
open Prop022GClassical Prop022GLinear Prop022BClass1 Prop022BClass2 Prop022BFock2 Prop022BFock3
open Prop022GAntiHS Ext006PhysicalNormBridge.PairTensor
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

set_option maxHeartbeats 8000000 in
theorem PROP022_general_intrinsic_v2_spec [TopologicalSpace.SeparableSpace H] (L : ℝ) [Fact (0 < L)]
    (K : Kernels H) (M A : ℝ) (hM : 1 ≤ M) (hA : 0 < A) (hK : KBound K M A) (hs : KSelfAdj K)
    (u₀ : H) (hu₀ : ‖u₀‖ = 1) (T P : ℝ) (hP : 1 ≤ P) {ι : Type*} (e : HilbertBasis ι ℂ H) :
    type_of% (Prop022CMain.PROP022_general_intrinsic L K M A hM hA hK hs u₀ hu₀ T P hP e) ∧
    (¬ FiniteDimensional ℂ H → ∀ U : H ≃ₗᵢ[ℂ] L2T L,
      (∀ (t : ℝ) (x y : H), ⟪powerH 1 x, aSym U K M A hA.le hK hs u₀ hu₀ t (powerH 1 y)⟫_ℂ =
        ⟪x, aH U K M A hA.le hK hs u₀ hu₀ t y⟫_ℂ) ∧
      (∀ (t : ℝ) (x y : H), ⟪x, bH U K M A hA.le hK hs u₀ hu₀ t y⟫_ℂ =
        ⟪htmul y x, twoIso (E := H) (bSym U K M A hA.le hK hs u₀ hu₀ t : HilbertTensorPower ℂ H 2)⟫_ℂ) ∧
      (let hM0 : 0 ≤ M := by linarith
       QFAut (VH U K M A hA.le hK hs u₀ hu₀ hM0) (SH U K M A hA.le hK hs u₀ hu₀) (vacH U))) ∧
    (FiniteDimensional ℂ H → ∀ J : H →ₗᵢ[ℂ] L2T L,
      (∀ (t : ℝ) (x y : H), ⟪powerH 1 x, aSymJ J K M A hA hK hs u₀ hu₀ t (powerH 1 y)⟫_ℂ =
        ⟪x, aJ J K M A hA.le hK hs u₀ hu₀ t y⟫_ℂ) ∧
      (∀ (t : ℝ) (x y : H), ⟪x, bJ J K M A hA.le hK hs u₀ hu₀ t y⟫_ℂ =
        ⟪htmul y x, twoIso (E := H) (bSymJ J K M A hA hK hs u₀ hu₀ t : HilbertTensorPower ℂ H 2)⟫_ℂ) ∧
      QFAut (VJ J K M A hM hA hK hs u₀ hu₀) (SJ J K M A hA.le hK hs u₀ hu₀) (vacJ J)) ∧
    ((∀ n : ℕ, numberBlockE (ContinuousLinearMap.id ℂ (SymSector ℂ H 1)) n =
        (n : ℂ) • ContinuousLinearMap.id ℂ (SymSector ℂ H n)) ∧
      (∀ x : FockSpace H, dGammaSeq (ContinuousLinearMap.id ℂ (SymSector ℂ H 1)) x = numSeq x) ∧
      (∀ y z : FockSpace H, QRel (ContinuousLinearMap.id ℂ (SymSector ℂ H 1)) (0 : SymSector ℂ H 2) y z ↔
        ∀ n : ℕ, z n = numSeq y n) ∧
      (∀ x : FockSpace H, numExpH x = ∑' n : ℕ, ENNReal.ofReal
        ((⟪x n, dGammaSeq (ContinuousLinearMap.id ℂ (SymSector ℂ H 1)) x n⟫_ℂ).re))) := by
  first
  | exact QuantumNLS.Prop022DMain.PROP022_general_intrinsic_v2
  | (apply QuantumNLS.Prop022DMain.PROP022_general_intrinsic_v2 <;> assumption)

end QuantumNLS.P22V2Spec
#print axioms QuantumNLS.P22V2Spec.PROP022_general_intrinsic_v2_spec
