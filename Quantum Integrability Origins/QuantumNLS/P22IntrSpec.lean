import QuantumNLS.Prop022CMain
/-! integrator-authored trusted spec for PROP-022 intrinsic (Prop022CMain): headline statement(s) copied verbatim from Prop022CMain (QuantumNLS.Prop022CMain). -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false
noncomputable section
open scoped InnerProductSpace Topology NNReal ENNReal
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
attribute [local instance 2000] InnerProductSpace.complexToReal
namespace QuantumNLS.P22IntrSpec
open QuantumNLS.Prop022CMain
open QuantumNLS.TensorCarrier QuantumNLS.Prop022GTensor QuantumNLS.Prop022AIsoTensor
open QuantumNLS.Prop022BIso QuantumNLS.Prop022CCanon QuantumNLS.Prop022BFock1
open QuantumNLS.Prop022CWeyl QuantumNLS.Prop022CQuad QuantumNLS.Prop022CQuadTorus
open QuantumNLS.Prop022CIntrinsic QuantumNLS.Prop022AFock
open PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors
open Prop022GAntiHS Prop022GClassical Prop022GLinear Prop022BClass1 Prop022BClass2 Prop022BFock2
open Prop022BFock3 Prop022FactorialCoefficientsR115 Prop022PositiveDataR126
open Occupation Ext006IdentityCyclicR35a Ext006PhysFockCoord Prop022ACoherent Prop022AWeyl
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {L : ℝ} [Fact (0 < L)]

set_option maxHeartbeats 8000000 in
theorem PROP022_general_intrinsic_spec [TopologicalSpace.SeparableSpace H] (L : ℝ) [Fact (0 < L)]
    (K : Kernels H) (M A : ℝ) (hM : 1 ≤ M) (hA : 0 < A) (hK : KBound K M A) (hs : KSelfAdj K)
    (u₀ : H) (hu₀ : ‖u₀‖ = 1) (T P : ℝ) (hP : 1 ≤ P) {ι : Type*} (e : HilbertBasis ι ℂ H) :
    type_of% (Prop022BMain.PROP022_general L K M A hM hA hK hs u₀ hu₀ T P hP e) ∧
    (¬ FiniteDimensional ℂ H → ∀ U : H ≃ₗᵢ[ℂ] L2T L,
      (let hM0 : 0 ≤ M := by linarith
       IntrinsicFock (VH U K M A hA.le hK hs u₀ hu₀ hM0)
        (aSym U K M A hA.le hK hs u₀ hu₀) (bSym U K M A hA.le hK hs u₀ hu₀)
        (SH U K M A hA.le hK hs u₀ hu₀) (vacH U)
        (fun t => antiHS e (betaH U K M A hA.le hK hs u₀ hu₀ t 0))) ∧
      (∀ v, IsWeylOp v (WH U v) ∧ ∀ W, IsWeylOp v W → W = WH U v) ∧
      (∀ a b y, y ∈ momentDomainH 2 → QRel a b y (QH U a b y))) ∧
    (FiniteDimensional ℂ H → ∀ J : H →ₗᵢ[ℂ] L2T L,
      IntrinsicFock (VJ J K M A hM hA hK hs u₀ hu₀)
        (aSymJ J K M A hA hK hs u₀ hu₀) (bSymJ J K M A hA hK hs u₀ hu₀)
        (SJ J K M A hA.le hK hs u₀ hu₀) (vacJ J)
        (fun t => antiHS e (betaJ J K M A hA.le hK hs u₀ hu₀ t 0)) ∧
      (∀ v, IsWeylOp v (WJ J v) ∧ ∀ W, IsWeylOp v W → W = WJ J v) ∧
      (∀ a b y, y ∈ momentDomainH 2 → QRel a b y (QJ J a b y))) := by
  first
  | exact QuantumNLS.Prop022CMain.PROP022_general_intrinsic
  | (apply QuantumNLS.Prop022CMain.PROP022_general_intrinsic <;> assumption)

end QuantumNLS.P22IntrSpec
#print axioms QuantumNLS.P22IntrSpec.PROP022_general_intrinsic_spec
