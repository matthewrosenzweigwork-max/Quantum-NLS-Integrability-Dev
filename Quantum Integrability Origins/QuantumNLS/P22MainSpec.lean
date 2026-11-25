import QuantumNLS.Prop022BMain
/-! integrator-authored trusted spec for PROP-022 Q7B:lem:pair (Prop022BMain): headline statement(s) copied verbatim from Prop022BMain (QuantumNLS.Prop022BMain). -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false
open scoped InnerProductSpace Topology NNReal ENNReal
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
attribute [local instance 2000] InnerProductSpace.complexToReal
namespace QuantumNLS.P22MainSpec
open QuantumNLS.Prop022BMain
open PhysicalTensor Prop022GTensor Prop022GAntiHS Prop022GClassical Prop022GLinear
open Prop022BIso Prop022BClass1 Prop022BClass2 Prop022BClass3 Prop022BFock1 Prop022BFock2 Prop022BFock3
open Prop022BIndep Prop022AFock
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {L : ℝ} [Fact (0 < L)]

set_option maxHeartbeats 8000000 in
theorem PROP022_general_spec [TopologicalSpace.SeparableSpace H] (L : ℝ) [Fact (0 < L)]
    (K : Kernels H) (M A : ℝ) (hM : 1 ≤ M) (hA : 0 < A) (hK : KBound K M A) (hs : KSelfAdj K)
    (u₀ : H) (hu₀ : ‖u₀‖ = 1) (T P : ℝ) (hP : 1 ≤ P) {ι : Type*} (e : HilbertBasis ι ℂ H) :
    (∀ hH : ¬ FiniteDimensional ℂ H,
      type_of% (Prop022AExact.PROP022_general_infinite_exact hH L K M A hM hA hK hs u₀ hu₀ T P hP e)) ∧
    (FiniteDimensional ℂ H →
      Nonempty (H →ₗᵢ[ℂ] L2T L) ∧ ∀ J : H →ₗᵢ[ℂ] L2T L,
        type_of% (PROP022_J_classical J K M A hM hA hK hs u₀ hu₀ T P hP e) ∧
        type_of% (PROP022_fock_J J K M A hM hA hK hs u₀ hu₀ e T P hP) ∧
        (∀ J' : H →ₗᵢ[ℂ] L2T L,
          (∀ v, WJ J' v = WJ J v) ∧ vacJ J' = vacJ J ∧
          (∀ t, QFJ J' (VJ J K M A hM hA hK hs u₀ hu₀ t 0 (vacJ J))) ∧
          (∀ t s, VJ J' K M A hM hA hK hs u₀ hu₀ t s = VJ J K M A hM hA hK hs u₀ hu₀ t s) ∧
          (∀ t, aSymJ J' K M A hA hK hs u₀ hu₀ t = aSymJ J K M A hA hK hs u₀ hu₀ t ∧
            bSymJ J' K M A hA hK hs u₀ hu₀ t = bSymJ J K M A hA hK hs u₀ hu₀ t) ∧
          (∀ (a : TensorCarrier.SymSector ℂ H 1 →L[ℂ] TensorCarrier.SymSector ℂ H 1)
            (b : TensorCarrier.SymSector ℂ H 2) (y : FockSpace H), QJ J' a b y = QJ J a b y))) := by
  first
  | exact QuantumNLS.Prop022BMain.PROP022_general
  | (apply QuantumNLS.Prop022BMain.PROP022_general <;> assumption)

end QuantumNLS.P22MainSpec
#print axioms QuantumNLS.P22MainSpec.PROP022_general_spec
