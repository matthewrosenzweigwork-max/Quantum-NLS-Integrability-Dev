import QuantumNLS.Prop022BPairInput
/-! integrator-authored trusted spec for PROP-022 Q7B:lem:pair (Prop022BPairInput): headline statement(s) copied verbatim from Prop022BPairInput (QuantumNLS.Prop022BPairInput). -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
open scoped InnerProductSpace ENNReal
namespace QuantumNLS.P22PairSpec
open QuantumNLS.Prop022BPairInput
open TensorCarrier PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors Prop022GTensor Prop022GClassical Prop022AFock Prop022ACovIndep
open Prop022BClass1 Prop022FockPropagatorR122 Prop022PositiveDataR126
variable {L : ℝ} [Fact (0 < L)]

set_option maxHeartbeats 8000000 in
theorem Prop022PairInput_of_general_spec (K : Kernels (L2T L)) (M A : ℝ) (hM : 1 ≤ M) (hA : 0 < A)
    (hK : KBound K M A) (hs : KSelfAdj K) (u₀ : Prop001.Sphere (L2T L)) (T P : ℝ) (hP : 1 ≤ P) :
    Prop024WeylConventionR55.Prop022PairInput K M A hM hA hK hs u₀ T P hP ∧
    (∀ (U : L2T L ≃ₗᵢ[ℂ] L2T L) (t s : ℝ) (z : Fock L),
      VH U K M A hA.le hK hs u₀.val u₀.property (zero_le_one.trans hM) t s z =
        propagator (positiveExtension K) M A (zero_le_one.trans hM) hA.le
          (positiveExtension_bound K M A hK) (positiveExtension_selfAdjoint K hs) u₀ s t z) := by
  first
  | exact QuantumNLS.Prop022BPairInput.Prop022PairInput_of_general
  | (apply QuantumNLS.Prop022BPairInput.Prop022PairInput_of_general <;> assumption)

end QuantumNLS.P22PairSpec
#print axioms QuantumNLS.P22PairSpec.Prop022PairInput_of_general_spec
