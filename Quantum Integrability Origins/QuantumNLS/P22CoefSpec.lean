import QuantumNLS.Prop022DCoef
/-! integrator-authored trusted spec for PROP-022 intrinsic (Prop022DCoef): headline statement(s) copied verbatim from Prop022DCoef (QuantumNLS.Prop022DCoef). -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false
open scoped InnerProductSpace
open ContinuousLinearMap
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
attribute [local instance 2000] InnerProductSpace.complexToReal
namespace QuantumNLS.P22CoefSpec
open QuantumNLS.Prop022DCoef
open TensorCarrier PhysicalTensor Prop022GTensor Prop022AIsoTensor Prop022GClassical Prop022GLinear
open Prop022GAntiHS Prop022BIso Prop022BCoef Prop022AFock
open Prop022FactorialCoefficientsR115 Prop022ActualProfileR117 Prop022PositiveDataR126
open Prop022PrintedCoefficientsR124 Prop022PairHSR122 Ext006PairDensityR40a Ext006KernelHilbertSchmidt
open Ext006PhysicalNormBridge.PairTensor Prop022TensorCompressionR115 BetheCoefficientTransform Ext025B3PhysicalSectors
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {L : ℝ} [Fact (0 < L)]
variable (U : H ≃ₗᵢ[ℂ] L2T L) (K : Kernels H) (M A : ℝ) (hA : 0 ≤ A) (hK : KBound K M A)
  (hs : KSelfAdj K) (u₀ : H) (hu₀ : ‖u₀‖ = 1)

set_option maxHeartbeats 8000000 in
theorem aSym_rep_spec (t : ℝ) (x y : H) :
    ⟪powerH 1 x, aSym U K M A hA hK hs u₀ hu₀ t (powerH 1 y)⟫_ℂ =
      ⟪x, aH U K M A hA hK hs u₀ hu₀ t y⟫_ℂ := by
  first
  | exact QuantumNLS.Prop022DCoef.aSym_rep
  | (apply QuantumNLS.Prop022DCoef.aSym_rep <;> assumption)

set_option maxHeartbeats 8000000 in
theorem bSym_rep_spec (t : ℝ) (x y : H) :
    ⟪x, bH U K M A hA hK hs u₀ hu₀ t y⟫_ℂ =
      ⟪htmul y x, twoIso (E := H) (bSym U K M A hA hK hs u₀ hu₀ t : HilbertTensorPower ℂ H 2)⟫_ℂ := by
  first
  | exact QuantumNLS.Prop022DCoef.bSym_rep
  | (apply QuantumNLS.Prop022DCoef.bSym_rep <;> assumption)

end QuantumNLS.P22CoefSpec
#print axioms QuantumNLS.P22CoefSpec.aSym_rep_spec
#print axioms QuantumNLS.P22CoefSpec.bSym_rep_spec
