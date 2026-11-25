import QuantumNLS.Prop022BFock3
/-! integrator-authored trusted spec for PROP-022 Q7B:lem:pair (Prop022BFock3): headline statement(s) copied verbatim from Prop022BFock3 (QuantumNLS.Prop022BFock3). -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false
open scoped InnerProductSpace Topology NNReal ENNReal
open ContinuousLinearMap
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
attribute [local instance 2000] InnerProductSpace.complexToReal
namespace QuantumNLS.P22FockSpec
open QuantumNLS.Prop022BFock3
open TensorCarrier PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors
open Prop022GTensor Prop022AIsoTensor Prop022GAntiHS Prop022GClassical Prop022GLinear
open Prop022BIso Prop022BClass1 Prop022BClass2 Prop022BFock1 Prop022BFock2
open Prop022FactorialCoefficientsR115 Prop022ActualProfileR117 Prop022FockPropagatorR122
open Prop022PositiveDataR126 Prop022AFock Prop022ACovIndep Prop022AWeyl Prop022OVacuum
open Ext006PhysFockCoord Ext006PhysQuasifree Prop022TensorCompressionR115 Prop022VariationalR123 Prop022PairHSR122
open Prop022PrintedCoefficientsR124 Prop022ACoherent Prop022ACovPhys Prop022AIndep
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {L : ℝ} [Fact (0 < L)]
variable (J : H →ₗᵢ[ℂ] L2T L) (K : Kernels H) (M A : ℝ) (hM : 1 ≤ M) (hA : 0 < A)
  (hK : KBound K M A) (hs : KSelfAdj K) (u₀ : H) (hu₀ : ‖u₀‖ = 1)

set_option maxHeartbeats 8000000 in
theorem PROP022_fock_J_spec {ι : Type*} (e : HilbertBasis ι ℂ H) (T P : ℝ) (hP : 1 ≤ P) :
    let V := VJ J K M A hM hA hK hs u₀ hu₀
    (∀ s x, V s s x = x) ∧
    (∀ r s t x, V t s (V s r x) = V t r x) ∧
    (∀ s x, Continuous (fun t => V t s x)) ∧
    (∀ s t (x : FockSpace H), (∀ j : ℕ, x ∈ momentDomainH j) →
      HasDerivAt (fun r => V r s x)
        ((-Complex.I) • QJ J (aSymJ J K M A hA hK hs u₀ hu₀ t)
          (bSymJ J K M A hA hK hs u₀ hu₀ t) (V t s x)) t) ∧
    (∀ s t (v : H) (x : FockSpace H),
      V t s (WJ J v ((V t s).symm x)) =
        WJ J (SJ J K M A hA.le hK hs u₀ hu₀ t s v) x) ∧
    (∀ t, QFJ J (V t 0 (vacJ J)) ∧ ‖V t 0 (vacJ J)‖ = 1 ∧
      numExpH (V t 0 (vacJ J)) = antiHS e (betaJ J K M A hA.le hK hs u₀ hu₀ t 0)) := by
  first
  | exact QuantumNLS.Prop022BFock3.PROP022_fock_J
  | (apply QuantumNLS.Prop022BFock3.PROP022_fock_J <;> assumption)

end QuantumNLS.P22FockSpec
#print axioms QuantumNLS.P22FockSpec.PROP022_fock_J_spec
