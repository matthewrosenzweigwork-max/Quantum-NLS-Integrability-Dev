import QuantumNLS.Ext006BD02R44a
/-! integrator-authored trusted spec for EXT-006 FIN-CORE-BD-02 (review record r60 PASS): headline statement(s) copied verbatim from Ext006BD02R44a (QuantumNLS.Ext006BD02R44a). -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped InnerProductSpace ENNReal
namespace QuantumNLS.E006Spec
open QuantumNLS.Ext006BD02R44a
open Ext006KernelHilbertSchmidt Ext006CompressionR32a Ext006OriginalVacuumR42a
open Ext006OriginalNormalizationR42a Ext006SourceWeylR44a Ext006NaturalWeylR44a
open Ext006FredholmTracePower Ext006FredholmNormR40a Ext006PhysicalExponentialTerms
open Ext006PhysicalNormBridge.PairTensor Ext006PhysFockCoord Ext006PhysQuasifree
open Ext006SourceOrientationR37a Ext006NumberPhase
variable {L : ℝ} [Fact (0 < L)]
attribute [local instance] InnerProductSpace.complexToReal

set_option maxHeartbeats 8000000 in
theorem FIN_CORE_BD_02_spec
    (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (hβ : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) ≠ ⊤) :
    let K := squeeze (physicalBasis L) S hS
    let c : ℝ := (fredholmDet (K.adjoint ∘L K))^(1/4 : ℝ)
    K = operatorConjugate (physicalBasis L)
      (sourceQ (physicalBasis L) S ∘L sourcePInv S hS) ∧
    (∀ i j, coordinates (physicalBasis L) K i j=coordinates (physicalBasis L) K j i) ∧
    ‖K‖<1 ∧ TraceClass.hsSq (physicalBasis L) K ≠ ⊤ ∧ 0<c ∧
    HasSum (fockTerm (physicalPair (physicalBasis L) K
      (original_kernel_properties S hS hβ).2.2 (original_kernel_properties S hS hβ).1))
      (originalExponential S hS hβ) ∧
    (∀ n : ℕ, term (physicalPair (physicalBasis L) K
      (original_kernel_properties S hS hβ).2.2 (original_kernel_properties S hS hβ).1) n =
      ((-1/2 : ℂ)^n/(n.factorial : ℂ)) • power (physicalPair (physicalBasis L) K
        (original_kernel_properties S hS hβ).2.2 (original_kernel_properties S hS hβ).1) n) ∧
    originalVacuum S hS hβ=(c : ℂ) • originalExponential S hS hβ ∧
    ‖originalVacuum S hS hβ‖=1 ∧
    inner ℂ vac (originalExponential S hS hβ)=1 ∧
    inner ℂ vac (originalVacuum S hS hβ)=(c : ℂ) ∧
    (∃ t : ℝ, 1<t ∧ numberExpectation (fun n => ENNReal.ofReal (t^n))
      (originalVacuum S hS hβ) ≠ ⊤) ∧
    ∃ U : Ext025B3PhysicalSectors.Fock L ≃ₗᵢ[ℂ] Ext025B3PhysicalSectors.Fock L,
      SourceWeylImplementer S U ∧ U vac=originalVacuum S hS hβ ∧
      (inner ℂ vac (U vac)).im=0 ∧ 0<(inner ℂ vac (U vac)).re ∧
      ∀ V : Ext025B3PhysicalSectors.Fock L ≃ₗᵢ[ℂ] Ext025B3PhysicalSectors.Fock L,
        SourceWeylImplementer S V →
        (∃ z : ℂ, ‖z‖=1 ∧ ∀ x, V x=z • U x) ∧
        (∃ z : ℂ, ‖z‖=1 ∧ V vac=z • ((c : ℂ) • originalExponential S hS hβ)) ∧
        (∀ w : ℕ → ℝ≥0∞, numberExpectation w (V vac)=
          numberExpectation w ((c : ℂ) • originalExponential S hS hβ)) ∧
        numberExpectation (fun n => (n : ℝ≥0∞)) (V vac)=
          TraceClass.posTrace ((beta (physicalBasis L) S).adjoint ∘L beta (physicalBasis L) S) ∧
        numberExpectation (fun n => (n : ℝ≥0∞)) (V vac)=
          TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) ∧
        numberExpectation (fun n => (n : ℝ≥0∞)) (V vac) ≠ ⊤ ∧
        (∃ t : ℝ, 1<t ∧ numberExpectation (fun n => ENNReal.ofReal (t^n)) (V vac) ≠ ⊤) ∧
        ((inner ℂ vac (V vac)).im=0 → 0<(inner ℂ vac (V vac)).re →
          ∀ x : Ext025B3PhysicalSectors.Fock L, V x=U x) := by
  exact QuantumNLS.Ext006BD02R44a.«FIN-CORE-BD-02» S hS hβ

end QuantumNLS.E006Spec
#print axioms QuantumNLS.E006Spec.FIN_CORE_BD_02_spec
