import QuantumNLS.Ext006PhysicalSeriesR39a
import QuantumNLS.Ext006CanonicalSignR38a

/-! Literal original-row implementer vacua are normalized ACTUAL completed
physical pair exponentials with the proved kernel -squeeze(S). The positive
normalization is still expressed as inverse norm; Fredholm evaluation is open. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
open scoped InnerProductSpace
namespace QuantumNLS.Ext006CanonicalExponentialR39a
open Ext006KernelHilbertSchmidt Ext006CanonicalOrientationR38a
open Ext006PhysicalSeriesR39a Ext006PhysicalExponentialTerms
open Ext006PhysicalNormBridge.PairTensor Ext006ActualHeisR37a Ext006PhysFockCoord
open Ext006PhysQuasifree Ext006SourceOrientationR37a
variable {L : ℝ} [Fact (0 < L)]
attribute [local instance] InnerProductSpace.complexToReal

/-- The actual completed physical exponential for the correctly oriented source. -/
def sourceExponential (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (hβ : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) ≠ ⊤) :
    Ext025B3PhysicalSectors.Fock L :=
  physicalExponential (vacuumKernel S hS) (vacuumKernel_properties S hS hβ).1
    (vacuumKernel_properties S hS hβ).2.1 (vacuumKernel_properties S hS hβ).2.2

theorem sourceExponential_hasSum (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (hβ : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) ≠ ⊤) :
    HasSum (fockTerm (physicalPair (physicalBasis L) (vacuumKernel S hS)
      (vacuumKernel_properties S hS hβ).2.2 (vacuumKernel_properties S hS hβ).1))
      (sourceExponential S hS hβ) :=
  physical_exponential_hasSum _ _ _ _

theorem canonicalVacuum_eq_physical_exponential
    (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (hβ : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) ≠ ⊤) :
    canonicalVacuum S hS hβ =
      (‖sourceExponential S hS hβ‖⁻¹ : ℂ) • sourceExponential S hS hβ :=
  physicalNormalized_eq_exponential _ _ _ _

theorem sourceExponential_ne_zero (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (hβ : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) ≠ ⊤) :
    sourceExponential S hS hβ ≠ 0 := by
  intro hz
  have h := canonicalVacuum_norm S hS hβ
  rw [canonicalVacuum_eq_physical_exponential, hz, smul_zero, norm_zero] at h
  norm_num at h

theorem source_normalization_positive
    (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (hβ : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) ≠ ⊤) :
    0 < ‖sourceExponential S hS hβ‖⁻¹ :=
  inv_pos.mpr (norm_pos_iff.mpr (sourceExponential_ne_zero S hS hβ))

/-- Every literal-row implementing unitary has the actual completed physical
exponential vacuum, with no implementation or domain premise on its value. -/
theorem all_implementer_physical_exponential
    (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (hβ : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) ≠ ⊤)
    (V : Ext025B3PhysicalSectors.Fock L ≃ₗᵢ[ℂ] Ext025B3PhysicalSectors.Fock L)
    (hA : HeisAnn V (actualA (physicalBasis L) S) (actualB (physicalBasis L) S))
    (hC : HeisCre V (actualA (physicalBasis L) S) (actualB (physicalBasis L) S)) :
    ∃ c : ℂ, ‖c‖=1 ∧ V vac =
      c • ((‖sourceExponential S hS hβ‖⁻¹ : ℂ) • sourceExponential S hS hβ) := by
  obtain ⟨c,hc,he⟩ := Ext006CanonicalVacuumR38a.all_implementer_canonical_vacuum S hS hβ V hA hC
  exact ⟨c,hc,he.trans (congrArg (c • ·) (canonicalVacuum_eq_physical_exponential S hS hβ))⟩

/-- The exponent uses the oriented kernel, whose sign relative to the original
source is a proved identity. This keeps the literal -a*(K)/2 convention intact. -/
theorem source_kernel_sign (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap) :
    vacuumKernel S hS = -squeeze (physicalBasis L) S hS :=
  Ext006CanonicalSignR38a.vacuumKernel_eq_neg_source_squeeze S hS

end QuantumNLS.Ext006CanonicalExponentialR39a

#print axioms QuantumNLS.Ext006CanonicalExponentialR39a.sourceExponential_hasSum

#print axioms QuantumNLS.Ext006CanonicalExponentialR39a.canonicalVacuum_eq_physical_exponential

#print axioms QuantumNLS.Ext006CanonicalExponentialR39a.all_implementer_physical_exponential

#print axioms QuantumNLS.Ext006CanonicalExponentialR39a.source_kernel_sign

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006CanonicalExponentialR39a." then
      pending := pending.push n
      roots := roots + 1
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"Round39a aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
