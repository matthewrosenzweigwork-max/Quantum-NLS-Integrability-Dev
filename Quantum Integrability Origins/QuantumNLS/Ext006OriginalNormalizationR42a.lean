import QuantumNLS.Ext006OriginalVacuumR42a

/-! The ORIGINAL-source normalized exponential has the positive vacuum
expectation specified by the source. Phase uniqueness here is still the
corrected row theorem, and is not claimed for unconstructed Weyl operators. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped InnerProductSpace
namespace QuantumNLS.Ext006OriginalNormalizationR42a
open Ext006KernelHilbertSchmidt Ext006SymplecticKernel Ext006CompressionR32a
open Ext006PhysicalSeriesR39a Ext006FredholmTracePower Ext006PhysFockCoord
open Ext006PhysQuasifree Ext006ReorientationR42a Ext006OriginalVacuumR42a
open Ext006SourceOrientationR37a
variable {L : ℝ} [Fact (0 < L)]
attribute [local instance] InnerProductSpace.complexToReal

theorem originalExponential_vacuum_expectation
    (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Symplectic S.toContinuousLinearMap)
    (hβ : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) ≠ ⊤) :
    inner ℂ vac (originalExponential S hS hβ) = 1 := by
  rw [vac,inner_physCore_ket]
  exact (physicalExponential_coefficient _ _ _ _ 0).trans
    (Ext006FormalVacuumR31a.coefficient_zero _)

theorem originalVacuum_vacuum_expectation
    (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Symplectic S.toContinuousLinearMap)
    (hβ : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) ≠ ⊤) :
    inner ℂ vac (originalVacuum S hS hβ) =
      (((fredholmDet ((squeeze (physicalBasis L) S hS).adjoint ∘L
        squeeze (physicalBasis L) S hS))^(1/4:ℝ) : ℝ) : ℂ) := by
  rw [originalVacuum_Fredholm S hS hβ,inner_smul_right,originalExponential_vacuum_expectation S hS hβ,mul_one]

theorem originalVacuum_vacuum_positive
    (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Symplectic S.toContinuousLinearMap)
    (hβ : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) ≠ ⊤) :
    0 < (inner ℂ vac (originalVacuum S hS hβ)).re := by
  rw [originalVacuum_vacuum_expectation S hS hβ,Complex.ofReal_re,← fourthRoot_eq_rpow]
  exact fourthRoot_pos _

/-- Whole-space phase uniqueness for the correctly reoriented ROW interface.
No Weyl-to-field equivalence is smuggled into its assumptions or conclusion. -/
theorem corrected_rows_unique_phase
    (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Symplectic S.toContinuousLinearMap)
    (U V : Ext025B3PhysicalSectors.Fock L ≃ₗᵢ[ℂ] Ext025B3PhysicalSectors.Fock L)
    (hUA : HeisAnn U (actualA (physicalBasis L) (reorient S)) (actualB (physicalBasis L) (reorient S)))
    (hUC : HeisCre U (actualA (physicalBasis L) (reorient S)) (actualB (physicalBasis L) (reorient S)))
    (hVA : HeisAnn V (actualA (physicalBasis L) (reorient S)) (actualB (physicalBasis L) (reorient S)))
    (hVC : HeisCre V (actualA (physicalBasis L) (reorient S)) (actualB (physicalBasis L) (reorient S))) :
    ∃ c : ℂ, ‖c‖=1 ∧ ∀ x : Ext025B3PhysicalSectors.Fock L, V x = c • U x :=
  Ext006ImplementerUniqueR37a.implementer_unique_phase U V _ _
    (actual_blocks_symplectic (physicalBasis L) (reorient S) (reorient_symplectic S hS))
    hUA hUC hVA hVC

end QuantumNLS.Ext006OriginalNormalizationR42a
#print axioms QuantumNLS.Ext006OriginalNormalizationR42a.originalVacuum_vacuum_expectation
#print axioms QuantumNLS.Ext006OriginalNormalizationR42a.originalVacuum_vacuum_positive
#print axioms QuantumNLS.Ext006OriginalNormalizationR42a.corrected_rows_unique_phase

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006OriginalNormalizationR42a." then
      pending := pending.push n
      roots := roots + 1
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn ".").any (fun s => s == "HeldGP14Tonelli" || s == "RegularCut") then
        throwError "Held identifier in dependency closure: {n}"
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
  Lean.logInfo m!"Round42a aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
