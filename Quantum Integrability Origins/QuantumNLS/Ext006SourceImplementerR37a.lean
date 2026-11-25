import QuantumNLS.Ext006ActualHeisR37a
import QuantumNLS.Ext006ImplementerUniqueR37a

/-! The single-map implementation obligation, with existence and uniqueness
for exactly the original source blocks. The completed pair exponential and
Fredholm normalization remain separate obligations of the full BD-02 contract. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace QuantumNLS.Ext006SourceImplementerR37a
open Ext006KernelHilbertSchmidt Ext006SourceOrientationR37a Ext006ActualHeisR37a
open Ext006PhysQuasifree Ext006ImplementerUniqueR37a
variable {L : ℝ} [Fact (0 < L)]
attribute [local instance] InnerProductSpace.complexToReal

/-- From original physical symplecticity and HS beta alone, construct a
unitary satisfying both literal frozen Heisenberg predicates and prove its
uniqueness up to phase among ALL unitary solutions of those predicates. -/
theorem source_implementer_exists_unique_phase
    (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (hβ : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) ≠ ⊤) :
    ∃ V : Ext025B3PhysicalSectors.Fock L ≃ₗᵢ[ℂ] Ext025B3PhysicalSectors.Fock L,
      HeisAnn V (actualA (physicalBasis L) S) (actualB (physicalBasis L) S) ∧
      HeisCre V (actualA (physicalBasis L) S) (actualB (physicalBasis L) S) ∧
      ∀ W : Ext025B3PhysicalSectors.Fock L ≃ₗᵢ[ℂ] Ext025B3PhysicalSectors.Fock L,
        HeisAnn W (actualA (physicalBasis L) S) (actualB (physicalBasis L) S) →
        HeisCre W (actualA (physicalBasis L) S) (actualB (physicalBasis L) S) →
        ∃ c : ℂ, ‖c‖=1 ∧ ∀ x : Ext025B3PhysicalSectors.Fock L, W x=c • V x := by
  obtain ⟨V,hs,hA,hC⟩ := source_actual_Heis S hS hβ
  exact ⟨V,hA,hC,fun W hWA hWC =>
    implementer_unique_phase V W (actualA (physicalBasis L) S) (actualB (physicalBasis L) S)
      hs hA hC hWA hWC⟩

end QuantumNLS.Ext006SourceImplementerR37a

#print axioms QuantumNLS.Ext006SourceImplementerR37a.source_implementer_exists_unique_phase

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006SourceImplementerR37a." then
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
  Lean.logInfo m!"Round37a aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
