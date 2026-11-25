import QuantumNLS.Ext006LiteralHeisR37a
import QuantumNLS.Ext006SourceOrientationR37a

/-! Existence of a physical unitary satisfying BOTH literal frozen
Heisenberg predicates for exactly the original source's row blocks.
No implementer, covariance or inverse-source HS premise is supplied. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace QuantumNLS.Ext006ActualHeisR37a
open Ext006KernelHilbertSchmidt Ext006SourceOrientationR37a Ext006LiteralHeisR37a
open Ext006PhysQuasifree Ext006PhysSymplectic
variable {L : ℝ} [Fact (0 < L)]
attribute [local instance] InnerProductSpace.complexToReal

/-- Original physical symplectic source and HS beta alone. The adjoint
source and its HS mass are derived, and both actual row identities are proved. -/
theorem source_actual_Heis
    (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (hβ : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) ≠ ⊤) :
    ∃ V : Ext025B3PhysicalSectors.Fock L ≃ₗᵢ[ℂ] Ext025B3PhysicalSectors.Fock L,
      PhysSymplectic (actualA (physicalBasis L) S) (actualB (physicalBasis L) S) ∧
      HeisAnn V (actualA (physicalBasis L) S) (actualB (physicalBasis L) S) ∧
      HeisCre V (actualA (physicalBasis L) S) (actualB (physicalBasis L) S) := by
  have ht : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) (adjointSource S)) ≠ ⊤ :=
    fun h => hβ ((beta_adjoint_hsSq (physicalBasis L) S).symm.trans h)
  obtain ⟨V,hA,hC⟩ := source_inverse_Heis (adjointSource S) (adjointSource_symplectic S hS) ht
  obtain ⟨ha,hb⟩ := adjoint_rows (physicalBasis L) S
  rw [ha,hb] at hA hC
  exact ⟨V,actual_blocks_symplectic (physicalBasis L) S hS,hA,hC⟩

/-- The original flow has an actual pure quasifree physical vacuum in the
frozen source interface, with both implementation identities discharged. -/
theorem source_physical_quasifree
    (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (hβ : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) ≠ ⊤) :
    ∃ x : Ext025B3PhysicalSectors.Fock L, PhysicalQuasifreeSource x := by
  obtain ⟨V,hs,hA,hC⟩ := source_actual_Heis S hS hβ
  exact ⟨V (Ext006PhysFockCoord.vac (L := L)),V,actualA (physicalBasis L) S,
    actualB (physicalBasis L) S,hs,hA,hC,rfl⟩

end QuantumNLS.Ext006ActualHeisR37a

#print axioms QuantumNLS.Ext006ActualHeisR37a.source_actual_Heis

#print axioms QuantumNLS.Ext006ActualHeisR37a.source_physical_quasifree

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006ActualHeisR37a." then
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
