import QuantumNLS.Ext006SourceImplementerR37a

/-! Canonical coefficient vacuum with the exact orientation for the frozen
original-row Heisenberg predicates. That orientation is (S real-adjoint)^-1;
it is derived, and is not silently identified with S. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
open scoped InnerProductSpace
namespace QuantumNLS.Ext006CanonicalOrientationR38a
open Ext006KernelHilbertSchmidt Ext006SourceOrientationR37a Ext006InverseSourceR36a
open Ext006HSVacuumR32a Ext006CompressionR32a
variable {L : ℝ} [Fact (0 < L)]
attribute [local instance] InnerProductSpace.complexToReal

/-- The source whose canonical vacuum belongs to the ORIGINAL-row implementer. -/
def vacuumSource (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L) :
    PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L := (adjointSource S).symm

lemma vacuumSource_symplectic (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap) :
    Ext006SymplecticKernel.Symplectic (vacuumSource S).toContinuousLinearMap :=
  inverse_symplectic (adjointSource S) (adjointSource_symplectic S hS)

/-- No additional HS premise is imposed on the changed orientation. -/
theorem vacuumSource_beta_hsSq (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap) :
    TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) (vacuumSource S)) =
      TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) :=
  (inverse_beta_hsSq (physicalBasis L) (adjointSource S)
    (adjointSource_symplectic S hS)).trans (beta_adjoint_hsSq (physicalBasis L) S)

def vacuumKernel (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap) :
    PhysicalTensor.L2T L →L[ℂ] PhysicalTensor.L2T L :=
  squeeze (physicalBasis L) (vacuumSource S) (vacuumSource_symplectic S hS)

theorem vacuumKernel_properties (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (hβ : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) ≠ ⊤) :
    (∀ i j, coordinates (physicalBasis L) (vacuumKernel S hS) i j =
      coordinates (physicalBasis L) (vacuumKernel S hS) j i) ∧
    ‖vacuumKernel S hS‖ < 1 ∧ TraceClass.hsSq (physicalBasis L) (vacuumKernel S hS) ≠ ⊤ := by
  have ht : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) (vacuumSource S)) ≠ ⊤ :=
    fun h => hβ ((vacuumSource_beta_hsSq S hS).symm.trans h)
  obtain ⟨hs,hn,hk,-,-⟩ := «FIN-CORE-BD-02-kernel» (physicalBasis L)
    (vacuumSource S) (vacuumSource_symplectic S hS) ht
  exact ⟨hs,hn,hk⟩

/-- Equation (4.1), including the bar over the ENTIRE product, for the
explicitly oriented source. -/
theorem vacuumKernel_source_formula (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap) :
    vacuumKernel S hS = operatorConjugate (physicalBasis L)
      (sourceQ (physicalBasis L) (vacuumSource S) ∘L
        sourcePInv (vacuumSource S) (vacuumSource_symplectic S hS)) :=
  sourceK_formula (physicalBasis L) (vacuumSource S) (vacuumSource_symplectic S hS)

/-- The constructed canonical coefficient vacuum. Identification with the
physical pair exponential and its Fredholm normalization remains separate. -/
def canonicalVacuum (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (hβ : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) ≠ ⊤) :
    Ext025B3PhysicalSectors.Fock L :=
  physicalNormalized (vacuumKernel S hS) (vacuumKernel_properties S hS hβ).1
    (vacuumKernel_properties S hS hβ).2.1 (vacuumKernel_properties S hS hβ).2.2

theorem canonicalVacuum_norm (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (hβ : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) ≠ ⊤) :
    ‖canonicalVacuum S hS hβ‖ = 1 :=
  physicalNormalized_norm _ _ _ _

theorem canonicalVacuum_weak (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (hβ : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) ≠ ⊤) :
    Ext006PhysicalVacuum.PhysicalWeakVacuum
      (coordinates (physicalBasis L) (vacuumKernel S hS)) (canonicalVacuum S hS hβ) :=
  physicalNormalized_weak _ _ _ _

end QuantumNLS.Ext006CanonicalOrientationR38a

#print axioms QuantumNLS.Ext006CanonicalOrientationR38a.vacuumSource_beta_hsSq

#print axioms QuantumNLS.Ext006CanonicalOrientationR38a.vacuumKernel_properties

#print axioms QuantumNLS.Ext006CanonicalOrientationR38a.vacuumKernel_source_formula

#print axioms QuantumNLS.Ext006CanonicalOrientationR38a.canonicalVacuum_norm

#print axioms QuantumNLS.Ext006CanonicalOrientationR38a.canonicalVacuum_weak

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006CanonicalOrientationR38a." then
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
  Lean.logInfo m!"Round38a aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
