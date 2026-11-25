import QuantumNLS.Ext006CanonicalVacuumR38a

/-! Exact original/adjoint/inverse sign conversion. In the frozen row
convention V Omega has the canonical kernel MINUS the original source K.
This is a proved identity, not a change to any frozen convention. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace QuantumNLS.Ext006CanonicalSignR38a
open Ext006Blocks Ext006SymplecticKernel Ext006KernelHilbertSchmidt
open Ext006InverseSourceR36a Ext006SourceOrientationR37a Ext006CanonicalOrientationR38a
variable {L : ℝ} [Fact (0 < L)]
attribute [local instance] InnerProductSpace.complexToReal

variable (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Symplectic S.toContinuousLinearMap)
include hS

lemma vacuumSource_complexPart :
    complexPart (vacuumSource S).toContinuousLinearMap = complexPart S.toContinuousLinearMap := by
  change complexPart (adjointSource S).symm.toContinuousLinearMap = _
  erw [complexPart_inverse (adjointSource S) (adjointSource_symplectic S hS),
    complexPart_adjoint, ContinuousLinearMap.adjoint_adjoint]
  rfl

lemma vacuumSource_antilinearPart :
    antilinearPart (vacuumSource S).toContinuousLinearMap =
      -antilinearPart S.toContinuousLinearMap := by
  change antilinearPart (adjointSource S).symm.toContinuousLinearMap = _
  erw [antilinearPart_inverse (adjointSource S) (adjointSource_symplectic S hS),
    antilinearPart_adjoint, ContinuousLinearMap.adjoint_adjoint]
  rfl

/-- The complex-linear block is unchanged by the full orientation conversion. -/
theorem vacuumSource_P : sourceP (vacuumSource S) = sourceP S := by
  ext x : 1
  change complexPart (vacuumSource S).toContinuousLinearMap x =
    complexPart S.toContinuousLinearMap x
  erw [vacuumSource_complexPart S hS]

/-- The source lower-left block changes sign, without a missing conjugation. -/
theorem vacuumSource_Q :
    sourceQ (physicalBasis L) (vacuumSource S) = -sourceQ (physicalBasis L) S := by
  ext x : 1
  change conjugation (physicalBasis L) (antilinearPart (vacuumSource S).toContinuousLinearMap x) =
    -conjugation (physicalBasis L) (antilinearPart S.toContinuousLinearMap x)
  erw [vacuumSource_antilinearPart S hS, neg_apply, map_neg]

theorem vacuumSource_beta :
    beta (physicalBasis L) (vacuumSource S) = -beta (physicalBasis L) S := by
  ext x : 1
  change antilinearPart (vacuumSource S).toContinuousLinearMap
    (conjugation (physicalBasis L) x) =
      -antilinearPart S.toContinuousLinearMap (conjugation (physicalBasis L) x)
  erw [vacuumSource_antilinearPart S hS, neg_apply]

lemma vacuumSource_PInv :
    sourcePInv (vacuumSource S) (vacuumSource_symplectic S hS) = sourcePInv S hS := by
  ext x : 1
  calc
    sourcePInv (vacuumSource S) (vacuumSource_symplectic S hS) x =
        sourcePInv S hS (sourceP S
          (sourcePInv (vacuumSource S) (vacuumSource_symplectic S hS) x)) :=
      (sourcePInv_left S hS _).symm
    _ = sourcePInv S hS x := by
      erw [← vacuumSource_P S hS, sourcePInv_right]

/-- The canonical kernel for the ORIGINAL-row vacuum is exactly -K(S).
The exponent remains the literal -a*(K)/2 when expressed in this kernel. -/
theorem vacuumKernel_eq_neg_source_squeeze :
    vacuumKernel S hS = -squeeze (physicalBasis L) S hS := by
  erw [vacuumKernel_source_formula, sourceK_formula (physicalBasis L) S hS,
    vacuumSource_Q S hS, vacuumSource_PInv S hS, ContinuousLinearMap.neg_comp]
  ext x : 1
  change conjugation (physicalBasis L)
    (-((sourceQ (physicalBasis L) S ∘L sourcePInv S hS) (conjugation (physicalBasis L) x))) =
      -conjugation (physicalBasis L)
        ((sourceQ (physicalBasis L) S ∘L sourcePInv S hS) (conjugation (physicalBasis L) x))
  exact map_neg _ _

end QuantumNLS.Ext006CanonicalSignR38a

#print axioms QuantumNLS.Ext006CanonicalSignR38a.vacuumSource_P

#print axioms QuantumNLS.Ext006CanonicalSignR38a.vacuumSource_Q

#print axioms QuantumNLS.Ext006CanonicalSignR38a.vacuumSource_beta

#print axioms QuantumNLS.Ext006CanonicalSignR38a.vacuumSource_PInv

#print axioms QuantumNLS.Ext006CanonicalSignR38a.vacuumKernel_eq_neg_source_squeeze

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006CanonicalSignR38a." then
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
