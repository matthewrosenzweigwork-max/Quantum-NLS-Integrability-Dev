import QuantumNLS.Ext006PhysicalFieldR41a

/-! R42a: the inverse real adjoint is a derived admissible source.
The frozen row construction is applied to this map; no Weyl conclusion is
claimed by the algebraic orientation lemmas. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped InnerProductSpace
namespace QuantumNLS.Ext006ReorientationR42a
open Ext006Blocks Ext006SymplecticKernel Ext006KernelHilbertSchmidt
open Ext006InverseSourceR36a Ext006SourceOrientationR37a Ext006CanonicalOrientationR38a
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
attribute [local instance] InnerProductSpace.complexToReal

/-- The source used as INPUT to the frozen original-row construction. -/
def reorient (S : E ≃L[ℝ] E) : E ≃L[ℝ] E := adjointSource S.symm

lemma adjointSource_adjointSource (S : E ≃L[ℝ] E) :
    adjointSource (adjointSource S) = S := by
  ext x
  change S.toContinuousLinearMap.adjoint.adjoint x = S x
  rw [ContinuousLinearMap.adjoint_adjoint]
  rfl

lemma adjointSource_symm (S : E ≃L[ℝ] E) :
    adjointSource S.symm = (adjointSource S).symm := rfl

lemma adjointSource_reorient (S : E ≃L[ℝ] E) :
    adjointSource (reorient S) = S.symm := adjointSource_adjointSource S.symm

lemma reorient_reorient (S : E ≃L[ℝ] E) : reorient (reorient S) = S := by
  rw [reorient,adjointSource_symm,adjointSource_reorient,ContinuousLinearEquiv.symm_symm]

/-- Symplecticity of the inverse real adjoint uses only the original premise. -/
theorem reorient_symplectic (S : E ≃L[ℝ] E) (hS : Symplectic S.toContinuousLinearMap) :
    Symplectic (reorient S).toContinuousLinearMap :=
  adjointSource_symplectic S.symm (inverse_symplectic S hS)

/-- The beta HS mass is exactly preserved, with no additional HS hypothesis. -/
theorem reorient_beta_hsSq (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E)
    (hS : Symplectic S.toContinuousLinearMap) :
    TraceClass.hsSq b (beta b (reorient S)) = TraceClass.hsSq b (beta b S) :=
  (beta_adjoint_hsSq b S.symm).trans (inverse_beta_hsSq b S hS)

/-- The linear block is unchanged under the combined orientation. -/
theorem reorient_P (S : E ≃L[ℝ] E) (hS : Symplectic S.toContinuousLinearMap) :
    sourceP (reorient S) = sourceP S := by
  ext x
  change complexPart (adjointSource S.symm).toContinuousLinearMap x =
    complexPart S.toContinuousLinearMap x
  rw [complexPart_adjoint,complexPart_inverse S hS,ContinuousLinearMap.adjoint_adjoint]

/-- The antilinear part changes sign. This fixes the squeeze orientation. -/
theorem reorient_antilinearPart (S : E ≃L[ℝ] E)
    (hS : Symplectic S.toContinuousLinearMap) :
    antilinearPart (reorient S).toContinuousLinearMap = -antilinearPart S.toContinuousLinearMap := by
  change antilinearPart (adjointSource S.symm).toContinuousLinearMap = _
  rw [antilinearPart_adjoint,antilinearPart_inverse S hS,map_neg,
    ContinuousLinearMap.adjoint_adjoint]

theorem reorient_beta (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E)
    (hS : Symplectic S.toContinuousLinearMap) : beta b (reorient S) = -beta b S := by
  ext x
  change antilinearPart (reorient S).toContinuousLinearMap (conjugation b x) = _
  rw [reorient_antilinearPart S hS]
  rfl

variable {L : ℝ} [Fact (0 < L)]

lemma reorient_eq_vacuumSource (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L) :
    reorient S = vacuumSource S := rfl

/-- The frozen construction's vacuum source is now literally the ORIGINAL S. -/
theorem vacuumSource_reorient (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L) :
    vacuumSource (reorient S) = S := by
  change (adjointSource (reorient S)).symm = S
  erw [adjointSource_reorient S,ContinuousLinearEquiv.symm_symm]

/-- The kernel used by the frozen construction at the new input is +K(S).
It is not the old -K(S) vacuum. -/
theorem vacuumKernel_reorient (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Symplectic S.toContinuousLinearMap) :
    vacuumKernel (reorient S) (reorient_symplectic S hS) = squeeze (physicalBasis L) S hS := by
  unfold vacuumKernel
  simp only [vacuumSource_reorient]

/-- The row smearing at the new input is S^-1, so the FORWARD unitary acts
at S after inversion. This is the coefficient-level orientation only. -/
theorem reoriented_Heis_fieldCoefficient
    (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (V : Ext025B3PhysicalSectors.Fock L ≃ₗᵢ[ℂ] Ext025B3PhysicalSectors.Fock L)
    (hA : Ext006PhysQuasifree.HeisAnn V (actualA (physicalBasis L) (reorient S))
      (actualB (physicalBasis L) (reorient S)))
    (hC : Ext006PhysQuasifree.HeisCre V (actualA (physicalBasis L) (reorient S))
      (actualB (physicalBasis L) (reorient S)))
    (f : Ext006BogoliubovAlg.H) (n m : Occupation.Occ) :
    Ext006FieldOrientationR41a.fieldCoefficient f
      (Ext006PhysQuasifree.Vtil V (lp.single 2 m 1)) n =
      inner ℂ ((physicalBasis L).repr (S.symm ((physicalBasis L).repr.symm f)))
        (Ext006PhysQuasifree.uvec V n m) +
      inner ℂ (star ((physicalBasis L).repr (S.symm ((physicalBasis L).repr.symm f))))
        (Ext006PhysQuasifree.wvec V n m) := by
  have he := Ext006FieldOrientationR41a.original_Heis_fieldCoefficient (reorient S) V hA hC f n m
  erw [adjointSource_reorient S] at he
  exact he

end QuantumNLS.Ext006ReorientationR42a
#print axioms QuantumNLS.Ext006ReorientationR42a.reorient_symplectic
#print axioms QuantumNLS.Ext006ReorientationR42a.reorient_beta_hsSq
#print axioms QuantumNLS.Ext006ReorientationR42a.vacuumKernel_reorient
#print axioms QuantumNLS.Ext006ReorientationR42a.reoriented_Heis_fieldCoefficient

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006ReorientationR42a." then
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
