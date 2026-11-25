import QuantumNLS.Ext006BD02R40a

/-! R41a: orientation of the actual smeared FIELD matrix coefficients.
This module does not define a substitute Weyl representation and does not
claim exponentiation or a source-Weyl implementation theorem. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped InnerProductSpace
namespace QuantumNLS.Ext006FieldOrientationR41a
open Ext006BogoliubovAlg Ext006PhysSymplectic Ext006QuasifreeWeak
open Ext006PhysQuasifree Ext006PhysFockCoord Ext006KernelHilbertSchmidt
open Ext006SourceOrientationR37a Ext006CanonicalOrientationR38a
open Ext006Blocks Ext006SymplecticKernel

/-- Real Hilbert adjoint of the row map, at the level of smearing vectors. -/
def adjointSmear (A B : H →L[ℂ] H) (f : H) : H :=
  A.adjoint f + star (B.adjoint f)

lemma inner_bar (T : H →L[ℂ] H) (f x : H) :
    inner ℂ (star f) (bar T x) = inner ℂ (star (T.adjoint f)) x := by
  rw [← ContinuousLinearMap.adjoint_inner_left,adjoint_bar,bar_apply,star_star]

/-- Smeared field coefficient pairing; all smearings may have infinite support. -/
lemma row_field_pairing (A B : H →L[ℂ] H) (f u w : H) :
    inner ℂ f (A u+B w) + inner ℂ (star f) (bar A w+bar B u) =
      inner ℂ (adjointSmear A B f) u +
        inner ℂ (star (adjointSmear A B f)) w := by
  simp only [inner_add_right,inner_bar,adjointSmear,star_add,star_star,inner_add_left]
  rw [← ContinuousLinearMap.adjoint_inner_left A u f,
    ← ContinuousLinearMap.adjoint_inner_left B w f]
  ring

section GeneralOrientation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
attribute [local instance] InnerProductSpace.complexToReal

lemma inverse_adjoint_eq_imp_antilinear_zero
    (S : E ≃L[ℝ] E) (hS : Symplectic S.toContinuousLinearMap)
    (he : (adjointSource S).symm=S) : antilinearPart S.toContinuousLinearMap=0 := by
  have hi : adjointSource S=S.symm := by
    simpa only [ContinuousLinearEquiv.symm_symm] using
      congrArg (fun T : E ≃L[ℝ] E => T.symm) he
  have hp := antilinearPart_adjoint S
  rw [hi] at hp
  have hn := (antilinearPart_inverse S hS).symm.trans hp
  have hz : (antilinearPart S.toContinuousLinearMap).adjoint=0 := by
    have hs : (antilinearPart S.toContinuousLinearMap).adjoint +
        (antilinearPart S.toContinuousLinearMap).adjoint=0 :=
      (congrArg (fun T => (antilinearPart S.toContinuousLinearMap).adjoint+T) hn).symm.trans
        (add_neg_cancel _)
    calc
      _ = (1/2:ℝ) • ((antilinearPart S.toContinuousLinearMap).adjoint+
        (antilinearPart S.toContinuousLinearMap).adjoint) := by module
      _ = 0 := by rw [hs,smul_zero]
  have hh := congrArg (fun T : E →L[ℝ] E => T.adjoint) hz
  simpa only [ContinuousLinearMap.adjoint_adjoint,map_zero] using hh
end GeneralOrientation

variable {L : ℝ} [Fact (0 < L)]
attribute [local instance] InnerProductSpace.complexToReal

/-- Coefficient of a(f)+a*(f) in its maximal weak occupation graph.
This definition alone asserts neither square summability of the output nor
self-adjointness. Those are separate domain obligations. -/
def fieldCoefficient (f : H) (z : OccupationHilbert.L2 Occupation.Occ)
    (n : Occupation.Occ) : ℂ :=
  inner ℂ f (xvec z n) + inner ℂ (star f) (yvec z n)

/-- Both frozen predicates imply the real-adjoint smeared matrix identity.
No invariance of an unbounded operator domain is inferred from this equality. -/
theorem Heis_fieldCoefficient
    (V : Ext025B3PhysicalSectors.Fock L ≃ₗᵢ[ℂ] Ext025B3PhysicalSectors.Fock L)
    (A B : H →L[ℂ] H) (hA : HeisAnn V A B) (hC : HeisCre V A B)
    (f : H) (n m : Occupation.Occ) :
    fieldCoefficient f (Vtil V (lp.single 2 m 1)) n =
      inner ℂ (adjointSmear A B f) (uvec V n m) +
        inner ℂ (star (adjointSmear A B f)) (wvec V n m) := by
  have hx : xvec (Vtil V (lp.single 2 m 1)) n=A (uvec V n m)+B (wvec V n m) := by
    apply lp.ext
    funext d
    rw [xvec_Vtil]
    exact hA d n m _ _ (uvec_apply V n m) (wvec_apply V n m)
  have hy : yvec (Vtil V (lp.single 2 m 1)) n=bar A (wvec V n m)+bar B (uvec V n m) := by
    apply lp.ext
    funext d
    rw [yvec_Vtil]
    exact hC d n m _ _ (uvec_apply V n m) (wvec_apply V n m)
  rw [fieldCoefficient,hx,hy]
  exact row_field_pairing A B f _ _

lemma actualA_adjoint
    (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L) :
    actualA (physicalBasis L) (adjointSource S)=(actualA (physicalBasis L) S).adjoint := by
  exact (congrArg (Ext006StrongVacuumR33a.coordinateOp (physicalBasis L))
    (sourceP_adjoint S)).trans (coordinateOp_adjoint (physicalBasis L) (sourceP S))

lemma actualB_adjoint
    (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L) :
    actualB (physicalBasis L) (adjointSource S)=tp (actualB (physicalBasis L) S) := by
  have hb := congrArg tp (adjoint_rows (physicalBasis L) S).2
  simpa only [Ext006RowPairingR37a.rowB,tp_tp,actualB] using hb

/-- In physical one-particle coordinates the smearing is literally S* f. -/
theorem adjointSmear_actual
    (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L) (f : H) :
    adjointSmear (actualA (physicalBasis L) S) (actualB (physicalBasis L) S) f =
      (physicalBasis L).repr (adjointSource S ((physicalBasis L).repr.symm f)) := by
  rw [← actual_blocks_apply (physicalBasis L) (adjointSource S) f,
    Smap,actualA_adjoint,actualB_adjoint,tp_apply,star_star]
  rfl

/-- Original-row Heis identities smear by S*, not by an unproved relabeling. -/
theorem original_Heis_fieldCoefficient
    (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (V : Ext025B3PhysicalSectors.Fock L ≃ₗᵢ[ℂ] Ext025B3PhysicalSectors.Fock L)
    (hA : HeisAnn V (actualA (physicalBasis L) S) (actualB (physicalBasis L) S))
    (hC : HeisCre V (actualA (physicalBasis L) S) (actualB (physicalBasis L) S))
    (f : H) (n m : Occupation.Occ) :
    fieldCoefficient f (Vtil V (lp.single 2 m 1)) n =
      inner ℂ ((physicalBasis L).repr (adjointSource S ((physicalBasis L).repr.symm f)))
        (uvec V n m) +
      inner ℂ (star ((physicalBasis L).repr (adjointSource S ((physicalBasis L).repr.symm f))))
        (wvec V n m) := by
  simpa only [adjointSmear_actual] using
    Heis_fieldCoefficient V _ _ hA hC f n m

/-- If the inverse-adjoint orientation were the original map, its actual
antilinear block would have to vanish. This follows from symplecticity. -/
theorem vacuumSource_eq_imp_beta_zero
    (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Symplectic S.toContinuousLinearMap) (he : vacuumSource S=S) :
    beta (physicalBasis L) S=0 := by
  have hzero := inverse_adjoint_eq_imp_antilinear_zero S hS he
  apply ContinuousLinearMap.ext
  intro x
  exact congrArg (fun T : PhysicalTensor.L2T L →L[ℝ] PhysicalTensor.L2T L =>
    T (conjugation (physicalBasis L) x)) hzero

/-- A nonzero original beta rules out silently identifying the two sources. -/
theorem vacuumSource_ne_of_beta_ne_zero
    (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Symplectic S.toContinuousLinearMap) (hβ : beta (physicalBasis L) S ≠ 0) :
    vacuumSource S ≠ S := fun he => hβ (vacuumSource_eq_imp_beta_zero S hS he)

end QuantumNLS.Ext006FieldOrientationR41a
#print axioms QuantumNLS.Ext006FieldOrientationR41a.original_Heis_fieldCoefficient
#print axioms QuantumNLS.Ext006FieldOrientationR41a.vacuumSource_eq_imp_beta_zero
#print axioms QuantumNLS.Ext006FieldOrientationR41a.vacuumSource_ne_of_beta_ne_zero

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006FieldOrientationR41a." then
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
  Lean.logInfo m!"Round41a aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
