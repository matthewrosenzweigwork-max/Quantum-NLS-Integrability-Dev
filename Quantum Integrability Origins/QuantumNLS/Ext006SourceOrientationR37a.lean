import QuantumNLS.Ext006RowPairingR37a

/-! The adjoint real source is constructed as an automorphism. Its
symplecticity and exact HS beta mass are derived from the original source.
Its inverse-unitary row blocks are exactly the ORIGINAL source blocks. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped InnerProductSpace
namespace QuantumNLS.Ext006SourceOrientationR37a
open Ext006Blocks Ext006SymplecticKernel Ext006KernelHilbertSchmidt
open Ext006InverseSourceR36a Ext006StrongVacuumR33a Ext006BogoliubovAlg
open Ext006RowPairingR37a
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
attribute [local instance] InnerProductSpace.complexToReal

/-- Real Hilbert adjoint, with inverse proved from the supplied automorphism. -/
def adjointSource (S : E ≃L[ℝ] E) : E ≃L[ℝ] E :=
  ContinuousLinearEquiv.equivOfInverse S.toContinuousLinearMap.adjoint
    S.symm.toContinuousLinearMap.adjoint
    (fun x => by
      apply ext_inner_left ℝ
      intro y
      rw [ContinuousLinearMap.adjoint_inner_right,ContinuousLinearMap.adjoint_inner_right]
      simp only [ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.apply_symm_apply])
    (fun x => by
      apply ext_inner_left ℝ
      intro y
      rw [ContinuousLinearMap.adjoint_inner_right,ContinuousLinearMap.adjoint_inner_right]
      simp only [ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply])

lemma adjointSource_phase_inverse (S : E ≃L[ℝ] E) (hS : Symplectic S.toContinuousLinearMap)
    (x : E) : adjointSource S x= -J (S.symm (J x)) := by
  have h := congrArg (fun T : E →L[ℝ] E => T (J x)) (inverse_formula S hS)
  change S.symm (J x)= -J (S.toContinuousLinearMap.adjoint (J (J x))) at h
  simp only [J_sq,map_neg] at h
  simp only [neg_neg] at h
  rw [h,J_sq,neg_neg]
  rfl

omit [CompleteSpace E] in
lemma J_inner (x y : E) : inner ℂ (J x) (J y)=inner ℂ x y := by
  simp [J_apply]
  ring_nf
  simp [Complex.I_sq]

/-- No new symplecticity premise for the adjoint source. -/
theorem adjointSource_symplectic (S : E ≃L[ℝ] E) (hS : Symplectic S.toContinuousLinearMap) :
    Symplectic (adjointSource S).toContinuousLinearMap := by
  intro x y
  change (inner ℂ (adjointSource S x) (adjointSource S y)).im=(inner ℂ x y).im
  rw [adjointSource_phase_inverse S hS,adjointSource_phase_inverse S hS,inner_neg_neg,J_inner]
  exact (inverse_symplectic S hS (J x) (J y)).trans (congrArg Complex.im (J_inner x y))

lemma complexPart_adjoint (S : E ≃L[ℝ] E) :
    complexPart (adjointSource S).toContinuousLinearMap=
      (complexPart S.toContinuousLinearMap).adjoint := by
  change complexPart S.toContinuousLinearMap.adjoint=_
  simp only [complexPart,map_smulₛₗ,starRingEnd_apply,star_trivial,map_sub,
    ContinuousLinearMap.adjoint_comp,J_adjoint]
  ext x
  simp only [smul_apply,sub_apply,ContinuousLinearMap.comp_apply,map_neg,neg_apply]
  module

lemma antilinearPart_adjoint (S : E ≃L[ℝ] E) :
    antilinearPart (adjointSource S).toContinuousLinearMap=
      (antilinearPart S.toContinuousLinearMap).adjoint := by
  change antilinearPart S.toContinuousLinearMap.adjoint=_
  simp only [antilinearPart,map_smulₛₗ,starRingEnd_apply,star_trivial,map_add,
    ContinuousLinearMap.adjoint_comp,J_adjoint]
  ext x
  simp only [smul_apply,add_apply,ContinuousLinearMap.comp_apply,map_neg,neg_apply]
  module

lemma sourceP_adjoint (S : E ≃L[ℝ] E) :
    sourceP (adjointSource S)=(sourceP S).adjoint := by
  ext x
  change complexPart (adjointSource S).toContinuousLinearMap x=(sourceP S).adjoint x
  rw [complexPart_adjoint]
  exact congrArg (fun T : E →L[ℝ] E => T x) (restrict_adjoint (sourceP S))

/-- Exact conjugation and transpose, with positive sign for the real adjoint. -/
lemma beta_adjoint (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E) (x : E) :
    beta b (adjointSource S) x=conjugation b ((beta b S).adjoint (conjugation b x)) := by
  have had : (beta b S).adjoint.restrictScalars ℝ=
      conjugation b ∘L (antilinearPart S.toContinuousLinearMap).adjoint := by
    rw [← restrict_adjoint,beta_real,ContinuousLinearMap.adjoint_comp,conjugation_adjoint]
  have he := congrArg (fun T : E →L[ℝ] E => T (conjugation b x)) had
  change (beta b S).adjoint (conjugation b x)=
    conjugation b ((antilinearPart S.toContinuousLinearMap).adjoint (conjugation b x)) at he
  change antilinearPart (adjointSource S).toContinuousLinearMap (conjugation b x)=_
  rw [antilinearPart_adjoint,he,conjugation_sq]

theorem beta_adjoint_hsSq (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E) :
    TraceClass.hsSq b (beta b (adjointSource S))=TraceClass.hsSq b (beta b S) := by
  calc
    TraceClass.hsSq b (beta b (adjointSource S))=TraceClass.hsSq b (beta b S).adjoint := by
      simp only [TraceClass.hsSq,beta_adjoint,conjugation_basis,conjugation_norm]
    _ = _ := (TraceClass.hsSq_eq_hsSq_adjoint b b (beta b S)).symm

lemma coordinateOp_adjoint (b : HilbertBasis ℤ ℂ E) (T : E →L[ℂ] E) :
    coordinateOp b T.adjoint=(coordinateOp b T).adjoint := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  change inner ℂ (b.repr (T.adjoint (b.repr.symm x))) y=
    inner ℂ x (b.repr (T (b.repr.symm y)))
  rw [← b.repr.symm.inner_map_map,← b.repr.symm.inner_map_map x]
  simp only [LinearIsometryEquiv.symm_apply_apply]
  exact ContinuousLinearMap.adjoint_inner_left T _ _

/-- ORIGINAL complex-linear block in the fixed basis. -/
def actualA (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E) : H →L[ℂ] H :=
  coordinateOp b (sourceP S)

/-- ORIGINAL antilinear block's complex representative in the fixed basis. -/
def actualB (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E) : H →L[ℂ] H :=
  coordinateOp b (beta b S)

lemma adjoint_rows (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E) :
    rowA b (adjointSource S)=actualA b S ∧ rowB b (adjointSource S)=actualB b S := by
  constructor
  · rw [rowA,sourceP_adjoint,coordinateOp_adjoint,ContinuousLinearMap.adjoint_adjoint]
    rfl
  · have hb : coordinateOp b (beta b (adjointSource S))=tp (coordinateOp b (beta b S)) := by
      ext x : 1
      change b.repr (beta b (adjointSource S) (b.repr.symm x))=
        star ((coordinateOp b (beta b S)).adjoint (star x))
      rw [← coordinateOp_adjoint]
      change b.repr (beta b (adjointSource S) (b.repr.symm x))=
        star (b.repr ((beta b S).adjoint (b.repr.symm (star x))))
      rw [beta_adjoint,conjugation_apply,LinearIsometryEquiv.apply_symm_apply,
        conjugation_apply,LinearIsometryEquiv.apply_symm_apply]
    rw [rowB,hb,Ext006PhysSymplectic.tp_tp]
    rfl

omit [CompleteSpace E] in
/-- The row pair is literally the fixed-basis representation of S itself. -/
lemma actual_blocks_apply (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E) (x : H) :
    Ext006PhysSymplectic.Smap (actualA b S) (actualB b S) x=b.repr (S (b.repr.symm x)) := by
  change b.repr (sourceP S (b.repr.symm x))+
    b.repr (beta b S (b.repr.symm (star x)))=_
  change b.repr (complexPart S.toContinuousLinearMap (b.repr.symm x))+
    b.repr (antilinearPart S.toContinuousLinearMap
      (conjugation b (b.repr.symm (star x))))=_
  simp only [conjugation_apply,LinearIsometryEquiv.apply_symm_apply,star_star]
  rw [← map_add]
  exact congrArg b.repr (congrArg (fun T : E →L[ℝ] E => T (b.repr.symm x)) (parts_sum S.toContinuousLinearMap))

omit [CompleteSpace E] in
/-- Symplecticity and surjectivity of the literal original coordinate blocks. -/
theorem actual_blocks_symplectic (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E)
    (hS : Symplectic S.toContinuousLinearMap) :
    Ext006PhysSymplectic.PhysSymplectic (actualA b S) (actualB b S) := by
  constructor
  · intro x y
    rw [actual_blocks_apply,actual_blocks_apply,LinearIsometryEquiv.inner_map_map]
    exact (hS (b.repr.symm x) (b.repr.symm y)).trans
      (congrArg Complex.im (b.repr.symm.inner_map_map x y))
  · intro y
    refine ⟨b.repr (S.symm (b.repr.symm y)),?_⟩
    rw [actual_blocks_apply,LinearIsometryEquiv.symm_apply_apply,
      ContinuousLinearEquiv.apply_symm_apply,LinearIsometryEquiv.apply_symm_apply]

end QuantumNLS.Ext006SourceOrientationR37a

#print axioms QuantumNLS.Ext006SourceOrientationR37a.actual_blocks_symplectic

#print axioms QuantumNLS.Ext006SourceOrientationR37a.adjointSource_symplectic

#print axioms QuantumNLS.Ext006SourceOrientationR37a.sourceP_adjoint

#print axioms QuantumNLS.Ext006SourceOrientationR37a.beta_adjoint

#print axioms QuantumNLS.Ext006SourceOrientationR37a.beta_adjoint_hsSq

#print axioms QuantumNLS.Ext006SourceOrientationR37a.adjoint_rows

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006SourceOrientationR37a." then
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
