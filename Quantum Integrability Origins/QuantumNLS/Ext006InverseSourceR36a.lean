import QuantumNLS.Ext006AdjointTransportR36a

/-! The inverse source has exactly the same Hilbert-Schmidt beta mass.
All inverse blocks come from the actual real symplectic inverse. A normalized
smooth inverse-source vacuum is therefore constructed from the ORIGINAL HS
assumption. No inverse implementer or target cyclicity is assumed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped InnerProductSpace
namespace QuantumNLS.Ext006InverseSourceR36a
open Ext006Blocks Ext006SymplecticKernel Ext006KernelHilbertSchmidt
open Ext006SmoothOperatorsR34a Ext006SourceCCRR34a Ext006CreationGramR34a
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
attribute [local instance] InnerProductSpace.complexToReal

omit [CompleteSpace E] in
lemma inverse_symplectic (S : E ≃L[ℝ] E) (hS : Symplectic S.toContinuousLinearMap) :
    Symplectic S.symm.toContinuousLinearMap := by
  intro x y
  have h := hS (S.symm x) (S.symm y)
  simpa only [ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.apply_symm_apply] using h.symm

omit [CompleteSpace E] in
lemma conjugation_inner (b : HilbertBasis ι ℂ E) (x y : E) :
    inner ℂ (conjugation b x) (conjugation b y) = star (inner ℂ x y) := by
  calc
    _ = inner ℂ (star (b.repr x)) (star (b.repr y)) := by
      rw [← b.repr.inner_map_map]
      simp only [conjugation_apply,LinearIsometryEquiv.apply_symm_apply]
    _ = star (inner ℂ (b.repr x) (b.repr y)) := by
      simp only [lp.inner_eq_tsum,Complex.star_def,Complex.conj_tsum]
      apply tsum_congr
      intro i
      simp [lp.star_apply,RCLike.inner_apply]
    _ = _ := by rw [LinearIsometryEquiv.inner_map_map]

lemma conjugation_adjoint (b : HilbertBasis ι ℂ E) :
    (conjugation b).adjoint=conjugation b := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  have h := conjugation_inner b x (conjugation b y)
  rw [conjugation_sq] at h
  simpa only [real_inner_eq_re_inner,RCLike.re_to_complex,Complex.star_def,Complex.conj_re] using
    congrArg Complex.re h

lemma restrict_adjoint (T : E →L[ℂ] E) :
    (T.restrictScalars ℝ).adjoint=T.adjoint.restrictScalars ℝ := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  change inner ℝ (T.adjoint x) y=inner ℝ x (T y)
  simp only [real_inner_eq_re_inner,ContinuousLinearMap.adjoint_inner_left]

omit [CompleteSpace E] in
lemma beta_real (b : HilbertBasis ι ℂ E) (S : E ≃L[ℝ] E) :
    (beta b S).restrictScalars ℝ =
      antilinearPart S.toContinuousLinearMap ∘L conjugation b := by
  ext x
  rfl

/-- Exact inverse beta action, including transpose/conjugation and minus sign. -/
theorem inverse_beta_apply (b : HilbertBasis ι ℂ E) (S : E ≃L[ℝ] E)
    (hS : Symplectic S.toContinuousLinearMap) (x : E) :
    beta b S.symm x = -conjugation b ((beta b S).adjoint (conjugation b x)) := by
  have had : (beta b S).adjoint.restrictScalars ℝ =
      conjugation b ∘L (antilinearPart S.toContinuousLinearMap).adjoint := by
    rw [← restrict_adjoint,beta_real,ContinuousLinearMap.adjoint_comp,conjugation_adjoint]
  have he := congrArg (fun T : E →L[ℝ] E => T (conjugation b x)) had
  change (beta b S).adjoint (conjugation b x) =
    conjugation b ((antilinearPart S.toContinuousLinearMap).adjoint (conjugation b x)) at he
  change antilinearPart S.symm.toContinuousLinearMap (conjugation b x) = _
  rw [antilinearPart_inverse S hS,neg_apply,he,conjugation_sq]

/-- Exact equality, not merely preservation of finiteness or an added premise. -/
theorem inverse_beta_hsSq (b : HilbertBasis ι ℂ E) (S : E ≃L[ℝ] E)
    (hS : Symplectic S.toContinuousLinearMap) :
    TraceClass.hsSq b (beta b S.symm)=TraceClass.hsSq b (beta b S) := by
  calc
    TraceClass.hsSq b (beta b S.symm) = TraceClass.hsSq b (beta b S).adjoint := by
      simp only [TraceClass.hsSq,inverse_beta_apply b S hS,conjugation_basis,
        norm_neg,conjugation_norm]
    _ = _ := (TraceClass.hsSq_eq_hsSq_adjoint b b (beta b S)).symm

local instance physicalReal (L : ℝ) [Fact (0 < L)] : NormedSpace ℝ (PhysicalTensor.L2T L) :=
  (InnerProductSpace.complexToReal : InnerProductSpace ℝ (PhysicalTensor.L2T L)).toNormedSpace

/-- An actual normalized smooth inverse-source vacuum follows from the
original physical HS assumption; its equation uses the literal inverse map. -/
theorem inverse_source_vacuum {L : ℝ} [Fact (0 < L)]
    (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Symplectic S.toContinuousLinearMap)
    (hβ : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) ≠ ⊤) :
    ∃ v : D, ‖v.1‖=1 ∧ ∀ f,sourceAnn (physicalBasis L) S.symm f v=0 := by
  exact source_vacuum S.symm (inverse_symplectic S hS)
    (fun h => hβ ((inverse_beta_hsSq (physicalBasis L) S hS).symm.trans h))

end QuantumNLS.Ext006InverseSourceR36a

#print axioms QuantumNLS.Ext006InverseSourceR36a.inverse_symplectic
#print axioms QuantumNLS.Ext006InverseSourceR36a.inverse_beta_apply
#print axioms QuantumNLS.Ext006InverseSourceR36a.inverse_beta_hsSq
#print axioms QuantumNLS.Ext006InverseSourceR36a.inverse_source_vacuum

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006InverseSourceR36a." then
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
  Lean.logInfo m!"Round36a aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
