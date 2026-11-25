import QuantumNLS.Ext006FieldOrientationR41a

/-! Actual smeared fields on the constructed common smooth domain, and
all polynomial iterates under the source isometry. This is a strong core
calculation; it does NOT identify a self-adjoint closure or exponentiate it. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped InnerProductSpace
namespace QuantumNLS.Ext006StrongFieldR41a
open Occupation Ext006BogoliubovAlg Ext006VacuumRecurrence Ext006QuasifreeWeak
open Ext006SmoothOperatorsR34a Ext006SourceCCRR34a Ext006CreationGramR34a
open Ext006IdentityCyclicR35a Ext006CoreTransportR35a Ext006FockEmbeddingR35a
open Ext006KernelHilbertSchmidt

/-- The actual unbounded smeared field, as an endomorphism of its common
invariant smooth domain. No boundedness of this endomorphism is asserted. -/
def field (h : H) : Module.End ℂ D := A h+C h

lemma A_add_smear (h k : H) : A (h+k)=A h+A k := by
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  apply lp.ext
  funext m
  change inner ℂ (h+k) (xvec w.1 m)=inner ℂ h (xvec w.1 m)+inner ℂ k (xvec w.1 m)
  exact inner_add_left _ _ _

lemma C_add_smear (h k : H) : C (h+k)=C h+C k := by
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  apply lp.ext
  funext m
  change (∑ a ∈ m.support, (h a+k a)*Ext006ModeDomainR33a.creCoeff a w.1 m)=
    (∑ a ∈ m.support, h a*Ext006ModeDomainR33a.creCoeff a w.1 m)+
    (∑ a ∈ m.support, k a*Ext006ModeDomainR33a.creCoeff a w.1 m)
  simp only [add_mul,Finset.sum_add_distrib]

lemma field_add_smear (h k : H) : field (h+k)=field h+field k := by
  rw [field,A_add_smear,C_add_smear,field,field]
  module

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
attribute [local instance] InnerProductSpace.complexToReal

omit [CompleteSpace E] in
lemma p_add_r (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E) (f : E) :
    p b S f+r b S f=b.repr (S f) := by
  change b.repr (Ext006Blocks.complexPart S.toContinuousLinearMap f)+
    b.repr (conjugation b (conjugation b
      (Ext006Blocks.antilinearPart S.toContinuousLinearMap f)))=_
  rw [conjugation_sq,← map_add]
  exact congrArg b.repr (congrArg (fun T : E →L[ℝ] E => T f)
    (Ext006Blocks.parts_sum S.toContinuousLinearMap))

omit [CompleteSpace E] in
/-- Source annihilator plus creator is exactly the actual field at S f.
This fixes both the sign and the direction at the strong operator level. -/
theorem source_field (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E) (f : E) :
    sourceAnn b S f+sourceCre b S f=field (b.repr (S f)) := by
  rw [← p_add_r b S f,field,A_add_smear,C_add_smear,sourceAnn,sourceCre,B,Bstar]
  module

/-- Strong field covariance on all finite identity-source creator polynomials,
with the target domain constructed by evalDomain. -/
theorem core_field (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (v : D) (hn : ‖v.1‖=1) (hv : ∀ f,sourceAnn b S f v=0)
    (f : E) (c : List E →₀ ℂ) :
    embedding b S hS v hn hv
      (field (b.repr f) (evalDomain b identitySource (ketD 0) c)).1 =
        (field (b.repr (S f)) (evalDomain b S v c)).1 := by
  have hi : field (b.repr f)=sourceAnn b identitySource f+sourceCre b identitySource f :=
    (source_field b identitySource f).symm
  rw [hi,← source_field b S f]
  simp only [LinearMap.add_apply,Submodule.coe_add,map_add]
  rw [core_ann b S hS v hn hv,core_cre b S hS v hn hv]

/-- A concrete algebraic field action on creator polynomials. -/
def polynomialField (f : E) : (List E →₀ ℂ) →ₗ[ℂ] (List E →₀ ℂ) :=
  contract f+prepend f

lemma evalDomain_field (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (v : D) (hv : ∀ f,sourceAnn b S f v=0) (f : E) (c : List E →₀ ℂ) :
    evalDomain b S v (polynomialField f c)=
      field (b.repr (S f)) (evalDomain b S v c) := by
  rw [polynomialField,LinearMap.add_apply,map_add,evalDomain_contract b S hS v hv,
    evalDomain_prefix,← LinearMap.add_apply,source_field]

lemma evalDomain_field_power (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (v : D) (hv : ∀ f,sourceAnn b S f v=0) (f : E) (c : List E →₀ ℂ) (n : ℕ) :
    evalDomain b S v (((polynomialField f)^n) c)=
      ((field (b.repr (S f)))^n) (evalDomain b S v c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ',pow_succ']
    change evalDomain b S v (polynomialField f (((polynomialField f)^n) c))=_
    rw [evalDomain_field b S hS v hv,ih]
    rfl

/-- Every power intertwines on the actual invariant polynomial core.
No analytic-vector, series convergence or functional-calculus premise is used. -/
theorem core_field_power (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (v : D) (hn : ‖v.1‖=1) (hv : ∀ f,sourceAnn b S f v=0)
    (f : E) (c : List E →₀ ℂ) (n : ℕ) :
    embedding b S hS v hn hv
      (((field (b.repr f))^n) (evalDomain b identitySource (ketD 0) c)).1 =
        (((field (b.repr (S f)))^n) (evalDomain b S v c)).1 := by
  have hi := evalDomain_field_power b identitySource identity_symplectic (ketD 0)
    (identity_vacuum b) f c n
  change evalDomain b identitySource (ketD 0) (((polynomialField f)^n) c)=
    ((field (b.repr f))^n) (evalDomain b identitySource (ketD 0) c) at hi
  rw [← hi,embedding_domain,evalDomain_field_power b S hS v hv]

/-- All target power norms are the proved source norms. This is useful for a
future analytic-vector construction, but supplies no unproved norm bound. -/
theorem core_field_power_norm (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (v : D) (hn : ‖v.1‖=1) (hv : ∀ f,sourceAnn b S f v=0)
    (f : E) (c : List E →₀ ℂ) (n : ℕ) :
    ‖(((field (b.repr (S f)))^n) (evalDomain b S v c)).1‖ =
      ‖(((field (b.repr f))^n) (evalDomain b identitySource (ketD 0) c)).1‖ := by
  rw [← core_field_power b S hS v hn hv f c n]
  exact (embedding b S hS v hn hv).norm_map _

end QuantumNLS.Ext006StrongFieldR41a
#print axioms QuantumNLS.Ext006StrongFieldR41a.source_field
#print axioms QuantumNLS.Ext006StrongFieldR41a.core_field_power
#print axioms QuantumNLS.Ext006StrongFieldR41a.core_field_power_norm

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006StrongFieldR41a." then
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
