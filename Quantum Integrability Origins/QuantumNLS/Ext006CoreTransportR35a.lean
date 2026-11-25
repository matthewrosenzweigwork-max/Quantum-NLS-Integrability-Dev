import QuantumNLS.Ext006SourceVacuumUniqueR35a

/-! Both field actions on actual finite creator polynomials, with all smooth
domains constructed. These are core intertwining relations for a full-domain
isometry, not the frozen physical HeisAnn/HeisCre predicates for a UNITARY. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped InnerProductSpace
namespace QuantumNLS.Ext006CoreTransportR35a
open Occupation Ext006VacuumRecurrence Ext006BogoliubovAlg
open Ext006SmoothOperatorsR34a Ext006SourceCCRR34a Ext006CreationGramR34a
open Ext006CyclicIsometryR34a Ext006IdentityCyclicR35a Ext006FockEmbeddingR35a
open Ext006SourceVacuumUniqueR35a Ext006KernelHilbertSchmidt
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
attribute [local instance] InnerProductSpace.complexToReal

/-- Finite source polynomials valued in their proved invariant domain. -/
def evalDomain (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E) (v : D) :
    (List E →₀ ℂ) →ₗ[ℂ] D := Finsupp.linearCombination ℂ (fun fs => word b S fs v)

omit [CompleteSpace E] in
lemma evalDomain_val (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E) (v : D)
    (c : List E →₀ ℂ) : (evalDomain b S v c).1=eval b S v c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add,Submodule.coe_add,hc,hd]
  | single fs z => simp [evalDomain,eval]

/-- Formal creator action on polynomials. -/
def prepend (f : E) : (List E →₀ ℂ) →ₗ[ℂ] (List E →₀ ℂ) :=
  Finsupp.linearCombination ℂ (fun fs => Finsupp.single (f::fs) 1)

/-- Formal annihilator action on a word, retaining all contractions. -/
def lower (f : E) (fs : List E) : List E →₀ ℂ :=
  ((derivative f fs).map (fun z => Finsupp.single z.2 z.1)).sum

def contract (f : E) : (List E →₀ ℂ) →ₗ[ℂ] (List E →₀ ℂ) :=
  Finsupp.linearCombination ℂ (lower f)

omit [CompleteSpace E] in
lemma evalDomain_prefix (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E) (v : D)
    (f : E) (c : List E →₀ ℂ) :
    evalDomain b S v (prepend f c)=sourceCre b S f (evalDomain b S v c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add,hc,hd]
  | single fs z => simp [prepend,evalDomain,word]

omit [CompleteSpace E] in
lemma evalDomain_list (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E) (v : D)
    (zs : List (ℂ × List E)) :
    evalDomain b S v ((zs.map (fun z => Finsupp.single z.2 z.1)).sum)=wordSum b S zs v := by
  induction zs with
  | nil => simp [wordSum]
  | cons z zs ih =>
    rw [List.map_cons,List.sum_cons,map_add,ih,wordSum_cons]
    congr 1
    simp only [evalDomain,Finsupp.linearCombination_single]

lemma evalDomain_contract (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (v : D) (hv : ∀ f,sourceAnn b S f v=0) (f : E) (c : List E →₀ ℂ) :
    evalDomain b S v (contract f c)=sourceAnn b S f (evalDomain b S v c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add,hc,hd]
  | single fs z =>
    simp only [contract,Finsupp.linearCombination_single,map_smul]
    rw [lower,evalDomain_list]
    simp only [evalDomain,Finsupp.linearCombination_single,map_smul,ann_word b S hS v hv]

lemma embedding_domain (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (v : D) (hn : ‖v.1‖=1) (hv : ∀ f,sourceAnn b S f v=0)
    (c : List E →₀ ℂ) :
    embedding b S hS v hn hv (evalDomain b identitySource (ketD 0) c).1 =
      (evalDomain b S v c).1 := by
  rw [evalDomain_val,evalDomain_val,embedding_eval]

/-- Actual creator intertwining on every finite polynomial, for arbitrary
one-particle smearings and the exact original source P,Q blocks. -/
lemma core_cre (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (v : D) (hn : ‖v.1‖=1) (hv : ∀ f,sourceAnn b S f v=0)
    (f : E) (c : List E →₀ ℂ) :
    embedding b S hS v hn hv
      (sourceCre b identitySource f (evalDomain b identitySource (ketD 0) c)).1 =
        (sourceCre b S f (evalDomain b S v c)).1 := by
  rw [← evalDomain_prefix,← evalDomain_prefix,embedding_domain]

/-- Actual annihilator intertwining on the same common finite polynomial
core. Domain membership is supplied by evalDomain, rather than assumed. -/
lemma core_ann (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (v : D) (hn : ‖v.1‖=1) (hv : ∀ f,sourceAnn b S f v=0)
    (f : E) (c : List E →₀ ℂ) :
    embedding b S hS v hn hv
      (sourceAnn b identitySource f (evalDomain b identitySource (ketD 0) c)).1 =
        (sourceAnn b S f (evalDomain b S v c)).1 := by
  rw [← evalDomain_contract b identitySource identity_symplectic (ketD 0) (identity_vacuum b),
    ← evalDomain_contract b S hS v hv,embedding_domain]

omit [CompleteSpace E] in
/-- The algebraic identity-source polynomial core is dense in all Fock. -/
lemma identity_eval_dense (b : HilbertBasis ℤ ℂ E) :
    DenseRange (eval b identitySource (ketD 0)) := by
  intro x
  have hx : x ∈ cyclic b identitySource (ketD 0) := by rw [identity_cyclic_eq_top]; trivial
  exact hx

/-- The isometry is determined on the whole Fock space by its creator-word
action. This uses the proved density, with no source cyclicity premise. -/
theorem embedding_unique (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (v : D) (hn : ‖v.1‖=1) (hv : ∀ f,sourceAnn b S f v=0)
    (U : Fock →ₗᵢ[ℂ] Fock)
    (hU : ∀ c, U (eval b identitySource (ketD 0) c)=eval b S v c) :
    U=embedding b S hS v hn hv := by
  apply DFunLike.ext'
  exact (identity_eval_dense b).equalizer U.continuous (embedding b S hS v hn hv).continuous
    (funext fun c => (hU c).trans (embedding_eval b S hS v hn hv c).symm)

/-- Changing the normalized source vacuum changes the constructed entire
isometry by precisely that phase. This does not assert a unitary exists. -/
theorem embedding_unique_phase (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (v w : D) (hvn : ‖v.1‖=1) (hwn : ‖w.1‖=1)
    (hv : ∀ f,sourceAnn b S f v=0) (hw : ∀ f,sourceAnn b S f w=0) :
    ∃ z : ℂ, ‖z‖=1 ∧ ∀ x : Fock,
      embedding b S hS w hwn hw x=z • embedding b S hS v hvn hv x := by
  obtain ⟨z,hz,hwv⟩ := source_vacuum_unique_phase b S hS v w hvn hwn hv hw
  have hword : ∀ fs : List E, word b S fs w=z • word b S fs v := by
    intro fs
    induction fs with
    | nil => exact hwv
    | cons f fs ih => simp only [word,ih,map_smul]
  have heval : ∀ c : List E →₀ ℂ, eval b S w c=z • eval b S v c := by
    intro c
    simp only [eval,Finsupp.linearCombination_apply,Finsupp.sum,hword,Submodule.coe_smul,
      Finset.smul_sum,smul_smul]
    apply Finset.sum_congr rfl
    intro fs _
    rw [mul_comm]
  refine ⟨z,hz,?_⟩
  have he := (identity_eval_dense b).equalizer (embedding b S hS w hwn hw).continuous
    ((continuous_const_smul z).comp (embedding b S hS v hvn hv).continuous)
    (funext fun c => by
      simp only [Function.comp_apply]
      rw [embedding_eval,embedding_eval,heval])
  exact fun x => congrFun he x

section Physical
variable {L : ℝ} [Fact (0 < L)]

/-- Both finite-polynomial field relations follow from precisely the original
physical source symplectic and HS data; the vacuum is constructed internally. -/
theorem source_core_relations
    (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (hβ : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) ≠ ⊤) :
    ∃ v : D, ∃ hn : ‖v.1‖=1, ∃ hv : ∀ f,sourceAnn (physicalBasis L) S f v=0,
      ∀ (f : PhysicalTensor.L2T L) (c : List (PhysicalTensor.L2T L) →₀ ℂ),
        embedding (physicalBasis L) S hS v hn hv
          (sourceAnn (physicalBasis L) identitySource f
            (evalDomain (physicalBasis L) identitySource (ketD 0) c)).1 =
          (sourceAnn (physicalBasis L) S f (evalDomain (physicalBasis L) S v c)).1 ∧
        embedding (physicalBasis L) S hS v hn hv
          (sourceCre (physicalBasis L) identitySource f
            (evalDomain (physicalBasis L) identitySource (ketD 0) c)).1 =
          (sourceCre (physicalBasis L) S f (evalDomain (physicalBasis L) S v c)).1 := by
  obtain ⟨v,hn,hv⟩ := source_vacuum S hS hβ
  exact ⟨v,hn,hv,fun f c => ⟨core_ann (physicalBasis L) S hS v hn hv f c,
    core_cre (physicalBasis L) S hS v hn hv f c⟩⟩

end Physical
end QuantumNLS.Ext006CoreTransportR35a

#print axioms QuantumNLS.Ext006CoreTransportR35a.evalDomain_contract
#print axioms QuantumNLS.Ext006CoreTransportR35a.core_cre
#print axioms QuantumNLS.Ext006CoreTransportR35a.core_ann
#print axioms QuantumNLS.Ext006CoreTransportR35a.embedding_unique
#print axioms QuantumNLS.Ext006CoreTransportR35a.source_core_relations
#print axioms QuantumNLS.Ext006CoreTransportR35a.embedding_unique_phase

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006CoreTransportR35a." then
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
  Lean.logInfo m!"Round35a aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
