import QuantumNLS.Ext006IdentityCyclicR35a

/-! A source-HS isometry defined on the WHOLE Fock space. Its closed range
is exactly the source cyclic space; equality of that range with the whole
target space is still unproved. In particular this is not a UNITARY. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped InnerProductSpace
namespace QuantumNLS.Ext006FockEmbeddingR35a
open Occupation Ext006VacuumRecurrence Ext006BogoliubovAlg
open Ext006SmoothOperatorsR34a Ext006SourceCCRR34a Ext006CreationGramR34a
open Ext006CyclicIsometryR34a Ext006IdentityCyclicR35a Ext006KernelHilbertSchmidt
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
attribute [local instance] InnerProductSpace.complexToReal

omit [CompleteSpace E] in
lemma identity_symplectic : Ext006SymplecticKernel.Symplectic
    (identitySource (E := E)).toContinuousLinearMap := fun _ _ => rfl

/-- Onto the closed source cyclic subspace, with the whole Fock as domain. -/
def ontoCyclic (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (v : D) (hn : ‖v.1‖=1) (hv : ∀ f,sourceAnn b S f v=0) :
    Fock ≃ₗᵢ[ℂ] cyclic b S v :=
  (LinearIsometryEquiv.ofTop Fock _ (identity_cyclic_eq_top b)).symm.trans
    (cyclicEquiv b identitySource S identity_symplectic hS (ketD 0) v
      vacuum_norm hn (identity_vacuum b) hv)

lemma ontoCyclic_eval (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (v : D) (hn : ‖v.1‖=1) (hv : ∀ f,sourceAnn b S f v=0)
    (c : List E →₀ ℂ) :
    ontoCyclic b S hS v hn hv (eval b identitySource (ketD 0) c)=intoCyclic b S v c := by
  have hi : (LinearIsometryEquiv.ofTop Fock _ (identity_cyclic_eq_top b)).symm
      (eval b identitySource (ketD 0) c) = intoCyclic b identitySource (ketD 0) c := by
    apply Subtype.ext
    rfl
  change cyclicEquiv b identitySource S identity_symplectic hS (ketD 0) v
    vacuum_norm hn (identity_vacuum b) hv ((LinearIsometryEquiv.ofTop Fock _ (identity_cyclic_eq_top b)).symm
      (eval b identitySource (ketD 0) c)) = _
  rw [hi]
  exact cyclicEquiv_eval b identitySource S identity_symplectic hS (ketD 0) v
    vacuum_norm hn (identity_vacuum b) hv c

/-- The whole-domain isometry into the existing target Fock carrier. -/
def embedding (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (v : D) (hn : ‖v.1‖=1) (hv : ∀ f,sourceAnn b S f v=0) : Fock →ₗᵢ[ℂ] Fock :=
  (cyclic b S v).subtypeₗᵢ.comp (ontoCyclic b S hS v hn hv).toLinearIsometry

lemma embedding_eval (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (v : D) (hn : ‖v.1‖=1) (hv : ∀ f,sourceAnn b S f v=0)
    (c : List E →₀ ℂ) :
    embedding b S hS v hn hv (eval b identitySource (ketD 0) c)=eval b S v c :=
  congrArg Subtype.val (ontoCyclic_eval b S hS v hn hv c)

/-- The range is identified exactly. No surjectivity premise is hidden. -/
theorem embedding_range (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (v : D) (hn : ‖v.1‖=1) (hv : ∀ f,sourceAnn b S f v=0) :
    (embedding b S hS v hn hv).toLinearMap.range = cyclic b S v := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    exact (ontoCyclic b S hS v hn hv y).2
  · intro hx
    obtain ⟨y,hy⟩ := (ontoCyclic b S hS v hn hv).surjective ⟨x,hx⟩
    exact ⟨y,congrArg Subtype.val hy⟩

lemma embedding_word (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (v : D) (hn : ‖v.1‖=1) (hv : ∀ f,sourceAnn b S f v=0) (fs : List E) :
    embedding b S hS v hn hv (word b identitySource fs (ketD 0)).1 = (word b S fs v).1 := by
  simpa only [eval,Finsupp.linearCombination_single,one_smul] using
    embedding_eval b S hS v hn hv (Finsupp.single fs 1)

lemma embedding_vacuum (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (v : D) (hn : ‖v.1‖=1) (hv : ∀ f,sourceAnn b S f v=0) :
    embedding b S hS v hn hv vacuum = v.1 := embedding_word b S hS v hn hv []

section Physical
variable {L : ℝ} [Fact (0 < L)]

/-- The isometry transported to the actual physical Fock. -/
def physicalEmbedding (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (v : D) (hn : ‖v.1‖=1) (hv : ∀ f,sourceAnn (physicalBasis L) S f v=0) :
    Ext025B3PhysicalSectors.Fock L →ₗᵢ[ℂ] Ext025B3PhysicalSectors.Fock L :=
  Ext006PhysFockCoord.Phi.symm.toLinearIsometry.comp
    ((embedding (physicalBasis L) S hS v hn hv).comp Ext006PhysFockCoord.Phi.toLinearIsometry)

/-- A full-domain physical isometry is constructed from the original
symplectic and HS assumptions. Target surjectivity remains an obligation. -/
theorem source_full_domain_isometry
    (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (hβ : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) ≠ ⊤) :
    ∃ v : D, ‖v.1‖=1 ∧ (∀ f,sourceAnn (physicalBasis L) S f v=0) ∧
      ∃ U : Ext025B3PhysicalSectors.Fock L →ₗᵢ[ℂ] Ext025B3PhysicalSectors.Fock L,
        ∀ fs : List (PhysicalTensor.L2T L),
          U (Ext006PhysFockCoord.Phi.symm (word (physicalBasis L) identitySource fs (ketD 0)).1)=
            Ext006PhysFockCoord.Phi.symm (word (physicalBasis L) S fs v).1 := by
  obtain ⟨v,hn,hv⟩ := source_vacuum S hS hβ
  refine ⟨v,hn,hv,physicalEmbedding S hS v hn hv,fun fs => ?_⟩
  change Ext006PhysFockCoord.Phi.symm
    (embedding (physicalBasis L) S hS v hn hv
      (Ext006PhysFockCoord.Phi (Ext006PhysFockCoord.Phi.symm _))) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact congrArg (Ext006PhysFockCoord.Phi (L := L)).symm
    (embedding_word (physicalBasis L) S hS v hn hv fs)

end Physical
end QuantumNLS.Ext006FockEmbeddingR35a

#print axioms QuantumNLS.Ext006FockEmbeddingR35a.ontoCyclic
#print axioms QuantumNLS.Ext006FockEmbeddingR35a.embedding_eval
#print axioms QuantumNLS.Ext006FockEmbeddingR35a.embedding_range
#print axioms QuantumNLS.Ext006FockEmbeddingR35a.embedding_vacuum
#print axioms QuantumNLS.Ext006FockEmbeddingR35a.source_full_domain_isometry

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006FockEmbeddingR35a." then
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
