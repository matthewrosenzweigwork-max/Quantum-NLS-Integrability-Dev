import QuantumNLS.Ext006ClosedFieldGraphsR36a

/-! The adjoint of the whole-domain source embedding is a left inverse.
Its pullback of EVERY smooth source vector has both ordinary weak field
actions, with images given by the pulled-back actual source fields. This
proves graph-domain membership, not smoothness of the pullback or injectivity. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped InnerProductSpace
namespace QuantumNLS.Ext006AdjointTransportR36a
open Occupation Ext006VacuumRecurrence Ext006BogoliubovAlg
open Ext006SmoothOperatorsR34a Ext006SourceCCRR34a Ext006CreationGramR34a
open Ext006CyclicIsometryR34a Ext006IdentityCyclicR35a Ext006FockEmbeddingR35a
open Ext006CoreTransportR35a Ext006ClosedFieldGraphsR36a Ext006KernelHilbertSchmidt
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
attribute [local instance] InnerProductSpace.complexToReal

/-- Constructed bounded pullback on all completed occupation Fock. -/
def pullback (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (v : D) (hn : ‖v.1‖=1) (hv : ∀ f,sourceAnn b S f v=0) : Fock →L[ℂ] Fock :=
  (embedding b S hS v hn hv).toContinuousLinearMap.adjoint

lemma pullback_inner (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (v : D) (hn : ‖v.1‖=1) (hv : ∀ f,sourceAnn b S f v=0) (x y : Fock) :
    inner ℂ x (pullback b S hS v hn hv y)=inner ℂ (embedding b S hS v hn hv x) y :=
  ContinuousLinearMap.adjoint_inner_right _ x y

/-- A true left inverse, with no target density or surjectivity assumption. -/
theorem pullback_embedding (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (v : D) (hn : ‖v.1‖=1) (hv : ∀ f,sourceAnn b S f v=0) (x : Fock) :
    pullback b S hS v hn hv (embedding b S hS v hn hv x)=x := by
  apply ext_inner_left ℂ
  intro y
  rw [pullback_inner,LinearIsometry.inner_map_map]

/-- The kernel is exactly the still-unexcluded orthogonal complement of the
source cyclic space. This identifies precisely the remaining inverse defect. -/
theorem pullback_kernel (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (v : D) (hn : ‖v.1‖=1) (hv : ∀ f,sourceAnn b S f v=0) :
    (pullback b S hS v hn hv).ker=(cyclic b S v)ᗮ := by
  rw [← embedding_range b S hS v hn hv]
  exact (ContinuousLinearMap.orthogonal_range
    (embedding b S hS v hn hv).toContinuousLinearMap).symm

/-- Every transported occupation ket is constructed in the actual smooth
domain; both field actions follow from the finite polynomial witness. -/
lemma ket_transport (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (v : D) (hn : ‖v.1‖=1) (hv : ∀ f,sourceAnn b S f v=0) (m : Occ) :
    ∃ d : D, embedding b S hS v hn hv (ketD m).1=d.1 ∧ ∀ f : E,
      (embedding b S hS v hn hv (sourceAnn b identitySource f (ketD m)).1=
        (sourceAnn b S f d).1) ∧
      (embedding b S hS v hn hv (sourceCre b identitySource f (ketD m)).1=
        (sourceCre b S f d).1) := by
  obtain ⟨c,hc⟩ := ket_in_range b m
  have hd : evalDomain b identitySource (ketD 0) c=ketD m := by
    apply Subtype.ext
    exact (evalDomain_val b identitySource (ketD 0) c).trans hc
  refine ⟨evalDomain b S v c,?_,fun f => ⟨?_,?_⟩⟩
  · rw [← hd]
    exact embedding_domain b S hS v hn hv c
  · rw [← hd]
    exact core_ann b S hS v hn hv f c
  · rw [← hd]
    exact core_cre b S hS v hn hv f c

/-- No approximation premise: for every smooth target vector, the pulled-back
source annihilator is its ordinary weak annihilation image. -/
theorem pullback_annGraph (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (v : D) (hn : ‖v.1‖=1) (hv : ∀ f,sourceAnn b S f v=0) (f : E) (w : D) :
    AnnGraph b identitySource f (pullback b S hS v hn hv w.1)
      (pullback b S hS v hn hv (sourceAnn b S f w).1) := by
  intro m
  obtain ⟨d,hd,hfields⟩ := ket_transport b S hS v hn hv m
  rw [pullback_inner,hd,source_adjoint,← (hfields f).2,← pullback_inner]

/-- The second field relation holds for the same whole smooth target domain. -/
theorem pullback_creGraph (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (v : D) (hn : ‖v.1‖=1) (hv : ∀ f,sourceAnn b S f v=0) (f : E) (w : D) :
    CreGraph b identitySource f (pullback b S hS v hn hv w.1)
      (pullback b S hS v hn hv (sourceCre b S f w).1) := by
  intro m
  obtain ⟨d,hd,hfields⟩ := ket_transport b S hS v hn hv m
  rw [pullback_inner,hd,source_adjoint_rev,← (hfields f).1,← pullback_inner]

/-- The result is instantiated from precisely the original physical source
symplectic and HS assumptions. Neither an implementer nor a graph identity
is provided as an additional input. -/
theorem source_pullback_graphs {L : ℝ} [Fact (0 < L)]
    (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (hβ : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) ≠ ⊤) :
    ∃ v : D, ∃ hn : ‖v.1‖=1, ∃ hv : ∀ f,sourceAnn (physicalBasis L) S f v=0,
      ∃ T : Fock →L[ℂ] Fock,
        (∀ x, T (embedding (physicalBasis L) S hS v hn hv x)=x) ∧
        ∀ (w : D) (f : PhysicalTensor.L2T L),
          AnnGraph (physicalBasis L) identitySource f (T w.1)
            (T (sourceAnn (physicalBasis L) S f w).1) ∧
          CreGraph (physicalBasis L) identitySource f (T w.1)
            (T (sourceCre (physicalBasis L) S f w).1) := by
  obtain ⟨v,hn,hv⟩ := source_vacuum S hS hβ
  exact ⟨v,hn,hv,pullback (physicalBasis L) S hS v hn hv,
    pullback_embedding (physicalBasis L) S hS v hn hv,
    fun w f => ⟨pullback_annGraph (physicalBasis L) S hS v hn hv f w,
      pullback_creGraph (physicalBasis L) S hS v hn hv f w⟩⟩

end QuantumNLS.Ext006AdjointTransportR36a

#print axioms QuantumNLS.Ext006AdjointTransportR36a.pullback_embedding
#print axioms QuantumNLS.Ext006AdjointTransportR36a.pullback_kernel
#print axioms QuantumNLS.Ext006AdjointTransportR36a.ket_transport
#print axioms QuantumNLS.Ext006AdjointTransportR36a.pullback_annGraph
#print axioms QuantumNLS.Ext006AdjointTransportR36a.pullback_creGraph
#print axioms QuantumNLS.Ext006AdjointTransportR36a.source_pullback_graphs

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006AdjointTransportR36a." then
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
