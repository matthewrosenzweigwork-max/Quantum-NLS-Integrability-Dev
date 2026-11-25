import QuantumNLS.Ext006InverseSourceR36a

/-! Inverse-source weak graph transport for the adjoint embedding. The
inverse block orientation is proved through real-linear field sums, rather
than inferred from a supplied inverse implementation identity. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped InnerProductSpace
namespace QuantumNLS.Ext006InverseGraphsR36a
open Occupation Ext006VacuumRecurrence Ext006BogoliubovAlg Ext006QuasifreeWeak
open Ext006ModeDomainR33a Ext006SmearedDomainR33a
open Ext006SmoothOperatorsR34a Ext006SourceCCRR34a Ext006CreationGramR34a
open Ext006CyclicIsometryR34a Ext006IdentityCyclicR35a Ext006FockEmbeddingR35a
open Ext006CoreTransportR35a Ext006ClosedFieldGraphsR36a Ext006AdjointTransportR36a
open Ext006KernelHilbertSchmidt
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
attribute [local instance] InnerProductSpace.complexToReal

lemma A_add (h k : H) : A (h+k)=A h+A k := by
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  apply lp.ext
  funext m
  exact inner_add_left h k (xvec w.1 m)

lemma C_add (h k : H) : C (h+k)=C h+C k := by
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  apply lp.ext
  funext m
  change (∑ a ∈ m.support, (h a+k a)*creCoeff a w.1 m) = _
  simp only [add_mul,Finset.sum_add_distrib]
  rfl

lemma A_smul (z : ℂ) (h : H) : A (z • h)=star z • A h := by
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  apply lp.ext
  funext m
  change inner ℂ (z • h) (xvec w.1 m)=star z * inner ℂ h (xvec w.1 m)
  exact inner_smul_left _ _ _

lemma C_smul (z : ℂ) (h : H) : C (z • h)=z • C h := by
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  apply lp.ext
  funext m
  change (∑ a ∈ m.support, (z*h a)*creCoeff a w.1 m) = z*(∑ a ∈ m.support, h a*creCoeff a w.1 m)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- The ordinary real-linear sum of annihilation and creation. -/
def field (b : HilbertBasis ℤ ℂ E) (f : E) : Module.End ℂ D :=
  A (b.repr f)+C (b.repr f)

lemma field_add (b : HilbertBasis ℤ ℂ E) (f g : E) : field b (f+g)=field b f+field b g := by
  simp only [field,map_add,A_add,C_add]
  abel

lemma field_identity (b : HilbertBasis ℤ ℂ E) (f : E) :
    field b f=sourceAnn b identitySource f+sourceCre b identitySource f := by
  rw [sourceAnn_identity,sourceCre_identity]
  rfl

/-- Exact real-linear source action, for the original P and C Q rows. -/
lemma source_field (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E) (f : E) :
    sourceAnn b S f+sourceCre b S f=field b (S f) := by
  rw [source_block_action b S f,field_add]
  change A (p b S f)+C (r b S f)+(C (p b S f)+A (r b S f)) =
    A (p b S f)+C (p b S f)+(A (r b S f)+C (r b S f))
  abel

lemma p_I (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E) (f : E) :
    p b S (Complex.I • f)=Complex.I • p b S f := by
  simp only [p,map_smul]

lemma r_I (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E) (f : E) :
    r b S (Complex.I • f)=(-Complex.I) • r b S f := by
  have hr (g : E) : r b S g=b.repr (Ext006Blocks.antilinearPart S.toContinuousLinearMap g) := by
    change b.repr (conjugation b (conjugation b _))=_
    rw [conjugation_sq]
    rfl
  rw [hr,hr]
  change b.repr (Ext006Blocks.antilinearPart S.toContinuousLinearMap (Ext006Blocks.J f))=_
  rw [Ext006Blocks.antilinearPart_anticommutes_J,Ext006Blocks.J_apply,map_neg,map_smul]
  simp only [neg_smul]

lemma sourceAnn_I (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E) (f : E) :
    sourceAnn b S (Complex.I • f)=(-Complex.I) • sourceAnn b S f := by
  simp only [sourceAnn,B,p_I,r_I,A_smul,C_smul,Complex.star_def,Complex.conj_I,smul_add]

lemma sourceCre_I (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E) (f : E) :
    sourceCre b S (Complex.I • f)=Complex.I • sourceCre b S f := by
  simp only [sourceCre,Bstar,p_I,r_I,A_smul,C_smul,Complex.star_def,map_neg,Complex.conj_I,neg_neg,smul_add]

/-- Recover the source annihilator from two real-linear source fields. -/
lemma recover_ann (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E) (f : E) :
    sourceAnn b S f=(1/2 : ℂ) •
      (field b (S f)+Complex.I • field b (S (Complex.I • f))) := by
  rw [← source_field,← source_field,sourceAnn_I,sourceCre_I]
  simp only [smul_add,smul_smul,mul_neg,Complex.I_mul_I,neg_neg,one_smul]
  module

lemma recover_cre (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E) (f : E) :
    sourceCre b S f=(1/2 : ℂ) •
      (field b (S f)-Complex.I • field b (S (Complex.I • f))) := by
  rw [← source_field,← source_field,sourceAnn_I,sourceCre_I]
  simp only [smul_add,smul_smul,mul_neg,Complex.I_mul_I,neg_neg,one_smul]
  module

variable [CompleteSpace E]

/-- The inverse source field orientation on each actual ket is derived from
R35's forward core relations and S(S^-1 f)=f. -/
theorem inverse_ket_transport (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (v : D) (hn : ‖v.1‖=1) (hv : ∀ f,sourceAnn b S f v=0) (m : Occ) :
    ∃ d : D, embedding b S hS v hn hv (ketD m).1=d.1 ∧ ∀ f : E,
      (embedding b S hS v hn hv (sourceAnn b S.symm f (ketD m)).1=
        (sourceAnn b identitySource f d).1) ∧
      (embedding b S hS v hn hv (sourceCre b S.symm f (ketD m)).1=
        (sourceCre b identitySource f d).1) := by
  obtain ⟨d,hd,hfields⟩ := ket_transport b S hS v hn hv m
  have hfield (g : E) : embedding b S hS v hn hv (field b g (ketD m)).1 =
      (field b (S g) d).1 := by
    rw [field_identity,← source_field]
    change embedding b S hS v hn hv
      ((sourceAnn b identitySource g (ketD m)).1+(sourceCre b identitySource g (ketD m)).1)=
      (sourceAnn b S g d).1+(sourceCre b S g d).1
    rw [map_add,(hfields g).1,(hfields g).2]
  refine ⟨d,hd,fun f => ⟨?_,?_⟩⟩
  · rw [recover_ann,recover_ann]
    change embedding b S hS v hn hv ((1/2 : ℂ) •
      ((field b (S.symm f) (ketD m)).1+Complex.I • (field b (S.symm (Complex.I • f)) (ketD m)).1)) =
      (1/2 : ℂ) • ((field b f d).1+Complex.I • (field b (Complex.I • f) d).1)
    rw [map_smul,map_add,map_smul,hfield,hfield,
      ContinuousLinearEquiv.apply_symm_apply,ContinuousLinearEquiv.apply_symm_apply]
  · rw [recover_cre,recover_cre]
    change embedding b S hS v hn hv ((1/2 : ℂ) •
      ((field b (S.symm f) (ketD m)).1-Complex.I • (field b (S.symm (Complex.I • f)) (ketD m)).1)) =
      (1/2 : ℂ) • ((field b f d).1-Complex.I • (field b (Complex.I • f) d).1)
    rw [map_smul,map_sub,map_smul,hfield,hfield,
      ContinuousLinearEquiv.apply_symm_apply,ContinuousLinearEquiv.apply_symm_apply]

/-- Pulling back an ordinary annihilation image gives the literal inverse
source's weak annihilation image. No graph approximation is assumed. -/
theorem pullback_inverse_annGraph (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (v : D) (hn : ‖v.1‖=1) (hv : ∀ f,sourceAnn b S f v=0) (f : E) (w : D) :
    AnnGraph b S.symm f (pullback b S hS v hn hv w.1)
      (pullback b S hS v hn hv (sourceAnn b identitySource f w).1) := by
  intro m
  obtain ⟨d,hd,hfields⟩ := inverse_ket_transport b S hS v hn hv m
  rw [pullback_inner,hd,source_adjoint,← (hfields f).2,← pullback_inner]

/-- Both inverse-source rows are derived, with the same original source S. -/
theorem pullback_inverse_creGraph (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (v : D) (hn : ‖v.1‖=1) (hv : ∀ f,sourceAnn b S f v=0) (f : E) (w : D) :
    CreGraph b S.symm f (pullback b S hS v hn hv w.1)
      (pullback b S hS v hn hv (sourceCre b identitySource f w).1) := by
  intro m
  obtain ⟨d,hd,hfields⟩ := inverse_ket_transport b S hS v hn hv m
  rw [pullback_inner,hd,source_adjoint_rev,← (hfields f).1,← pullback_inner]

/-- The pulled-back ordinary vacuum is inverse-source annihilated in the
closed weak graph. Smoothness and canonical identification remain separate. -/
theorem pullback_vacuum_inverse_graph (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (v : D) (hn : ‖v.1‖=1) (hv : ∀ f,sourceAnn b S f v=0) (f : E) :
    AnnGraph b S.symm f (pullback b S hS v hn hv (ketD 0).1) 0 := by
  have h := pullback_inverse_annGraph b S hS v hn hv f (ketD 0)
  simp only [identity_vacuum,Submodule.coe_zero,map_zero] at h
  exact h

/-- The pulled-back ordinary vacuum is NONZERO. This uses the proved
nonvanishing vacuum coefficient of the original normalized source vacuum. -/
theorem pullback_vacuum_ne_zero (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (v : D) (hn : ‖v.1‖=1) (hv : ∀ f,sourceAnn b S f v=0) :
    pullback b S hS v hn hv vacuum ≠ 0 := by
  intro hz
  have hnz := vacuum_coefficient_ne_zero
    (Ext006SourceVacuumUniqueR35a.source_ann_implies_weak b S hS v hv) hn
  have he : inner ℂ v.1 vacuum=0 := by
    rw [← embedding_vacuum b S hS v hn hv,← pullback_inner,hz,inner_zero_right]
  have hc := congrArg (starRingEnd ℂ) he
  apply hnz
  simpa [vacuum,lp.inner_single_right,RCLike.inner_apply] using hc

/-- Both inverse-source weak graph relations and a nonzero inverse-source
weak-graph vacuum are constructed from the original physical source data. -/
theorem source_inverse_graphs {L : ℝ} [Fact (0 < L)]
    (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (hβ : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) ≠ ⊤) :
    ∃ T : Fock →L[ℂ] Fock, T vacuum ≠ 0 ∧
      (∀ f, AnnGraph (physicalBasis L) S.symm f (T vacuum) 0) ∧
      ∀ (w : D) (f : PhysicalTensor.L2T L),
        AnnGraph (physicalBasis L) S.symm f (T w.1)
          (T (sourceAnn (physicalBasis L) identitySource f w).1) ∧
        CreGraph (physicalBasis L) S.symm f (T w.1)
          (T (sourceCre (physicalBasis L) identitySource f w).1) := by
  obtain ⟨v,hn,hv⟩ := source_vacuum S hS hβ
  exact ⟨pullback (physicalBasis L) S hS v hn hv,
    pullback_vacuum_ne_zero (physicalBasis L) S hS v hn hv,
    pullback_vacuum_inverse_graph (physicalBasis L) S hS v hn hv,
    fun w f => ⟨pullback_inverse_annGraph (physicalBasis L) S hS v hn hv f w,
      pullback_inverse_creGraph (physicalBasis L) S hS v hn hv f w⟩⟩

end QuantumNLS.Ext006InverseGraphsR36a

#print axioms QuantumNLS.Ext006InverseGraphsR36a.pullback_vacuum_ne_zero
#print axioms QuantumNLS.Ext006InverseGraphsR36a.source_inverse_graphs
#print axioms QuantumNLS.Ext006InverseGraphsR36a.source_field
#print axioms QuantumNLS.Ext006InverseGraphsR36a.recover_ann
#print axioms QuantumNLS.Ext006InverseGraphsR36a.inverse_ket_transport
#print axioms QuantumNLS.Ext006InverseGraphsR36a.pullback_inverse_annGraph
#print axioms QuantumNLS.Ext006InverseGraphsR36a.pullback_inverse_creGraph
#print axioms QuantumNLS.Ext006InverseGraphsR36a.pullback_vacuum_inverse_graph

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006InverseGraphsR36a." then
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
