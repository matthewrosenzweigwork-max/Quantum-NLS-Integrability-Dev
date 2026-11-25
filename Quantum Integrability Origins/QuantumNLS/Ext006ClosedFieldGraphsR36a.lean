import QuantumNLS.Ext006CoreTransportR35a

/-! Closed weak graphs of the actual source fields. Ket tests are total in
completed occupation Fock. Norm limits below require convergence of BOTH
vector and field image; no invariance of a closed range is inferred. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Filter Topology
open scoped InnerProductSpace
namespace QuantumNLS.Ext006ClosedFieldGraphsR36a
open Occupation Ext006VacuumRecurrence Ext006BogoliubovAlg
open Ext006SmoothOperatorsR34a Ext006SourceCCRR34a Ext006CreationGramR34a
open Ext006CyclicIsometryR34a Ext006IdentityCyclicR35a Ext006FockEmbeddingR35a
open Ext006CoreTransportR35a
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
attribute [local instance] InnerProductSpace.complexToReal

/-- Maximal weak annihilation graph, using the actual adjoint creator on kets. -/
def AnnGraph (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E) (f : E)
    (x y : Fock) : Prop :=
  ∀ m : Occ, inner ℂ (ketD m).1 y = inner ℂ (sourceCre b S f (ketD m)).1 x

/-- Maximal weak creation graph, with the actual annihilator as test action. -/
def CreGraph (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E) (f : E)
    (x y : Fock) : Prop :=
  ∀ m : Occ, inner ℂ (ketD m).1 y = inner ℂ (sourceAnn b S f (ketD m)).1 x

lemma ket_total {x y : Fock}
    (h : ∀ m : Occ, inner ℂ (ketD m).1 x=inner ℂ (ketD m).1 y) : x=y := by
  apply lp.ext
  funext m
  simpa [ketD,lp.inner_single_left,RCLike.inner_apply] using h m

lemma annGraph_unique (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E) (f : E)
    {x y z : Fock} (hy : AnnGraph b S f x y) (hz : AnnGraph b S f x z) : y=z :=
  ket_total (fun m => (hy m).trans (hz m).symm)

lemma creGraph_unique (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E) (f : E)
    {x y z : Fock} (hy : CreGraph b S f x y) (hz : CreGraph b S f x z) : y=z :=
  ket_total (fun m => (hy m).trans (hz m).symm)

/-- Every constructed smooth vector lies in the weak graph, with its actual action. -/
lemma annGraph_smooth (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E) (f : E) (w : D) :
    AnnGraph b S f w.1 (sourceAnn b S f w).1 :=
  fun m => source_adjoint b S f (ketD m) w

lemma source_adjoint_rev (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E) (f : E) (v w : D) :
    inner ℂ v.1 (sourceCre b S f w).1 = inner ℂ (sourceAnn b S f v).1 w.1 := by
  have h := congrArg (starRingEnd ℂ) (source_adjoint b S f w v)
  simpa only [inner_conj_symm] using h.symm

lemma creGraph_smooth (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E) (f : E) (w : D) :
    CreGraph b S f w.1 (sourceCre b S f w).1 :=
  fun m => source_adjoint_rev b S f (ketD m) w

lemma annGraph_closed (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E) (f : E) :
    IsClosed {z : Fock × Fock | AnnGraph b S f z.1 z.2} := by
  have he : {z : Fock × Fock | AnnGraph b S f z.1 z.2} =
      ⋂ m : Occ, {z : Fock × Fock |
        inner ℂ (ketD m).1 z.2 = inner ℂ (sourceCre b S f (ketD m)).1 z.1} := by
    ext z
    simp only [Set.mem_ofPred_eq,Set.mem_iInter,AnnGraph]
  rw [he]
  exact isClosed_iInter (fun _ => isClosed_eq (continuous_const.inner continuous_snd)
    (continuous_const.inner continuous_fst))

lemma creGraph_closed (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E) (f : E) :
    IsClosed {z : Fock × Fock | CreGraph b S f z.1 z.2} := by
  have he : {z : Fock × Fock | CreGraph b S f z.1 z.2} =
      ⋂ m : Occ, {z : Fock × Fock |
        inner ℂ (ketD m).1 z.2 = inner ℂ (sourceAnn b S f (ketD m)).1 z.1} := by
    ext z
    simp only [Set.mem_ofPred_eq,Set.mem_iInter,CreGraph]
  rw [he]
  exact isClosed_iInter (fun _ => isClosed_eq (continuous_const.inner continuous_snd)
    (continuous_const.inner continuous_fst))

/-- Strong graph-limit passage, without assuming that the limit is smooth. -/
lemma annGraph_limit (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E) (f : E)
    {I : Type*} {l : Filter I} [NeBot l] {x y : I → Fock} {u v : Fock}
    (hx : Tendsto x l (𝓝 u)) (hy : Tendsto y l (𝓝 v))
    (h : ∀ᶠ i in l, AnnGraph b S f (x i) (y i)) : AnnGraph b S f u v :=
  (annGraph_closed b S f).mem_of_tendsto (hx.prodMk_nhds hy) h

lemma creGraph_limit (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E) (f : E)
    {I : Type*} {l : Filter I} [NeBot l] {x y : I → Fock} {u v : Fock}
    (hx : Tendsto x l (𝓝 u)) (hy : Tendsto y l (𝓝 v))
    (h : ∀ᶠ i in l, CreGraph b S f (x i) (y i)) : CreGraph b S f u v :=
  (creGraph_closed b S f).mem_of_tendsto (hx.prodMk_nhds hy) h

variable [CompleteSpace E]

/-- R35's source annihilator relation passes through every genuine graph
approximation by identity polynomials, even when the target limit is not smooth. -/
theorem embedding_annGraph_limit (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (v : D) (hn : ‖v.1‖=1) (hv : ∀ f,sourceAnn b S f v=0)
    (f : E) {I : Type*} {l : Filter I} [NeBot l]
    (c : I → List E →₀ ℂ) (x y : Fock)
    (hx : Tendsto (fun i => (evalDomain b identitySource (ketD 0) (c i)).1) l (𝓝 x))
    (hy : Tendsto (fun i => (sourceAnn b identitySource f
      (evalDomain b identitySource (ketD 0) (c i))).1) l (𝓝 y)) :
    AnnGraph b S f (embedding b S hS v hn hv x) (embedding b S hS v hn hv y) := by
  apply annGraph_limit b S f
    ((embedding b S hS v hn hv).continuous.continuousAt.tendsto.comp hx)
    ((embedding b S hS v hn hv).continuous.continuousAt.tendsto.comp hy)
  apply Filter.Eventually.of_forall
  intro i
  simp only [Function.comp_apply]
  rw [embedding_domain,core_ann]
  exact annGraph_smooth b S f (evalDomain b S v (c i))

/-- The corresponding creator passage retains the same explicit graph premise. -/
theorem embedding_creGraph_limit (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (v : D) (hn : ‖v.1‖=1) (hv : ∀ f,sourceAnn b S f v=0)
    (f : E) {I : Type*} {l : Filter I} [NeBot l]
    (c : I → List E →₀ ℂ) (x y : Fock)
    (hx : Tendsto (fun i => (evalDomain b identitySource (ketD 0) (c i)).1) l (𝓝 x))
    (hy : Tendsto (fun i => (sourceCre b identitySource f
      (evalDomain b identitySource (ketD 0) (c i))).1) l (𝓝 y)) :
    CreGraph b S f (embedding b S hS v hn hv x) (embedding b S hS v hn hv y) := by
  apply creGraph_limit b S f
    ((embedding b S hS v hn hv).continuous.continuousAt.tendsto.comp hx)
    ((embedding b S hS v hn hv).continuous.continuousAt.tendsto.comp hy)
  apply Filter.Eventually.of_forall
  intro i
  simp only [Function.comp_apply]
  rw [embedding_domain,core_cre]
  exact creGraph_smooth b S f (evalDomain b S v (c i))

end QuantumNLS.Ext006ClosedFieldGraphsR36a

#print axioms QuantumNLS.Ext006ClosedFieldGraphsR36a.annGraph_closed
#print axioms QuantumNLS.Ext006ClosedFieldGraphsR36a.creGraph_closed
#print axioms QuantumNLS.Ext006ClosedFieldGraphsR36a.annGraph_unique
#print axioms QuantumNLS.Ext006ClosedFieldGraphsR36a.embedding_annGraph_limit
#print axioms QuantumNLS.Ext006ClosedFieldGraphsR36a.embedding_creGraph_limit

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006ClosedFieldGraphsR36a." then
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
