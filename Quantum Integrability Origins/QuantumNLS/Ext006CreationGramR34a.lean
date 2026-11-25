import QuantumNLS.Ext006SourceCCRR34a

/-! Source creation-word Gram matrix. Normal ordering is a theorem of the
actual source operators. The final existence theorem constructs its vacuum
from the original source symplectic and HS assumptions. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped InnerProductSpace
namespace QuantumNLS.Ext006CreationGramR34a
open Occupation Ext006VacuumRecurrence Ext006BogoliubovAlg Ext006QuasifreeWeak
open Ext006ModeDomainR33a Ext006SmearedDomainR33a Ext006SmoothOperatorsR34a
open Ext006SourceCCRR34a Ext006KernelHilbertSchmidt
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
attribute [local instance] InnerProductSpace.complexToReal
variable (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E)

/-- Ordered creation words on the actual invariant domain. -/
def word : List E → D → D
  | [],v => v
  | f::fs,v => sourceCre b S f (word fs v)

/-- The finite formal derivative, retaining multiplicities and ordering. -/
def derivative (f : E) : List E → List (ℂ × List E)
  | [] => []
  | g::gs => (inner ℂ f g,gs)::(derivative f gs).map (fun z => (z.1,g::z.2))

/-- Evaluation of a finite formal combination of words. -/
def wordSum (zs : List (ℂ × List E)) (v : D) : D :=
  (zs.map (fun z => z.1 • word b S z.2 v)).sum

omit [CompleteSpace E] in
lemma wordSum_cons (z : ℂ × List E) (zs : List (ℂ × List E)) (v : D) :
    wordSum b S (z::zs) v = z.1 • word b S z.2 v+wordSum b S zs v := rfl

omit [CompleteSpace E] in
lemma wordSum_prefix (g : E) (zs : List (ℂ × List E)) (v : D) :
    wordSum b S (zs.map (fun z => (z.1,g::z.2))) v = sourceCre b S g (wordSum b S zs v) := by
  induction zs with
  | nil => simp [wordSum]
  | cons z zs ih =>
    simp only [List.map_cons,wordSum_cons,word,map_add,map_smul,ih]

lemma normal_order (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (f g : E) (v : D) :
    sourceAnn b S f (sourceCre b S g v) =
      (inner ℂ f g) • v+sourceCre b S g (sourceAnn b S f v) := by
  have he := LinearMap.congr_fun (source_AC b S hS f g) v
  change sourceAnn b S f (sourceCre b S g v)-sourceCre b S g (sourceAnn b S f v) =
    (inner ℂ f g) • v at he
  exact sub_eq_iff_eq_add.mp he

/-- An annihilator acts by the finite formal derivative on every word. -/
theorem ann_word (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (v : D) (hv : ∀ f,sourceAnn b S f v=0) (f : E) (gs : List E) :
    sourceAnn b S f (word b S gs v) = wordSum b S (derivative f gs) v := by
  induction gs with
  | nil => simpa only [word,derivative,wordSum,List.map_nil,List.sum_nil] using hv f
  | cons g gs ih =>
    rw [word,normal_order b S hS,ih,derivative,wordSum_cons,wordSum_prefix]

/-- The free bosonic Wick Gram kernel, defined by finite contraction. The
empty word has mass one; all nonempty words have zero vacuum expectation. -/
def wick : List E → List E → ℂ
  | [],gs => if gs=[] then 1 else 0
  | f::fs,gs => ((derivative f gs).map (fun z => z.1*wick fs z.2)).sum

omit [CompleteSpace E] in
lemma inner_wordSum (u v : D) (zs : List (ℂ × List E)) :
    inner ℂ u.1 ((wordSum b S zs v).1) =
      (zs.map (fun z => z.1*inner ℂ u.1 ((word b S z.2 v).1))).sum := by
  induction zs with
  | nil => simp [wordSum]
  | cons z zs ih =>
    change inner ℂ u.1 (z.1 • ((word b S z.2 v).1)+(wordSum b S zs v).1) = _
    rw [inner_add_right,inner_smul_right,ih]
    rfl

/-- The actual source word Gram matrix is the free Wick Gram matrix.
This lemma is applied below to a vacuum constructed from source HS data. -/
theorem gram (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (v : D) (hn : ‖v.1‖=1) (hv : ∀ f,sourceAnn b S f v=0)
    (fs gs : List E) :
    inner ℂ ((word b S fs v).1) ((word b S gs v).1) = wick fs gs := by
  induction fs generalizing gs with
  | nil =>
    cases gs with
    | nil => simpa only [word,wick,ite_true] using inner_self_eq_one_of_norm_eq_one hn
    | cons g gs =>
      change inner ℂ v.1 ((sourceCre b S g (word b S gs v)).1) = 0
      apply inner_eq_zero_symm.mp
      rw [← source_adjoint b S g, hv]
      simp
  | cons f fs ih =>
    change inner ℂ ((sourceCre b S f (word b S fs v)).1) ((word b S gs v).1) = _
    rw [← source_adjoint b S f,ann_word b S hS v hv,inner_wordSum]
    simp only [wick,ih]

section Physical
variable {L : ℝ} [Fact (0 < L)]

/-- The source-HS vacuum is constructed; its annihilation and domain are
proved in the frozen R33a source theorem, not supplied to this result. -/
theorem source_vacuum
    (T : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hT : Ext006SymplecticKernel.Symplectic T.toContinuousLinearMap)
    (hβ : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) T) ≠ ⊤) :
    ∃ v : D, ‖v.1‖=1 ∧ ∀ f, sourceAnn (physicalBasis L) T f v=0 := by
  obtain ⟨x,hxn,hx,hvac⟩ := Ext006StrongVacuumR33a.source_physical_blocks T hT hβ
  let v : D := ⟨Ext006PhysFockCoord.Phi x,hx⟩
  refine ⟨v,?_,fun f => ?_⟩
  · change ‖Ext006PhysFockCoord.Phi x‖=1
    rw [LinearIsometryEquiv.norm_map,hxn]
  · apply Subtype.ext
    change smearedAnn (p (physicalBasis L) T f) (Ext006PhysFockCoord.Phi x) hx +
      smearedCre (r (physicalBasis L) T f) (Ext006PhysFockCoord.Phi x) hx = 0
    have he := congrArg (Ext006PhysFockCoord.Phi (L := L)) (hvac f)
    simpa only [p,r,map_add,map_zero,Ext006StrongVacuumR33a.physicalAnn,
      Ext006StrongVacuumR33a.physicalCre,LinearIsometryEquiv.apply_symm_apply] using he

/-- Gram matrix of the constructed original-source creation words, under
precisely the original symplectic and Hilbert-Schmidt assumptions. -/
theorem source_gram
    (T : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hT : Ext006SymplecticKernel.Symplectic T.toContinuousLinearMap)
    (hβ : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) T) ≠ ⊤) :
    ∃ v : D, ‖v.1‖=1 ∧ (∀ f,sourceAnn (physicalBasis L) T f v=0) ∧
      ∀ fs gs : List (PhysicalTensor.L2T L),
        inner ℂ ((word (physicalBasis L) T fs v).1) ((word (physicalBasis L) T gs v).1)=wick fs gs := by
  obtain ⟨v,hn,hv⟩ := source_vacuum T hT hβ
  exact ⟨v,hn,hv,gram (physicalBasis L) T hT v hn hv⟩

end Physical
end QuantumNLS.Ext006CreationGramR34a

#print axioms QuantumNLS.Ext006CreationGramR34a.normal_order
#print axioms QuantumNLS.Ext006CreationGramR34a.ann_word
#print axioms QuantumNLS.Ext006CreationGramR34a.gram
#print axioms QuantumNLS.Ext006CreationGramR34a.source_vacuum
#print axioms QuantumNLS.Ext006CreationGramR34a.source_gram

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006CreationGramR34a." then
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
  Lean.logInfo m!"Round34a aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
