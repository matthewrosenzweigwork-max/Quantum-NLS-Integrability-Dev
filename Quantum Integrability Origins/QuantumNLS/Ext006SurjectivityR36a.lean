import QuantumNLS.Ext006GraphVacuumR36a

/-! Surjectivity of the original source embedding, using its actual adjoint
and a constructed inverse-source vacuum. The adjoint is a nonzero scalar
multiple of the inverse-source isometry on a proved dense core, hence is
injective. This gives a physical whole-Fock UNITARY; the literal frozen
HeisAnn/HeisCre row-coordinate identities remain separate obligations. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped InnerProductSpace
namespace QuantumNLS.Ext006SurjectivityR36a
open Occupation Ext006VacuumRecurrence Ext006BogoliubovAlg
open Ext006SmoothOperatorsR34a Ext006SourceCCRR34a Ext006CreationGramR34a
open Ext006CyclicIsometryR34a Ext006IdentityCyclicR35a Ext006FockEmbeddingR35a
open Ext006CoreTransportR35a Ext006ClosedFieldGraphsR36a Ext006AdjointTransportR36a
open Ext006InverseSourceR36a Ext006InverseGraphsR36a Ext006GraphVacuumR36a
open Ext006KernelHilbertSchmidt
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
attribute [local instance] InnerProductSpace.complexToReal

/-- Weak graph uniqueness upgrades each pulled-back creator word to the
actual smooth inverse-source word, starting from the identified vacuum. -/
lemma pullback_word (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (v w : D) (hn : ‖v.1‖=1) (hv : ∀ f,sourceAnn b S f v=0)
    (c : ℂ) (hc : pullback b S hS v hn hv vacuum=c • w.1) (fs : List E) :
    pullback b S hS v hn hv (word b identitySource fs (ketD 0)).1=
      c • (word b S.symm fs w).1 := by
  induction fs with
  | nil => exact hc
  | cons f fs ih =>
    have hg := pullback_inverse_creGraph b S hS v hn hv f (word b identitySource fs (ketD 0))
    rw [ih] at hg
    have ht := creGraph_smooth b S.symm f (c • word b S.symm fs w)
    have he := creGraph_unique b S.symm f hg ht
    simpa only [word,map_smul,Submodule.coe_smul] using he

lemma pullback_eval (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (v w : D) (hn : ‖v.1‖=1) (hv : ∀ f,sourceAnn b S f v=0)
    (c : ℂ) (hc : pullback b S hS v hn hv vacuum=c • w.1) (d : List E →₀ ℂ) :
    pullback b S hS v hn hv (eval b identitySource (ketD 0) d)=c • eval b S.symm w d := by
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add d e hd he => simp only [map_add,hd,he,smul_add]
  | single fs z =>
    simp only [eval,Finsupp.linearCombination_single,map_smul,
      pullback_word b S hS v w hn hv c hc fs,smul_smul,mul_comm]

/-- The whole adjoint is determined by its proved inverse-source polynomial
action. In particular its injectivity is derived, not assumed. -/
theorem pullback_scalar_inverse (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (v w : D) (hvn : ‖v.1‖=1) (hwn : ‖w.1‖=1)
    (hv : ∀ f,sourceAnn b S f v=0) (hw : ∀ f,sourceAnn b S.symm f w=0) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ x : Fock,
      pullback b S hS v hvn hv x=
        c • embedding b S.symm (inverse_symplectic S hS) w hwn hw x := by
  obtain ⟨c,hc,hvac⟩ := pullback_vacuum_scalar b S hS v w hvn hwn hv hw
  refine ⟨c,hc,?_⟩
  have he := (identity_eval_dense b).equalizer (pullback b S hS v hvn hv).continuous
    ((continuous_const_smul c).comp
      (embedding b S.symm (inverse_symplectic S hS) w hwn hw).continuous)
    (funext fun d => by
      simp only [Function.comp_apply]
      rw [pullback_eval b S hS v w hvn hv c hvac d,embedding_eval])
  exact fun x => congrFun he x

/-- Actual target surjectivity. The inverse vacuum is the only intermediate
data; it is constructed from the original physical HS assumption below. -/
theorem embedding_surjective (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (v w : D) (hvn : ‖v.1‖=1) (hwn : ‖w.1‖=1)
    (hv : ∀ f,sourceAnn b S f v=0) (hw : ∀ f,sourceAnn b S.symm f w=0) :
    Function.Surjective (embedding b S hS v hvn hv) := by
  obtain ⟨c,hc,he⟩ := pullback_scalar_inverse b S hS v w hvn hwn hv hw
  have hinj : Function.Injective (pullback b S hS v hvn hv) := by
    intro x y hxy
    have h : c • embedding b S.symm (inverse_symplectic S hS) w hwn hw x=
        c • embedding b S.symm (inverse_symplectic S hS) w hwn hw y :=
      (he x).symm.trans (hxy.trans (he y))
    have hi := congrArg (fun z : Fock => c⁻¹ • z) h
    apply (embedding b S.symm (inverse_symplectic S hS) w hwn hw).injective
    simpa only [smul_smul,inv_mul_cancel₀ hc,one_smul] using hi
  intro x
  refine ⟨pullback b S hS v hvn hv x,?_⟩
  apply hinj
  exact pullback_embedding b S hS v hvn hv (pullback b S hS v hvn hv x)

theorem source_cyclic_eq_top (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (v w : D) (hvn : ‖v.1‖=1) (hwn : ‖w.1‖=1)
    (hv : ∀ f,sourceAnn b S f v=0) (hw : ∀ f,sourceAnn b S.symm f w=0) :
    cyclic b S v=⊤ := by
  rw [← embedding_range b S hS v hvn hv]
  exact LinearMap.range_eq_top.mpr (embedding_surjective b S hS v w hvn hwn hv hw)

/-- Promote the actual full-domain embedding using the proved surjectivity. -/
def unitary (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (v w : D) (hvn : ‖v.1‖=1) (hwn : ‖w.1‖=1)
    (hv : ∀ f,sourceAnn b S f v=0) (hw : ∀ f,sourceAnn b S.symm f w=0) : Fock ≃ₗᵢ[ℂ] Fock :=
  LinearIsometryEquiv.ofSurjective (embedding b S hS v hvn hv)
    (embedding_surjective b S hS v w hvn hwn hv hw)

section Physical
variable {L : ℝ} [Fact (0 < L)]

def physicalUnitary (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (v w : D) (hvn : ‖v.1‖=1) (hwn : ‖w.1‖=1)
    (hv : ∀ f,sourceAnn (physicalBasis L) S f v=0)
    (hw : ∀ f,sourceAnn (physicalBasis L) S.symm f w=0) :
    Ext025B3PhysicalSectors.Fock L ≃ₗᵢ[ℂ] Ext025B3PhysicalSectors.Fock L :=
  (Ext006PhysFockCoord.Phi.trans
    (unitary (physicalBasis L) S hS v w hvn hwn hv hw)).trans Ext006PhysFockCoord.Phi.symm

/-- A physical whole-Fock UNITARY is constructed from exactly the original
symplectic source and HS beta hypothesis, with its literal creator-word action. -/
theorem source_physical_unitary
    (S : PhysicalTensor.L2T L ≃L[ℝ] PhysicalTensor.L2T L)
    (hS : Ext006SymplecticKernel.Symplectic S.toContinuousLinearMap)
    (hβ : TraceClass.hsSq (physicalBasis L) (beta (physicalBasis L) S) ≠ ⊤) :
    ∃ v : D, ‖v.1‖=1 ∧ (∀ f,sourceAnn (physicalBasis L) S f v=0) ∧
      ∃ U : Ext025B3PhysicalSectors.Fock L ≃ₗᵢ[ℂ] Ext025B3PhysicalSectors.Fock L,
        ∀ fs : List (PhysicalTensor.L2T L),
          U (Ext006PhysFockCoord.Phi.symm (word (physicalBasis L) identitySource fs (ketD 0)).1)=
            Ext006PhysFockCoord.Phi.symm (word (physicalBasis L) S fs v).1 := by
  obtain ⟨v,hvn,hv⟩ := source_vacuum S hS hβ
  obtain ⟨w,hwn,hw⟩ := inverse_source_vacuum S hS hβ
  refine ⟨v,hvn,hv,physicalUnitary S hS v w hvn hwn hv hw,fun fs => ?_⟩
  change Ext006PhysFockCoord.Phi.symm
    (embedding (physicalBasis L) S hS v hvn hv
      (Ext006PhysFockCoord.Phi (Ext006PhysFockCoord.Phi.symm _))) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact congrArg (Ext006PhysFockCoord.Phi (L := L)).symm
    (embedding_word (physicalBasis L) S hS v hvn hv fs)

end Physical
end QuantumNLS.Ext006SurjectivityR36a

#print axioms QuantumNLS.Ext006SurjectivityR36a.pullback_word
#print axioms QuantumNLS.Ext006SurjectivityR36a.pullback_scalar_inverse
#print axioms QuantumNLS.Ext006SurjectivityR36a.embedding_surjective
#print axioms QuantumNLS.Ext006SurjectivityR36a.source_cyclic_eq_top
#print axioms QuantumNLS.Ext006SurjectivityR36a.source_physical_unitary

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006SurjectivityR36a." then
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
