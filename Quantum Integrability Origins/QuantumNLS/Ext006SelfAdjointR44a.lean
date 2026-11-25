import QuantumNLS.Ext006FieldMaximalityR44a

/-! The closure of the actual smooth smeared field, as a self-adjoint
partially defined operator. All domain and maximality statements refer to
the previously constructed analytic core and literal closed graph. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace
open scoped LinearPMap
namespace QuantumNLS.Ext006SelfAdjointR44a
open Ext006BogoliubovAlg Ext006VacuumRecurrence Ext006SmoothOperatorsR34a
open Ext006StrongFieldR41a Ext006FieldBoundsR42a Ext006BoundedExponentialR43a
open Ext006FieldClosureR42a Ext006FieldMaximalityR44a
open WithLp

def graph (h : H) : Submodule ℂ (Fock × Fock) :=
  (closedCoreGraph h).map (WithLp.linearEquiv 2 ℂ (Fock × Fock)).toLinearMap

lemma mem_graph (h : H) (x y : Fock) :
    (x,y) ∈ graph h ↔ toLp 2 (x,y) ∈ closedCoreGraph h := by
  constructor
  · rintro ⟨p,hp,he⟩
    have hpe : p=toLp 2 (x,y) := by
      apply (WithLp.equiv 2 (Fock × Fock)).injective
      exact he
    rwa [← hpe]
  · intro hp
    exact ⟨toLp 2 (x,y),hp,rfl⟩

lemma graph_eq_closedFieldGraph (h : H) :
    (graph h : Set (Fock × Fock)) = closedFieldGraph h := by
  ext p
  exact (mem_graph h p.1 p.2).trans (analytic_core_graph h p.1 p.2)

lemma graph_mem_closed (h : H) (x y : Fock) :
    (x,y) ∈ graph h ↔ (x,y) ∈ closedFieldGraph h :=
  (mem_graph h x y).trans (analytic_core_graph h x y)

lemma graph_smooth (h : H) (v : D) : (v.1,(field h v).1) ∈ graph h := by
  rw [graph_mem_closed]
  exact subset_closure ⟨v,rfl⟩

lemma graph_zero (h : H) (p : Fock × Fock) (hp : p ∈ graph h)
    (hx : p.1=0) : p.2=0 := by
  have hp := (graph_mem_closed h p.1 p.2).mp hp
  rw [hx] at hp
  have hz : ((0 : Fock),0) ∈ closedFieldGraph h := by
    have he := graph_smooth h (0 : D)
    rw [graph_mem_closed] at he
    simpa using he
  exact closedFieldGraph_unique h hp hz

/-- The actual closure is constructed from its single-valued closed graph. -/
def closureField (h : H) : Fock →ₗ.[ℂ] Fock := (graph h).toLinearPMap

lemma closureField_graph (h : H) : (closureField h).graph=graph h :=
  (graph h).toLinearPMap_graph_eq (graph_zero h)

lemma closureField_dense (h : H) : Dense ((closureField h).domain : Set Fock) := by
  have hd : Dense (Ext006SmoothOperatorsR34a.domain : Set Fock) := by
    intro x
    have hx := smooth_domain_dense x
    have hr : Set.range (fun v : D => v.1)=(Ext006SmoothOperatorsR34a.domain : Set Fock) := by
      ext z
      constructor
      · rintro ⟨v,rfl⟩
        exact v.2
      · intro hz
        exact ⟨⟨z,hz⟩,rfl⟩
    change x ∈ closure (Set.range (fun v : D => v.1)) at hx
    rwa [hr] at hx
  apply hd.mono
  intro x hx
  have he := graph_smooth h ⟨x,hx⟩
  rw [← closureField_graph,LinearPMap.mem_graph_iff] at he
  obtain ⟨y,hy,-⟩ := he
  change (y : Fock)=x at hy
  exact hy ▸ y.2

lemma graph_adjoint (h : H) : (graph h).adjoint=graph h := by
  ext p
  constructor
  · intro hp
    rw [mem_graph,closedCoreGraph_eq_weak]
    intro v
    have he := (Submodule.mem_adjoint_iff (graph h) p).mp hp
      (inclusion v) (field h v.1).1 (graph_smooth h v.1)
    exact sub_eq_zero.mp he
  · intro hp
    rw [Submodule.mem_adjoint_iff]
    have hw : toLp 2 p ∈ weakCoreGraph h := by
      rw [← closedCoreGraph_eq_weak]
      exact (mem_graph h p.1 p.2).mp hp
    have hall : (closedCoreGraph h : Set Pair) ⊆
        {q : Pair | inner ℂ q.snd p.1=inner ℂ q.fst p.2} := by
      apply closure_minimal ?_ (isClosed_eq
        ((WithLp.continuous_snd 2 Fock Fock).inner continuous_const)
        ((WithLp.continuous_fst 2 Fock Fock).inner continuous_const))
      rintro q ⟨v,rfl⟩
      exact hw v
    intro a b hab
    exact sub_eq_zero.mpr (hall ((mem_graph h a b).mp hab))

lemma closedFieldGraph_symmetric (h : H) {x y u v : Fock}
    (hxy : (x,y) ∈ closedFieldGraph h) (huv : (u,v) ∈ closedFieldGraph h) :
    inner ℂ y u = inner ℂ x v := by
  have hxy' : (x,y) ∈ graph h := by rw [graph_mem_closed]; exact hxy
  have huv' : (u,v) ∈ (graph h).adjoint := by
    rw [graph_adjoint,graph_mem_closed]
    exact huv
  exact sub_eq_zero.mp ((Submodule.mem_adjoint_iff (graph h) (u,v)).mp huv' x y hxy')

/-- Essential self-adjointness on the actual bounded-particle analytic core:
its graph closure is the literal smooth-field closure, and that closure
is self-adjoint in Mathlib's partially defined operator sense. -/
theorem closureField_selfAdjoint (h : H) : IsSelfAdjoint (closureField h) := by
  rw [LinearPMap.isSelfAdjoint_def]
  apply LinearPMap.eq_of_eq_graph
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint (closureField_dense h),
    closureField_graph,graph_adjoint]

end QuantumNLS.Ext006SelfAdjointR44a
#print axioms QuantumNLS.Ext006SelfAdjointR44a.closureField_graph
#print axioms QuantumNLS.Ext006SelfAdjointR44a.closureField_selfAdjoint

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006SelfAdjointR44a." then
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
  Lean.logInfo m!"Round44a aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
