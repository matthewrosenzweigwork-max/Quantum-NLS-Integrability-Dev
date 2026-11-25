import QuantumNLS.Ext006FieldDeficiencyR44a
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-! Maximality of the field closure on the analytic-vector core, obtained
by orthogonal graph decomposition and the proved vanishing deficiencies. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace
namespace QuantumNLS.Ext006FieldMaximalityR44a
open Ext006BogoliubovAlg Ext006VacuumRecurrence Ext006SmoothOperatorsR34a
open Ext006StrongFieldR41a Ext006FieldBoundsR42a Ext006BoundedExponentialR43a
open Ext006FieldClosureR42a Ext006FieldDeficiencyR44a
open WithLp

abbrev Pair := WithLp 2 (Fock × Fock)

def graphMap (h : H) : Core →ₗ[ℂ] Pair :=
  (WithLp.linearEquiv 2 ℂ (Fock × Fock)).symm.toLinearMap.comp
    (inclusion.prod (Ext006SmoothOperatorsR34a.domain.subtype.comp
      ((field h).comp particleDomain.subtype)))

lemma graphMap_apply (h : H) (v : Core) :
    graphMap h v = toLp 2 (inclusion v,(field h v.1).1) := rfl

def closedCoreGraph (h : H) : Submodule ℂ Pair := (graphMap h).range.topologicalClosure

def weakCoreGraph (h : H) : Submodule ℂ Pair where
  carrier := {p | ∀ v : Core, inner ℂ (field h v.1).1 p.fst = inner ℂ (inclusion v) p.snd}
  zero_mem' := by simp
  add_mem' := by intro p q hp hq v; simp only [add_fst,add_snd,inner_add_right]; rw [hp v,hq v]
  smul_mem' := by intro a p hp v; simp only [smul_fst,smul_snd,inner_smul_right]; rw [hp v]

lemma weakCoreGraph_closed (h : H) : IsClosed (weakCoreGraph h : Set Pair) := by
  have he : (weakCoreGraph h : Set Pair) =
      ⋂ v : Core, {p : Pair | inner ℂ (field h v.1).1 p.fst = inner ℂ (inclusion v) p.snd} := by
    ext p
    simp only [Set.mem_iInter,Set.mem_ofPred_eq]
    rfl
  rw [he]
  exact isClosed_iInter (fun _ => isClosed_eq
    (continuous_const.inner (WithLp.continuous_fst 2 Fock Fock))
    (continuous_const.inner (WithLp.continuous_snd 2 Fock Fock)))

lemma core_mem_closed (h : H) (v : Core) : graphMap h v ∈ closedCoreGraph h :=
  (graphMap h).range.le_topologicalClosure ⟨v,rfl⟩

lemma closedCoreGraph_le_weak (h : H) : closedCoreGraph h ≤ weakCoreGraph h := by
  apply (graphMap h).range.topologicalClosure_minimal ?_ (weakCoreGraph_closed h)
  rintro p ⟨v,rfl⟩ w
  exact (field_symmetric h w.1 v.1).symm

/-- The analytic core closure equals its full weak adjoint graph. -/
theorem closedCoreGraph_eq_weak (h : H) : closedCoreGraph h = weakCoreGraph h := by
  apply le_antisymm (closedCoreGraph_le_weak h)
  intro p hp
  let : CompleteSpace (closedCoreGraph h) :=
    (graphMap h).range.isClosed_topologicalClosure.completeSpace_coe
  obtain ⟨q,hq,r,hr,hpr⟩ := (closedCoreGraph h).exists_add_mem_mem_orthogonal p
  have hrw : r ∈ weakCoreGraph h := by
    have he := (weakCoreGraph h).sub_mem hp (closedCoreGraph_le_weak h hq)
    simpa only [hpr,add_sub_cancel_left] using he
  have ho (v : Core) :
      inner ℂ (inclusion v) r.fst + inner ℂ (field h v.1).1 r.snd = 0 := by
    have he := (closedCoreGraph h).inner_right_of_mem_orthogonal (core_mem_closed h v) hr
    exact he
  have hdplus : Defect h (-1) (r.fst+Complex.I • r.snd) := by
    intro v
    have hw := hrw v
    simp only [inner_add_right,inner_smul_right,Complex.ofReal_neg,Complex.ofReal_one,mul_neg,mul_one]
    rw [hw]
    linear_combination (norm := (ring_nf; simp [Complex.I_sq])) Complex.I * ho v
  have hdminus : Defect h 1 (r.fst-Complex.I • r.snd) := by
    intro v
    have hw := hrw v
    simp only [inner_sub_right,inner_smul_right,Complex.ofReal_one,mul_one]
    rw [hw]
    linear_combination (norm := (ring_nf; simp [Complex.I_sq])) -Complex.I * ho v
  have hpz := defect_zero h (-1) (by norm_num) _ hdplus
  have hmz := defect_zero h 1 (by norm_num) _ hdminus
  have hfst : r.fst=0 := by
    calc
      r.fst = (1/2 : ℂ) • ((r.fst+Complex.I • r.snd)+(r.fst-Complex.I • r.snd)) := by module
      _ = 0 := by rw [hpz,hmz]; simp
  have hsnd : r.snd=0 := by
    rw [hfst,zero_add] at hpz
    exact (smul_eq_zero.mp hpz).resolve_left Complex.I_ne_zero
  have hrz : r=0 := by
    apply (WithLp.equiv 2 (Fock × Fock)).injective
    exact Prod.ext hfst hsnd
  simpa only [hpr,hrz,add_zero] using hq

/-- The closure of the field on the whole smooth domain is exactly the
closure of its bounded-particle analytic core. -/
theorem analytic_core_graph (h : H) (x y : Fock) :
    toLp 2 (x,y) ∈ closedCoreGraph h ↔ (x,y) ∈ closedFieldGraph h := by
  constructor
  · intro hp
    have hs : IsClosed {p : Pair | (p.fst,p.snd) ∈ closedFieldGraph h} :=
      (closedFieldGraph_closed h).preimage
        ((WithLp.continuous_fst 2 Fock Fock).prodMk (WithLp.continuous_snd 2 Fock Fock))
    have hi : (closedCoreGraph h : Set Pair) ⊆ {p : Pair | (p.fst,p.snd) ∈ closedFieldGraph h} := by
      apply closure_minimal ?_ hs
      rintro p ⟨v,rfl⟩
      apply subset_closure
      exact ⟨v.1,rfl⟩
    exact hi hp
  · intro hp
    rw [closedCoreGraph_eq_weak]
    have hs : IsClosed {p : Fock × Fock | toLp 2 p ∈ weakCoreGraph h} :=
      (weakCoreGraph_closed h).preimage (WithLp.prod_continuous_toLp 2 Fock Fock)
    have hi : closedFieldGraph h ⊆ {p : Fock × Fock | toLp 2 p ∈ weakCoreGraph h} := by
      apply closure_minimal ?_ hs
      rintro p ⟨v,rfl⟩ w
      exact (field_symmetric h w.1 v).symm
    exact hi hp

end QuantumNLS.Ext006FieldMaximalityR44a
#print axioms QuantumNLS.Ext006FieldMaximalityR44a.closedCoreGraph_eq_weak
#print axioms QuantumNLS.Ext006FieldMaximalityR44a.analytic_core_graph

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006FieldMaximalityR44a." then
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
