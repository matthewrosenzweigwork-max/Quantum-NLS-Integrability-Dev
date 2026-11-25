import QuantumNLS.Def033BindingR25m
import QuantumNLS.RB7BindFinal

/-!
# Bind7BDEF033H01: DEF-033 binding, ready to promote

Frozen intermediate: `QuantumNLS.Def033BindingR25m.DEF033_intermediate`
(sol_multi round 25, source `QuantumNLS/Def033BindingR25m.lean`,
SHA-256 87d383fdd7a3a9f9b571ac9e34378222de1c9b9b0a5702a118a4d7eeb7319caa).

The sol_multi round 24 object `Def033HierarchyR24m` takes `HierarchyPrintedInput`, which is not the
shared type. Round 25 replaces it with `DEF033_intermediate`, whose single predecessor argument
`HierarchyR7B122087Input : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ` is the shared type exactly.
That argument is discharged here by `QuantumNLS.RB7BindFinal.hierarchyInputR25m_unconditional`
(review record round 86 PASS). No adapter is needed.

Remaining hypotheses: `hκ : 0 < κ`, `w` and `hw : PrintedChart hκ w`, which are the intermediate's own
chart arguments and are not pending predecessors.
This module makes no acceptance claim; R-7B122087 is held for the owner ruling on the DEF-024 predecessor gate.
-/
set_option autoImplicit false
noncomputable section
open Filter MeasureTheory Topology
namespace QuantumNLS.Bind7BDEF033H01
open QuantumNLS.ClassicalCharges QuantumNLS.HierarchyFlow
open QuantumNLS.Def033HierarchyR24m QuantumNLS.Def033CoreR24m
variable {L κ : ℝ} [Fact (0 < L)]

/-- DEF-033 all-order commuting-flow and unique-active-frequency conclusion of
`Def033BindingR25m.DEF033_intermediate`, with the shared hierarchy input discharged. -/
theorem DEF033_bound (hκ : 0 < κ)
    (w : QuantumNLS.PhysicalTensor.L2T L → QuantumNLS.REF88Chart.K)
    (hw : QuantumNLS.REF88PrintedChart.PrintedChart hκ w) :
    ∃ (Ψ : ℕ → ℝ → (ℝ → ℂ) → (ℝ → ℂ))
      (hΨ : ∀ r, IsHamFlow L (hamiltonian L κ r) (Ψ r)),
      (∀ r s, ∀ u : Smooth L, ∀ t τ, Ψ r t (Ψ s τ u.val) = Ψ s τ (Ψ r t u.val)) ∧
      ∀ r (u : Smooth L) n, 0 < (QuantumNLS.RootIndexedMasses.masses hκ (physical u)).1 n →
        ∃! freq : ℝ, ActiveFrequency
          (fun t => w (physical ⟨Ψ r t u.val, ((hΨ r u.val u.property).2.2 t).1⟩) n)
          (w (physical u) n) freq :=
  QuantumNLS.Def033BindingR25m.DEF033_intermediate hκ w hw
    (QuantumNLS.RB7BindFinal.hierarchyInputR25m_unconditional (L := L) hκ)

open Lean Meta in
/-- Index of the first binder whose type is the shared hierarchy input. -/
private partial def sharedBinderIdx (e : Expr) (i : Nat) : Option Nat :=
  match e with
  | .forallE _ d b _ =>
    if d.getAppFn.isConstOf ``QuantumNLS.HierarchyInputR25m.HierarchyR7B122087Input then some i
    else sharedBinderIdx b (i + 1)
  | _ => none

open Lean Meta in
/-- Statement correspondence: the frozen type with its shared binder removed equals this binding type. -/
private def bindCorrespondence (oldN newN : Name) : MetaM (Bool × Bool) := do
  let env ← getEnv
  let some oldCi := env.find? oldN | throwError "missing {oldN}"
  let some newCi := env.find? newN | throwError "missing {newN}"
  let some k := sharedBinderIdx oldCi.type 0 | throwError "no shared binder in {oldN}"
  forallBoundedTelescope oldCi.type (some (k + 1)) fun xs told =>
    forallBoundedTelescope newCi.type (some k) fun ys tnew => do
      if xs.size != k + 1 || ys.size != k then throwError "telescope arity mismatch"
      let xsN := xs.extract 0 k
      let mut binders := true
      for i in [0:k] do
        let tOld ← inferType xs[i]!
        let tNew ← inferType ys[i]!
        unless tOld.replaceFVars xsN ys == tNew do binders := false
      let concl := told.replaceFVars xsN ys
      let eqv := concl == tnew
      let defeq ← isDefEq concl tnew
      return (binders && eqv, binders && defeq)

open Lean Meta in
/-- Transitive closure of a root constant: held names and non-standard axioms are rejected. -/
private def transitiveAudit (root : Name) : MetaM (Nat × Nat) := do
  let env ← getEnv
  let mut pending : Array Name := #[root]
  let mut seen : Std.HashSet Name := {}
  let mut axioms : Nat := 0
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn "HeldGP14Tonelli").length > 1 || (n.toString.splitOn "RegularCut").length > 1 then
        throwError "held identifier in closure: {n}"
      let some ci := env.find? n | throwError "missing constant {n}"
      match ci with
      | .axiomInfo _ =>
        unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
          throwError "nonstandard axiom in closure: {n}"
        axioms := axioms + 1
      | _ => pure ()
      pending := pending ++ ci.type.getUsedConstants
      if let some v := ci.value? (allowOpaque := true) then
        pending := pending ++ v.getUsedConstants
  return (seen.size, axioms)

end QuantumNLS.Bind7BDEF033H01

set_option maxHeartbeats 16000000 in
open Lean Meta Elab Command in
run_cmd liftTermElabM do
  let newN := ``QuantumNLS.Bind7BDEF033H01.DEF033_bound
  let oldN := ``QuantumNLS.Def033BindingR25m.DEF033_intermediate
  let (eqv, defeq) ← QuantumNLS.Bind7BDEF033H01.bindCorrespondence oldN newN
  unless eqv do throwError "statement correspondence FAILED (eqv={eqv}, defeq={defeq})"
  let (nConst, nAx) ← QuantumNLS.Bind7BDEF033H01.transitiveAudit newN
  logInfo m!"Bind7BDEF033H01 correspondence PASS: alpha-equivalent to frozen DEF033_intermediate minus shared binder (defeq {defeq}); closure {nConst} constants, {nAx} standard axioms, no held identifiers."

#print axioms QuantumNLS.Bind7BDEF033H01.DEF033_bound

end
