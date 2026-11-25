import QuantumNLS.WindowBindingR46b
import QuantumNLS.RB7BindFinal

/-!
# Bind7BE59628C9H01: R-E59628C9 (prop:window) binding, ready to promote

Frozen intermediate: `QuantumNLS.WindowAssemblyR46b.window_intermediate`
(sol_ext_b round 46; source `QuantumNLS/WindowBindingR46b.lean`,
SHA-256 17cbae60b9e2f09706faff764435286b4b9773353df8e22a602399e6d494c990).

Its only predecessor argument `HierarchyInput : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ`
is the shared R-7B122087 type exactly. It is discharged by
`QuantumNLS.RB7BindFinal.hierarchyInputR25m_unconditional` (review record round 86 PASS).
No adapter is needed.

Remaining hypothesis: `hκ : 0 < κ` only. This module makes no acceptance claim;
R-7B122087 is held for the owner ruling on the DEF-024 predecessor gate.
-/
set_option autoImplicit false

namespace QuantumNLS.Bind7BE59628C9H01

variable {L κ : ℝ} [Fact (0 < L)]

/-- R-E59628C9 `prop:window` (`WindowInput`), with the shared hierarchy input discharged. -/
theorem window_bound (hκ : 0 < κ) : QuantumNLS.Prop025OInputs.WindowInput (L := L) hκ :=
  QuantumNLS.WindowAssemblyR46b.window_intermediate hκ
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

end QuantumNLS.Bind7BE59628C9H01

set_option maxHeartbeats 16000000 in
open Lean Meta Elab Command in
run_cmd liftTermElabM do
  let newN := ``QuantumNLS.Bind7BE59628C9H01.window_bound
  let oldN := ``QuantumNLS.WindowAssemblyR46b.window_intermediate
  let (eqv, defeq) ← QuantumNLS.Bind7BE59628C9H01.bindCorrespondence oldN newN
  unless eqv do throwError "statement correspondence FAILED (eqv={eqv}, defeq={defeq})"
  let (nConst, nAx) ← QuantumNLS.Bind7BE59628C9H01.transitiveAudit newN
  logInfo m!"Bind7BE59628C9H01 correspondence PASS: alpha-equivalent to frozen window_intermediate minus shared binder (defeq {defeq}); closure {nConst} constants, {nAx} standard axioms, no held identifiers."

#print axioms QuantumNLS.Bind7BE59628C9H01.window_bound
