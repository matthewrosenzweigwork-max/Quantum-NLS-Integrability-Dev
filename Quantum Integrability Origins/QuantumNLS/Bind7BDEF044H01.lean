import QuantumNLS.Def044PhysicalBindingR54a
import QuantumNLS.RB7BindFinal

/-!
# Bind7BDEF044H01: DEF-044 binding, ready to promote

Frozen intermediate: `QuantumNLS.Def044PhysicalBindingR54a.DEF044_physical_intermediate`
(review record round 54, R54a physical spectral assembly; source `QuantumNLS/Def044PhysicalBindingR54a.lean`,
SHA-256 8282320a7b831d65ed25a60edeb9e173fecfe3a287bb3a36ab76a98ff8d3c362; the spectral witnesses
come from `QuantumNLS.Def044PhysicalSpectralR54a.spectral`, which has no pending predecessor binder).

Its only predecessor argument `HierarchyR7B122087Input : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ`
is the shared R-7B122087 type exactly, and it is passed on to the R28m entry point
`Def044BindingR28m.DEF044_intermediate` with the same type. It is discharged here by
`QuantumNLS.RB7BindFinal.hierarchyInputR25m_unconditional` (review record round 86 PASS). No adapter is needed.

The conclusion is a `structure` (`Def044BindingR26m.MixedInterface`), so this binding is a `def`, not a `theorem`.
Remaining hypotheses: `hκ : 0 < κ`, `u : Smooth L`, `hu : ‖physical u‖ = 1`.
This module makes no acceptance claim; R-7B122087 is held for the owner ruling on the DEF-024 predecessor gate.
-/
set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace QuantumNLS.Bind7BDEF044H01

variable {L κ : ℝ} [Fact (0 < L)]

/-- DEF-044 mixed interface at a physical unit profile `u`, with the shared hierarchy input discharged. -/
noncomputable def DEF044_bound (hκ : 0 < κ) (u : QuantumNLS.Def033HierarchyR24m.Smooth L)
    (hu : ‖QuantumNLS.Def033HierarchyR24m.physical u‖ = 1) :
    QuantumNLS.Def044BindingR26m.MixedInterface hκ u hu :=
  QuantumNLS.Def044PhysicalBindingR54a.DEF044_physical_intermediate hκ u hu
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

end QuantumNLS.Bind7BDEF044H01

set_option maxHeartbeats 16000000 in
open Lean Meta Elab Command in
run_cmd liftTermElabM do
  let newN := ``QuantumNLS.Bind7BDEF044H01.DEF044_bound
  let oldN := ``QuantumNLS.Def044PhysicalBindingR54a.DEF044_physical_intermediate
  let (eqv, defeq) ← QuantumNLS.Bind7BDEF044H01.bindCorrespondence oldN newN
  unless eqv do throwError "statement correspondence FAILED (eqv={eqv}, defeq={defeq})"
  let (nConst, nAx) ← QuantumNLS.Bind7BDEF044H01.transitiveAudit newN
  logInfo m!"Bind7BDEF044H01 correspondence PASS: alpha-equivalent to frozen DEF044_physical_intermediate minus shared binder (defeq {defeq}); closure {nConst} constants, {nAx} standard axioms, no held identifiers."

#print axioms QuantumNLS.Bind7BDEF044H01.DEF044_bound
