import QuantumNLS.AuditWeightedBindingR25m
import QuantumNLS.RB7BindFinal

/-!
# Bind7B115CAA16H01: R-115CAA16 (lem:audit-weighted) binding, ready to promote

Frozen intermediate: `QuantumNLS.AuditWeightedBindingR25m.audit_weighted_intermediate`
(sol_multi round 25, source `QuantumNLS/AuditWeightedBindingR25m.lean`,
SHA-256 0e1792e8af2d0298fa6bfbcf60e2e3f6d095b3bd908e4330420a5a79a69fecaf; its analytic content is the
review record round 50 `AuditWeightedAssemblyR50a.audit_weighted_intermediate`).

Its only predecessor argument `HierarchyR7B122087Input : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ`
is the shared R-7B122087 type exactly. The analytic proof does not use it. It is discharged here by
`QuantumNLS.RB7BindFinal.hierarchyInputR25m_unconditional` (review record round 86 PASS).
No adapter is needed.

Remaining hypotheses: `hκ : 0 < κ`, `hf : SmoothPeriodic L f`, `hu : ‖smoothL2 hf‖ = 1`.
This module makes no acceptance claim; R-7B122087 is held for the owner ruling on the DEF-024 predecessor gate.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory Filter Topology
open scoped BigOperators
namespace QuantumNLS.Bind7B115CAA16H01
open QuantumNLS.PhysicalTensor QuantumNLS.BetheLabels
open QuantumNLS.EmpiricalRapidity QuantumNLS.BulkResponseActual
open QuantumNLS.BetheCoefficientTransform
open QuantumNLS.ClassicalCharges QuantumNLS.SmoothScalarMomentsPhysical
open QuantumNLS.CommonBethePacket
open QuantumNLS.AuditWeightedProbabilityR49a QuantumNLS.AuditWeightedSeriesR49a
open QuantumNLS.AuditWeightedValuesR50a QuantumNLS.AuditWeightedTightR50a
open QuantumNLS.AuditWeightedSelectionR50a QuantumNLS.AuditWeightedCommonPacketR50a
variable {L κ : ℝ} [Fact (0 < L)] {f : ℝ → ℂ}

/-- R-115CAA16 `lem:audit-weighted`: the frozen R50a conclusion verbatim, with the shared
hierarchy input discharged. -/
theorem audit_weighted_bound (hκ : 0 < κ) (hf : SmoothPeriodic L f)
    (hu : ‖smoothL2 hf‖=1) :
    (∀ p : ℝ, 0 ≤ p → ∀ ε : ℝ, 0 < ε →
      Tendsto (fun N => bornMeasure (physBasis L hκ N) (smoothL2 hf) hu
        {m | ε < error hκ (smoothL2 hf) p N m}) atTop (𝓝 0)) ∧
    (∀ r : ℕ, QuantumNLS.BornConvergence.TendstoInProbability
      (fun N => bornMeasure (physBasis L hκ N) (smoothL2 hf) hu)
      (fun N m => QuantumNLS.BetheSpectralCharges.eigenvalue L N (κ/N) r m/(N : ℝ))
      (charge L κ f (r+1)).re) ∧
    ∃ P : (N : ℕ) → Packet (physBasis L hκ N),
      Tendsto (fun N => ‖vector (P N)-productVec L N (smoothL2 hf)‖) atTop (𝓝 0) ∧
      (∀ r ε, 0 < ε → ∀ᶠ N in atTop, ∀ m ∈ support (P N),
        |QuantumNLS.BetheSpectralCharges.eigenvalue L N (κ/N) r m/(N : ℝ)-(charge L κ f (r+1)).re| ≤ ε) ∧
      (∀ p : ℝ, 0 ≤ p → ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ m ∈ support (P N),
        error hκ (smoothL2 hf) p N m ≤ ε) ∧
      ∀ N (ev : MArr N → ℝ), vector (P N) ∈
        (QuantumNLS.BetheSpectralCharges.multiplier (physBasis L hκ N) ev).domain :=
  QuantumNLS.AuditWeightedBindingR25m.audit_weighted_intermediate hκ hf hu
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

end QuantumNLS.Bind7B115CAA16H01

set_option maxHeartbeats 16000000 in
open Lean Meta Elab Command in
run_cmd liftTermElabM do
  let newN := ``QuantumNLS.Bind7B115CAA16H01.audit_weighted_bound
  let oldN := ``QuantumNLS.AuditWeightedBindingR25m.audit_weighted_intermediate
  let (eqv, defeq) ← QuantumNLS.Bind7B115CAA16H01.bindCorrespondence oldN newN
  unless eqv do throwError "statement correspondence FAILED (eqv={eqv}, defeq={defeq})"
  let (nConst, nAx) ← QuantumNLS.Bind7B115CAA16H01.transitiveAudit newN
  logInfo m!"Bind7B115CAA16H01 correspondence PASS: alpha-equivalent to frozen audit_weighted_intermediate minus shared binder (defeq {defeq}); closure {nConst} constants, {nAx} standard axioms, no held identifiers."

#print axioms QuantumNLS.Bind7B115CAA16H01.audit_weighted_bound

end
