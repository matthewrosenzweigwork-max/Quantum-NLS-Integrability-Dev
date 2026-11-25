import QuantumNLS.AuditGapsS01Headline
import QuantumNLS.DynamicGaugeFinalR35m

/-!
# AuditGapsFinalS02: FINAL BINDING of R-10EE6421 `lem:audit-gaps`, no named theorem inputs

PRINTED SOURCE: `source-text/chapters/core/weighted_actions_and_same_gauge_dynamics.tex`, lines 261-294
(`\begin{lemma}[Actual adjacent differences from these dynamic symbols]`, `\ReportID{R-10EE6421}`,
`\label{lem:audit-gaps}`).

PRINTED STATEMENT: "For each fixed positive-action donor-receiver pair and every fixed charge order, the
rebuilt-gauge dynamical symbols imply the master's receiver-minus-donor adjacent-difference convergence in
probability under the original product law. Finite families converge jointly. No moment convergence follows
from this argument."

This module instantiates the printed-form theorem `AuditGapsS01Headline.audit_gaps_printed` (author module
of the R-10EE6421 node, terra_review r258 CONDITIONAL PASS) at the accepted chain's fixed objects:

* `F` : the fixed smooth hierarchy flows of Definition 24, `ReconstructionR33m.flows hκ H` with the shared
  hierarchy theorem `H = RB7BindFinal.hierarchyInputR25m_unconditional hκ`
  (`DynamicGaugeFinalR35m.hierarchy`, the hierarchy supplied by the R-7B122087 binding `RB7BindFinal`);
* `g` : the single rebuilt gauge of R-8362E5EB, `DynamicGaugeFinalR35m.gauge hκ`, i.e. the physical basis gauge
  of the R-D51987CA named pair `(RetargetSelectionR49b.sectorStage, RetargetSelectionR49b.sectorGauge)`;
* the rebuilt-gauge dynamical symbols (formerly the named input `ReconstructionR33m.RD8362E5EBInput hκ F g`):
  `DynamicGaugeFinalR35m.audit_dynamic_gauge hκ` (sol_multi r35 final binding of R-8362E5EB, no named input);
* `D` : DEF-033 at the printed chart `w = (Def021ChartR41b.chart L κ hκ).Φ`,
  `Bind7BDEF033H02.DEF033_package hκ w (ActualModelBindingR53a.printed_chart hκ)`, the REALIZED DEF-033 package
  (printed clauses of definitions.tex:199-203); its selected active frequencies `D.ω` are the printed
  `ω_{r,n}(u)`.

The remaining hypotheses are exactly the printed ones: the coupling `hκ : 0 < κ` (with the period fact
`0 < L`), a smooth unit state `u`, a charge order `r`, donor/receiver labels `a b` of positive action
(`ha hb`), and the (arbitrary) missing-donor convention `missing` that the printed definition
`DifferenceLimit` carries.  No hypothesis of the shape `RD8362E5EBInput`, `DEF033Package`, a gauge, a flow
family or a hierarchy input remains.

No acceptance claim.  Scope239, pins, frozen modules untouched.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
noncomputable section
open Filter Topology MeasureTheory

namespace QuantumNLS.AuditGapsFinalS02
open QuantumNLS.BetheLabels QuantumNLS.BetheOccupationGauge
open QuantumNLS.TerraMultiRound12Definitions QuantumNLS.Def033CoreR24m
open QuantumNLS.ActualModelTargetR53a (HigherFlows)
open QuantumNLS.Def033HierarchyR24m (Smooth physical)

variable {L κ : ℝ} [Fact (0 < L)]

/-- The fixed hierarchy flows of the accepted chain. -/
abbrev F (hκ : 0 < κ) : HigherFlows L κ :=
  ReconstructionR33m.flows hκ (DynamicGaugeFinalR35m.hierarchy (L := L) hκ)

/-- The single rebuilt gauge of the accepted chain (R-8362E5EB at the R-D51987CA named pair). -/
abbrev g (hκ : 0 < κ) : Gauge := DynamicGaugeFinalR35m.gauge (L := L) hκ

/-- The realized DEF-033 package at the printed chart. -/
abbrev D (hκ : 0 < κ) :
    Bind7BDEF033H02.DEF033Package hκ (Def021ChartR41b.chart L κ hκ).Φ :=
  Bind7BDEF033H02.DEF033_package hκ (Def021ChartR41b.chart L κ hκ).Φ
    (ActualModelBindingR53a.printed_chart (L := L) hκ)

/-- **R-10EE6421 `lem:audit-gaps`, final binding.** For each fixed positive-action donor-receiver pair
`(a, b)` and every fixed charge order `r`, the receiver-minus-donor adjacent differences converge in
probability, under the original product Born law, to `ω_{r,b}(u) - ω_{r,a}(u)` (the DEF-033 limit
`DifferenceLimit`, for an arbitrary missing-donor convention). -/
theorem audit_gaps_final (hκ : 0 < κ) (u : Smooth L) (hu : ‖physical u‖ = 1) (r : ℕ) (a b : ℤ)
    (ha : 0 < (QuantumNLS.RootIndexedMasses.masses hκ (physical u)).1 a)
    (hb : 0 < (QuantumNLS.RootIndexedMasses.masses hκ (physical u)).1 b)
    (missing : ∀ N, MArr (N + 1) → ℝ) :
    DifferenceLimit hκ (physical u) hu r a b ((D (L := L) hκ).ω r u) missing :=
  AuditGapsS01Headline.audit_gaps_printed hκ (F (L := L) hκ) (g (L := L) hκ)
    (DynamicGaugeFinalR35m.audit_dynamic_gauge (L := L) hκ) (D (L := L) hκ) u hu r a b ha hb missing

/-- **Finite families converge jointly** (printed: "Finite families converge jointly."). -/
theorem audit_gaps_final_joint (hκ : 0 < κ) (u : Smooth L) (hu : ‖physical u‖ = 1)
    {ι : Type} [Fintype ι] (r : ι → ℕ) (a b : ι → ℤ)
    (ha : ∀ i, 0 < (QuantumNLS.RootIndexedMasses.masses hκ (physical u)).1 (a i))
    (hb : ∀ i, 0 < (QuantumNLS.RootIndexedMasses.masses hκ (physical u)).1 (b i))
    (missing : ι → ∀ N, MArr (N + 1) → ℝ) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun N => originalBorn hκ (physical u) hu N
      {m | ∃ i, ε < |withMissing L κ (N + 1) (r i) (a i) (b i) (missing i N) m -
        target ((D (L := L) hκ).ω (r i) u) (a i) (b i)|}) atTop (𝓝 0) :=
  AuditGapsS01Headline.audit_gaps_joint hκ (F (L := L) hκ) (g (L := L) hκ)
    (DynamicGaugeFinalR35m.audit_dynamic_gauge (L := L) hκ) (D (L := L) hκ) u hu r a b ha hb
    missing ε hε

end QuantumNLS.AuditGapsFinalS02

#print axioms QuantumNLS.AuditGapsFinalS02.audit_gaps_final
#print axioms QuantumNLS.AuditGapsFinalS02.audit_gaps_final_joint

/-! Type comparison against `audit_gaps_printed` / `audit_gaps_joint` at the chain's `F`, `g`, `hD`, `D`;
binder audit (no named theorem input among the hypotheses); closure audit (standard axioms only, held
identifiers `HeldGP14Tonelli`, `RegularCut` absent; the discharging theorems ARE in the closure). -/
set_option maxHeartbeats 24000000 in
open Lean Meta Elab Command in
run_cmd liftTermElabM do
  let final ← getConstInfo ``QuantumNLS.AuditGapsFinalS02.audit_gaps_final
  let joint ← getConstInfo ``QuantumNLS.AuditGapsFinalS02.audit_gaps_final_joint
  -- (1) binders of the final headlines
  let binders (ty : Expr) : MetaM (Array (Name × Expr)) :=
    forallTelescope ty fun xs _ => do
      let mut out := #[]
      for x in xs do
        let d ← x.fvarId!.getDecl
        out := out.push (d.userName, ← instantiateMVars d.type)
      return out
  let bs ← binders final.type
  let bj ← binders joint.type
  logInfo m!"FINAL_BINDERS {bs.map (·.1)}"
  logInfo m!"JOINT_BINDERS {bj.map (·.1)}"
  let forbidden : List Name :=
    [``QuantumNLS.ReconstructionR33m.RD8362E5EBInput, ``QuantumNLS.Bind7BDEF033H02.DEF033Package,
     ``QuantumNLS.ActualModelTargetR53a.HigherFlows, ``QuantumNLS.BetheOccupationGauge.Gauge,
     ``QuantumNLS.HierarchyInputR25m.HierarchyR7B122087Input]
  for (n, ty) in bs ++ bj do
    let used := ty.getUsedConstants
    for f in forbidden do
      if used.contains f then throwError "binder {n} mentions named input/context {f}"
  -- (2) type comparison with the printed-form theorems at the chain's F, g, hD, D
  let app (n : Name) (xs : Array Expr) : Expr := mkAppN (mkConst n) xs
  forallTelescope final.type fun domain expected => do
    let pre := domain.extract 0 4   -- L, κ, Fact, hκ
    let rest := domain.extract 4 domain.size
    let F := app ``QuantumNLS.AuditGapsFinalS02.F pre
    let g := app ``QuantumNLS.AuditGapsFinalS02.g pre
    let hD := app ``QuantumNLS.DynamicGaugeFinalR35m.audit_dynamic_gauge pre
    let Dd := app ``QuantumNLS.AuditGapsFinalS02.D pre
    let printed := app ``QuantumNLS.AuditGapsS01Headline.audit_gaps_printed
      (pre ++ #[F, g, hD, Dd] ++ rest)
    unless ← isDefEq (← inferType printed) expected do
      throwError "audit_gaps_final differs from the instantiated audit_gaps_printed"
    logInfo "TYPE_COMPARISON_PRINTED PASS (audit_gaps_final is definitionally the instantiated audit_gaps_printed)"
  forallTelescope joint.type fun domain expected => do
    let pre := domain.extract 0 4
    let rest := domain.extract 4 domain.size
    let F := app ``QuantumNLS.AuditGapsFinalS02.F pre
    let g := app ``QuantumNLS.AuditGapsFinalS02.g pre
    let hD := app ``QuantumNLS.DynamicGaugeFinalR35m.audit_dynamic_gauge pre
    let Dd := app ``QuantumNLS.AuditGapsFinalS02.D pre
    let jointT := app ``QuantumNLS.AuditGapsS01Headline.audit_gaps_joint
      (pre ++ #[F, g, hD, Dd] ++ rest)
    unless ← isDefEq (← inferType jointT) expected do
      throwError "audit_gaps_final_joint differs from the instantiated audit_gaps_joint"
    logInfo "TYPE_COMPARISON_JOINT PASS (audit_gaps_final_joint is definitionally the instantiated audit_gaps_joint)"
  -- (3) closure audit
  let env ← getEnv
  let roots : Array Name := #[``QuantumNLS.AuditGapsFinalS02.audit_gaps_final,
    ``QuantumNLS.AuditGapsFinalS02.audit_gaps_final_joint]
  let mut pending : Array Name := roots
  let mut seen : Std.HashSet Name := {}
  let mut axioms : Std.HashSet Name := {}
  let mut heldHits : Array Name := #[]
  let mut sawNames : Array Name := #[]
  let watch : List Name := [``QuantumNLS.DynamicGaugeFinalR35m.audit_dynamic_gauge,
    ``QuantumNLS.RB7BindFinal.hierarchyInputR25m_unconditional,
    ``QuantumNLS.Bind7BDEF033H02.DEF033_package,
    ``QuantumNLS.AuditGapsS01Headline.audit_gaps_printed]
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn "HeldGP14Tonelli").length > 1 ||
          n.components.any (fun c => c.toString == "RegularCut") ||
          (n.toString.splitOn "RegularCut").length > 1 then
        heldHits := heldHits.push n
      if watch.contains n then sawNames := sawNames.push n
      let some ci := env.find? n | throwError "Missing dependency {n}"
      if let .axiomInfo _ := ci then
        unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
          throwError "Nonstandard axiom {n}"
        axioms := axioms.insert n
      pending := pending ++ ci.type.getUsedConstants
      if let some v := ci.value? (allowOpaque := true) then
        pending := pending ++ v.getUsedConstants
  unless heldHits.isEmpty do throwError "Held identifiers in closure: {heldHits}"
  unless sawNames.size == watch.length do
    throwError "Expected discharging theorems not all in closure: {sawNames}"
  logInfo m!"AXIOM_AUDIT PASS constants={seen.size} axioms={axioms.toList} heldHits={heldHits} discharging_in_closure={sawNames}"
