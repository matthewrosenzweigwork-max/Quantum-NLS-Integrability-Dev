import QuantumNLS.DynSeedR47b
import QuantumNLS.RB7BindFinal
import QuantumNLS.RB7BindChart
import QuantumNLS.Def033LowR24m
import QuantumNLS.Def021ChartR41b
import QuantumNLS.RootIndexedMasses
import QuantumNLS.ActualModelTargetR53a
import QuantumNLS.HierarchyInputR25m
import QuantumNLS.Def044ChartR28m

/-!
# Bind7BR300B8640A01: R-300B8640 `lem:dynft-seed`, checked adapter (ready to promote, no acceptance claim)

Frozen intermediate: `QuantumNLS.DynSeedR47b.seed_intermediate` (sol_ext_b round 47; source
`QuantumNLS/DynSeedR47b.lean`, SHA-256 66bfa825bf9817d7d891bc4d0b16a58858c1a3916c36ef738243ad1b00549128).
That theorem takes an arbitrary flow `F : HigherFlows L κ` and a separate premise `flow_actions` about `F`.

This module instantiates `F` by the hierarchy-selected flow `hierFlow hκ w hw`. That flow is the higher family
in the `HierarchyConclusion` supplied by `HierarchyInputR25m.HierarchyR7B122087Input` through
`RB7BindFinal.hierarchyInputR25m_unconditional` (review record round 86 PASS). Its antecedents are discharged by
`RB7BindChart.sobolev_antecedent`, `HierarchyInputR25m.scalar_uniqueness` and `HierarchyInputR25m.scalar_moments`.
The `flow_actions` premise is then proved, not assumed:

* the hierarchy action clause (orders `r ≥ 2`) preserves every indexed mass (`ActionFlow`);
* the orders `0` and `1` in `ActualModelTargetR53a.hamFlows` are `Def024LowFlows.phaseFlow` and `transFlow`. They
  preserve every indexed mass by `Def033LowR24m.smoothClass_phase`/`smoothClass_trans` together with
  `RootIndexedMasses.masses_phase`/`masses_translation`;
* the joint flow is a fold of single steps, and `Def021ChartR41b.Chart.actions` turns equal indexed masses into equal
  chart moduli, which is exactly membership in `DynSeedClassicalR47b.torus`.

`flow_actions` holds for every time family `t : ℕ → ℝ`, so the finite time box `TimeBox R lo hi` is not used and
nothing in `flow_actions` is strengthened or weakened.

Remaining hypotheses of `dynft_seed_hierarchy`: `hκ : 0 < κ`; the printed chart `w` with `hw : PrintedChart hκ w`;
`u`, `hu : ‖physical u‖ = 1`; `R`, `lo`, `hi`; `a`, `b`, `hab`; the printed finite-angle premise `mixed`
(`MixedFinite`, eq:dynft-mixed-finite); and the single pending predecessor `PredecessorInput : DynftFullTorusInput`
(the printed R-B2E70586, `lem:dynft-full-torus`). No other input is pending.

No sorry, no admit, no native_decide, no new axiom. R-7B122087 is held for the owner ruling on the DEF-024
predecessor gate, so this module is ready-to-promote only.
-/

set_option autoImplicit false
noncomputable section

namespace QuantumNLS.Bind7BR300B8640A01

variable {L κ : ℝ} [Fact (0 < L)]

/-- The action clause of `HierarchyInputR25m.HierarchyConclusion` for one higher flow family: every order `r ≥ 2`
preserves each indexed mass of the physical class. -/
def ActionFlow (hκ : 0 < κ) (F : QuantumNLS.ActualModelTargetR53a.HigherFlows L κ) : Prop :=
  ∀ (r : ℕ) (hr : 2 ≤ r) (u : QuantumNLS.Def033HierarchyR24m.Smooth L) (s : ℝ) (n : ℤ),
    (QuantumNLS.RootIndexedMasses.masses hκ (QuantumNLS.Def033HierarchyR24m.physical
        (⟨F.Φ r s u.val, ((F.ham r hr u.val u.property).2.2 s).1⟩ :
          QuantumNLS.Def033HierarchyR24m.Smooth L))).1 n =
      (QuantumNLS.RootIndexedMasses.masses hκ (QuantumNLS.Def033HierarchyR24m.physical u)).1 n

/-- The order-zero flow `e^{-is}u` preserves every indexed mass. -/
theorem phase_flow_masses (hκ : 0 < κ) (v : QuantumNLS.Def033HierarchyR24m.Smooth L) (s : ℝ) (n : ℤ) :
    (QuantumNLS.RootIndexedMasses.masses hκ (QuantumNLS.Def033HierarchyR24m.physical
        (⟨QuantumNLS.Def024LowFlows.phaseFlow s v.val,
          QuantumNLS.Def024LowFlows.phase_smooth v.property s⟩ :
          QuantumNLS.Def033HierarchyR24m.Smooth L))).1 n =
      (QuantumNLS.RootIndexedMasses.masses hκ (QuantumNLS.Def033HierarchyR24m.physical v)).1 n := by
  have h : QuantumNLS.RootIndexedMasses.masses hκ (QuantumNLS.Def033HierarchyR24m.physical
        (⟨QuantumNLS.Def024LowFlows.phaseFlow s v.val,
          QuantumNLS.Def024LowFlows.phase_smooth v.property s⟩ :
          QuantumNLS.Def033HierarchyR24m.Smooth L)) =
      QuantumNLS.RootIndexedMasses.masses hκ (QuantumNLS.Def033HierarchyR24m.physical v) := by
    show QuantumNLS.RootIndexedMasses.masses hκ
        (QuantumNLS.PhysicalProductPreparation.smoothClass
          (QuantumNLS.Def024LowFlows.phase_smooth v.property s)) =
      QuantumNLS.RootIndexedMasses.masses hκ
        (QuantumNLS.PhysicalProductPreparation.smoothClass v.property)
    rw [QuantumNLS.Def033LowR24m.smoothClass_phase v.property s]
    exact QuantumNLS.RootIndexedMasses.masses_phase hκ _ (QuantumNLS.Def024LowFlows.norm_exp_negI s)
  rw [h]

/-- The order-one flow `u(· - s)` preserves every indexed mass. -/
theorem trans_flow_masses (hκ : 0 < κ) (v : QuantumNLS.Def033HierarchyR24m.Smooth L) (s : ℝ) (n : ℤ) :
    (QuantumNLS.RootIndexedMasses.masses hκ (QuantumNLS.Def033HierarchyR24m.physical
        (⟨QuantumNLS.Def024LowFlows.transFlow s v.val,
          QuantumNLS.Def024LowFlows.trans_smooth v.property s⟩ :
          QuantumNLS.Def033HierarchyR24m.Smooth L))).1 n =
      (QuantumNLS.RootIndexedMasses.masses hκ (QuantumNLS.Def033HierarchyR24m.physical v)).1 n := by
  have h : QuantumNLS.RootIndexedMasses.masses hκ (QuantumNLS.Def033HierarchyR24m.physical
        (⟨QuantumNLS.Def024LowFlows.transFlow s v.val,
          QuantumNLS.Def024LowFlows.trans_smooth v.property s⟩ :
          QuantumNLS.Def033HierarchyR24m.Smooth L)) =
      QuantumNLS.RootIndexedMasses.masses hκ (QuantumNLS.Def033HierarchyR24m.physical v) := by
    show QuantumNLS.RootIndexedMasses.masses hκ
        (QuantumNLS.PhysicalProductPreparation.smoothClass
          (QuantumNLS.Def024LowFlows.trans_smooth v.property s)) =
      QuantumNLS.RootIndexedMasses.masses hκ
        (QuantumNLS.PhysicalProductPreparation.smoothClass v.property)
    rw [QuantumNLS.Def033LowR24m.smoothClass_trans v.property s]
    exact QuantumNLS.RootIndexedMasses.masses_translation hκ _ (-s)
  rw [h]

/-- One step of the joint classical flow preserves every indexed mass, for every order (orders `0`, `1` are the
explicit low flows; orders `r ≥ 2` are the hierarchy action clause; orders outside `R` are the identity). -/
theorem step_masses (hκ : 0 < κ) (F : QuantumNLS.ActualModelTargetR53a.HigherFlows L κ)
    (hA : ActionFlow hκ F) (R : Finset ℕ) (r : ℕ) (s : ℝ)
    (v : QuantumNLS.Def033HierarchyR24m.Smooth L) (n : ℤ) :
    (QuantumNLS.RootIndexedMasses.masses hκ (QuantumNLS.Def033HierarchyR24m.physical
        (QuantumNLS.Def033HierarchyR24m.smoothStep
          (QuantumNLS.ActualModelTargetR53a.hamFlows F R) r s v))).1 n =
      (QuantumNLS.RootIndexedMasses.masses hκ (QuantumNLS.Def033HierarchyR24m.physical v)).1 n := by
  by_cases hr : r ∈ R
  · unfold QuantumNLS.Def033HierarchyR24m.smoothStep
    rw [dif_pos hr]
    rcases Nat.lt_or_ge r 2 with h2 | h2
    · interval_cases r
      · exact phase_flow_masses hκ v s n
      · exact trans_flow_masses hκ v s n
    · obtain ⟨k, rfl⟩ : ∃ k, r = k + 2 := ⟨r - 2, by omega⟩
      exact hA (k + 2) (by omega) v s n
  · unfold QuantumNLS.Def033HierarchyR24m.smoothStep
    rw [dif_neg hr]

/-- A finite composition of joint-flow steps preserves every indexed mass. -/
theorem fold_masses (hκ : 0 < κ) (F : QuantumNLS.ActualModelTargetR53a.HigherFlows L κ)
    (hA : ActionFlow hκ F) (R : Finset ℕ) (s : ℕ → ℝ) (l : List ℕ)
    (v : QuantumNLS.Def033HierarchyR24m.Smooth L) (n : ℤ) :
    (QuantumNLS.RootIndexedMasses.masses hκ (QuantumNLS.Def033HierarchyR24m.physical
        (l.foldr (fun r w => QuantumNLS.Def033HierarchyR24m.smoothStep
          (QuantumNLS.ActualModelTargetR53a.hamFlows F R) r (s r) w) v))).1 n =
      (QuantumNLS.RootIndexedMasses.masses hκ (QuantumNLS.Def033HierarchyR24m.physical v)).1 n := by
  induction l with
  | nil => rfl
  | cons r l ih =>
    simp only [List.foldr_cons]
    exact (step_masses hκ F hA R r (s r) _ n).trans ih

/-- The classical orbit of the joint flow stays in the torus of the physical datum (`flow_actions`, pointwise
in the time family). -/
theorem classicalOrbit_mem (hκ : 0 < κ) (F : QuantumNLS.ActualModelTargetR53a.HigherFlows L κ)
    (hA : ActionFlow hκ F) (u : QuantumNLS.Def033HierarchyR24m.Smooth L) (R : Finset ℕ) (t : ℕ → ℝ) :
    QuantumNLS.DynSeedInputR47b.classicalOrbit hκ F u R t ∈
      QuantumNLS.DynSeedClassicalR47b.torus hκ (QuantumNLS.Def033HierarchyR24m.physical u) := by
  intro j
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [(QuantumNLS.Def021ChartR41b.chart L κ hκ).actions,
    (QuantumNLS.Def021ChartR41b.chart L κ hκ).actions]
  exact fold_masses hκ F hA R t (R.sort (· ≤ ·)) u j

/-- The printed `flow_actions` premise of `DynSeedR47b.seed_intermediate`, for any action-preserving family. -/
theorem flow_actions_of (hκ : 0 < κ) (F : QuantumNLS.ActualModelTargetR53a.HigherFlows L κ)
    (hA : ActionFlow hκ F) (u : QuantumNLS.Def033HierarchyR24m.Smooth L) (R : Finset ℕ) (lo hi : ℕ → ℝ) :
    ∀ t : QuantumNLS.DynSeedInputR47b.TimeBox R lo hi,
      QuantumNLS.DynSeedInputR47b.classicalOrbit hκ F u R t.val ∈
        QuantumNLS.DynSeedClassicalR47b.torus hκ (QuantumNLS.Def033HierarchyR24m.physical u) :=
  fun t => classicalOrbit_mem hκ F hA u R t.val

/-- The shared hierarchy input, at the printed chart `w`, yields a higher flow family with the action clause. -/
theorem hierarchy_action_exists (hκ : 0 < κ)
    (w : QuantumNLS.PhysicalTensor.L2T L → QuantumNLS.REF88Chart.K)
    (hw : QuantumNLS.REF88PrintedChart.PrintedChart hκ w) :
    ∃ F : QuantumNLS.ActualModelTargetR53a.HigherFlows L κ, ActionFlow hκ F := by
  obtain ⟨Φ, hΦ, hu, hc, -, -, -, -, -, ha⟩ :=
    QuantumNLS.RB7BindFinal.hierarchyInputR25m_unconditional (L := L) hκ w hw
      (QuantumNLS.RB7BindChart.sobolev_antecedent (L := L) hκ w hw)
      (QuantumNLS.HierarchyInputR25m.scalar_uniqueness (L := L) hκ)
      (QuantumNLS.HierarchyInputR25m.scalar_moments (L := L) hκ)
  exact ⟨⟨Φ, hΦ, hu, hc⟩, ha⟩

/-- The hierarchy-selected higher flow family at the printed chart `w`
(`Classical.choose` of the shared-input existence theorem). -/
noncomputable def hierFlow (hκ : 0 < κ)
    (w : QuantumNLS.PhysicalTensor.L2T L → QuantumNLS.REF88Chart.K)
    (hw : QuantumNLS.REF88PrintedChart.PrintedChart hκ w) :
    QuantumNLS.ActualModelTargetR53a.HigherFlows L κ :=
  Classical.choose (hierarchy_action_exists hκ w hw)

/-- The hierarchy-selected flow satisfies the action clause. -/
theorem hierFlow_action (hκ : 0 < κ)
    (w : QuantumNLS.PhysicalTensor.L2T L → QuantumNLS.REF88Chart.K)
    (hw : QuantumNLS.REF88PrintedChart.PrintedChart hκ w) :
    ActionFlow hκ (hierFlow hκ w hw) :=
  Classical.choose_spec (hierarchy_action_exists hκ w hw)

/-- Same chart: every printed chart `w` is the `Φ` of the DEF-021 chart used to define `torus`, so the torus premise
of `flow_actions` is checked on exactly the chart that the hierarchy input is stated for. -/
theorem printed_chart_is_torus_chart (hκ : 0 < κ)
    (w : QuantumNLS.PhysicalTensor.L2T L → QuantumNLS.REF88Chart.K)
    (hw : QuantumNLS.REF88PrintedChart.PrintedChart hκ w) :
    w = (QuantumNLS.Def021ChartR41b.chart L κ hκ).Φ :=
  (QuantumNLS.Def044ChartR28m.printed_chart_maps hκ (QuantumNLS.Def021ChartR41b.chart L κ hκ) w hw).1

/-- **`DynSeedR47b.seed_intermediate` with the hierarchy-selected flow instantiated.** The flow argument is
`hierFlow hκ w hw`, and `flow_actions` is discharged. The only pending predecessor is `PredecessorInput`
(the printed R-B2E70586 `DynftFullTorusInput`), together with the printed finite-angle premise `mixed`. -/
theorem dynft_seed_hierarchy (hκ : 0 < κ)
    (w : QuantumNLS.PhysicalTensor.L2T L → QuantumNLS.REF88Chart.K)
    (hw : QuantumNLS.REF88PrintedChart.PrintedChart hκ w)
    (u : QuantumNLS.Def033HierarchyR24m.Smooth L)
    (hu : ‖QuantumNLS.Def033HierarchyR24m.physical u‖ = 1)
    (R : Finset ℕ) (lo hi : ℕ → ℝ) (a b : ℤ) (hab : a ≠ b)
    (mixed : QuantumNLS.DynSeedInputR47b.MixedFinite hκ (hierFlow hκ w hw) u R)
    (PredecessorInput : QuantumNLS.DynSeedInputR47b.DynftFullTorusInput hκ (hierFlow hκ w hw) u R) :
    QuantumNLS.DynSeedR47b.SeedStatement hκ (hierFlow hκ w hw) u R lo hi a b :=
  QuantumNLS.DynSeedR47b.seed_intermediate hκ (hierFlow hκ w hw) u hu R lo hi a b hab
    (flow_actions_of hκ (hierFlow hκ w hw) (hierFlow_action hκ w hw) u R lo hi) mixed PredecessorInput

open Lean Meta in
/-- Statement correspondence. Take the frozen `seed_intermediate` type. Replace its flow binder `F` by the
expression `hierFlow hκ w hw` built from the new binders `w`, `hw`, and drop the `flow_actions` binder. The result
must equal the restated type binder by binder and in the body (alpha-equivalence via `Expr.eqv`, and also defeq). -/
private def seedCorrespondence (oldN newN flowN : Name) : MetaM (Bool × Bool) := do
  let env ← getEnv
  let some oldCi := env.find? oldN | throwError "missing {oldN}"
  let some newCi := env.find? newN | throwError "missing {newN}"
  forallTelescope oldCi.type fun xs told => do
    forallTelescope newCi.type fun ys tnew => do
      unless xs.size == ys.size do
        throwError "arity mismatch: frozen {xs.size} binders, restated {ys.size}"
      let mut oldNames : Array Name := #[]
      for x in xs do
        oldNames := oldNames.push (← x.fvarId!.getDecl).userName
      let mut newNames : Array Name := #[]
      for y in ys do
        newNames := newNames.push (← y.fvarId!.getDecl).userName
      let some iF := oldNames.findIdx? (· == `F) | throwError "no F binder in frozen type"
      let some iFA := oldNames.findIdx? (· == `flow_actions) | throwError "no flow_actions binder"
      let some iHk := newNames.findIdx? (· == `hκ) | throwError "no hκ binder in restated type"
      let some iw := newNames.findIdx? (· == `w) | throwError "no w binder in restated type"
      let some ihw := newNames.findIdx? (· == `hw) | throwError "no hw binder in restated type"
      let flowE := mkAppN (mkConst flowN) #[ys[0]!, ys[1]!, ys[2]!, ys[iHk]!, ys[iw]!, ys[ihw]!]
      let newIdx (nm : Name) : Option Nat := newNames.findIdx? (· == nm)
      -- jmap.[i] is the restated binder index that frozen binder i maps to (none for F and flow_actions)
      let mut jmap : Array (Option Nat) := #[]
      let mut fromArr : Array Expr := #[]
      let mut toArr : Array Expr := #[]
      let mut used : Array Nat := #[]
      for i in [0:xs.size] do
        if i == iF then
          jmap := jmap.push none
          fromArr := fromArr.push xs[i]!
          toArr := toArr.push flowE
        else if i == iFA then
          jmap := jmap.push none
        else
          let j : Nat ← if i < 3 then pure i else do
            match newIdx oldNames[i]! with
            | some j => pure j
            | none => throwError "no restated binder for {oldNames[i]!}"
          jmap := jmap.push (some j)
          used := used.push j
          fromArr := fromArr.push xs[i]!
          toArr := toArr.push ys[j]!
      -- binder-by-binder comparison of the surviving frozen binders against the restated ones
      let mut binderOk := true
      for i in [0:xs.size] do
        unless i == iF || i == iFA do
          let tOld ← inferType xs[i]!
          let tOldM := tOld.replaceFVars fromArr toArr
          let some j := jmap[i]! | throwError "internal: unmapped binder {oldNames[i]!}"
          let tNew ← inferType ys[j]!
          unless tOldM == tNew do binderOk := false
      -- the restated binders are exactly the surviving frozen binders plus w and hw, each once
      let allNew := (used.push iw).push ihw
      let sorted := allNew.qsort (fun p q => decide (p < q))
      unless sorted == (List.range ys.size).toArray do binderOk := false
      let concl := told.replaceFVars fromArr toArr
      let eqv := concl == tnew
      let defeq ← isDefEq concl tnew
      return (binderOk && eqv, binderOk && defeq)

open Lean Meta in
/-- Transitive closure of a root constant. Held names and non-standard axioms are rejected. Also reports whether a
given provenance constant lies in the closure. -/
private def transitiveAudit (root prov : Name) : MetaM (Nat × Nat × Bool) := do
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
  return (seen.size, axioms, seen.contains prov)

end QuantumNLS.Bind7BR300B8640A01

set_option maxHeartbeats 16000000 in
open Lean Meta Elab Command in
run_cmd liftTermElabM do
  let newN := ``QuantumNLS.Bind7BR300B8640A01.dynft_seed_hierarchy
  let oldN := ``QuantumNLS.DynSeedR47b.seed_intermediate
  let (eqv, defeq) ← QuantumNLS.Bind7BR300B8640A01.seedCorrespondence oldN newN
    ``QuantumNLS.Bind7BR300B8640A01.hierFlow
  unless eqv do throwError "statement correspondence FAILED (eqv={eqv}, defeq={defeq})"
  let (nConst, nAx, hasProv) ← QuantumNLS.Bind7BR300B8640A01.transitiveAudit newN
    ``QuantumNLS.RB7BindFinal.hierarchyInputR25m_unconditional
  unless hasProv do throwError "hierarchy provenance constant not in closure"
  logInfo m!"Bind7BR300B8640A01 correspondence PASS: alpha-equivalent to frozen seed_intermediate with F instantiated by hierFlow hκ w hw and flow_actions removed (defeq {defeq}); closure {nConst} constants, {nAx} standard axioms, no held identifiers, hierarchy provenance present."

#print axioms QuantumNLS.Bind7BR300B8640A01.dynft_seed_hierarchy
#print axioms QuantumNLS.Bind7BR300B8640A01.hierFlow_action
#print axioms QuantumNLS.Bind7BR300B8640A01.printed_chart_is_torus_chart

end
