import QuantumNLS.Prop025ProvenanceR59a
import QuantumNLS.Prop025OLow
import QuantumNLS.Prop021FinalR135
import QuantumNLS.Prop021AssemblyR131
import QuantumNLS.Prop022BPairInput
import QuantumNLS.Prop024WIdent
import QuantumNLS.Bind7BE59628C9H01
import QuantumNLS.Bind7BDEF044H02
import QuantumNLS.RB7BindFinal

/-! # PROP-025 `thm:MP-mixed`: final binding (opus_tensor, R01)

Source: `source-text/chapters/propagation/mixed_propagation.tex`, sha256
`24ab083b54ff60951edb92acc0c86cfcde5274bfe6a0a875985ce19d9a6e69df`, lines 68–93.

The headline `prop025_final` is the strengthened fixed-packet statement
`Prop025ProvenanceR59a.PROP025WithPacket hκ` (review record R59a, reviewed review record r99): the error
sequence is `fixedZeta hκ u hu I`, which comes only from the fixed finite-action packet (lines 88–89).
It has NO named theorem input; its only hypothesis is `hκ : 0 < κ`. The DEF-044 interface stays the
printed definitional parameter `M : Def044BindingR26m.MixedInterface hκ u hu` ("Assume Definition
def:PF-mixed-interfaces"), exactly as in the reviewed `Prop025OLow.prop025` and R59a.

The two former named inputs are discharged by accepted theorems:
* `Prop025OInputs.Prop021Input` (the torus form of PROP-021) by `prop021_torus`
  `= Prop021AssemblyR131.prop021 pair_family remainder_physical`, where `pair_family` is the accepted
  PROP-022 corollary `Prop022BPairInput.Prop022PairInput_of_general` (its `.1`) and `remainder_physical`
  is built from the accepted PROP-024 headline `Prop024FinalR135.prop024` through the public
  `Prop021FinalR135.remainder_torus`. This is the same assembly term that the accepted PROP-021 proof
  `Prop021FinalR135.prop021_in_chart` uses (checked below). The alternative route with
  `Prop024WIdent.prop024RemainderInput_holds` is also given (`prop021_torus_via_WIdent`).
* `Prop025OInputs.WindowInput hκ` (R-E59628C9) by `Bind7BE59628C9H01.window_bound hκ`.

Consequences: the R56a consumer form (`prop025_final_R56a`), the reviewed OLow route
(`prop025_final_OLow`), the realized DEF-044 interface `Bind7BDEF044H02.DEF044_final`
(`prop025_at_DEF044`), the actual-model form of `Prop025OLow.prop025_actual` with the accepted
hierarchy `RB7BindFinal.hierarchyInputR25m_unconditional` (`prop025_actual_final`), and the printed
"In particular" convergence (`prop025_convergence`).

No frozen module is edited. No sorry, admit, axiom or native_decide. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section
open scoped Topology
open Filter

namespace QuantumNLS.Prop025FinalR01

open Def033HierarchyR24m (Smooth physical)
open ActualModelTargetR53a (higher)

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

/-! ## PROP-021 (torus form), from the accepted PROP-022 and PROP-024 -/

/-- The universal PROP-022 pair family, from the accepted `Prop022PairInput_of_general`
(verbatim the private `pair_family` of the accepted `Prop021FinalR135`). -/
theorem pair_family : Prop021AssemblyR131.Prop022PairFamily (L := L) := by
  intro A M hA hM K hK hs u₀ T P hP
  exact (Prop022BPairInput.Prop022PairInput_of_general K M A hM hA hK hs u₀ T P hP).1

/-- The physical remainder input, from the accepted PROP-024 headline `Prop024FinalR135.prop024`
(the term of the accepted `Prop021FinalR135.prop021_in_chart`). -/
theorem remainder_physical : Prop021RemainderInputR131.Prop024RemainderInput (L := L) :=
  fun A hA => ⟨Prop024FinalH1.printedConstant A, Prop024FinalH1.printedConstant_nonneg A,
    Prop021FinalR135.remainder_torus Prop024FinalR135.prop024 A hA⟩

/-- **`Prop025OInputs.Prop021Input`, discharged.** -/
theorem prop021_torus : Prop025OInputs.Prop021Input (L := L) :=
  Prop021AssemblyR131.prop021 pair_family remainder_physical

/-- The same proposition through the alternative remainder `Prop024WIdent.prop024RemainderInput_holds`. -/
theorem prop021_torus_via_WIdent : Prop025OInputs.Prop021Input (L := L) :=
  Prop021AssemblyR131.prop021 pair_family Prop024WIdent.prop024RemainderInput_holds

/-! ## R-E59628C9 -/

/-- **`Prop025OInputs.WindowInput hκ`, discharged** by the accepted binding. -/
theorem window (hκ : 0 < κ) : Prop025OInputs.WindowInput (L := L) hκ :=
  Bind7BE59628C9H01.window_bound hκ

/-! ## Headline -/

/-- **PROP-025 `thm:MP-mixed` (final).** For every smooth unit profile `u`, every DEF-044 mixed
interface `M` at `u`, and every finite `I ⊆ ℤ`: the fixed-packet sequence `ζ = fixedZeta hκ u hu I`
tends to `0`, vanishes when `I = ∅`, and for every finite `R ⊆ ℕ` (orders `0, 1` included), rank `k`
and nonnegative boxes `Θ, T` there is `A ≥ 0` with the eq:MP-main estimate for all large `N`. -/
theorem prop025_final (hκ : 0 < κ) : Prop025ProvenanceR59a.PROP025WithPacket (L := L) hκ :=
  Prop025ProvenanceR59a.prop025_intermediate hκ prop021_torus (window hκ)

/-- The headline implies the R56a consumer form (`MainEstimate` for every fixed box). -/
theorem prop025_final_R56a (hκ : 0 < κ) : ActualModelCorollaryR56a.PROP025Input (L := L) hκ :=
  Prop025ProvenanceR59a.to_PROP025Input hκ (prop025_final hκ)

/-- The same R56a form through the reviewed OLow headline (cross-check of the two routes). -/
theorem prop025_final_OLow (hκ : 0 < κ) : ActualModelCorollaryR56a.PROP025Input (L := L) hκ :=
  Prop025OLow.prop025 hκ prop021_torus (window hκ)

/-- The earlier R53a consumer form also follows. -/
theorem prop025_final_R53a (hκ : 0 < κ) : ActualModelCorollaryR53a.PROP025Input (L := L) hκ :=
  Prop025ProvenanceR59a.to_R53a_PROP025Input hκ (prop025_final hκ)

/-- At the realized DEF-044 interface `Bind7BDEF044H02.DEF044_final` (fixed packet). -/
theorem prop025_at_DEF044_packet (hκ : 0 < κ) (u : Smooth L) (hu : ‖physical u‖ = 1)
    (I : Finset ℤ) :
    Tendsto (Prop025ProvenanceR59a.fixedZeta hκ u hu I) atTop (𝓝 0) ∧
      (I = ∅ → ∀ N, Prop025ProvenanceR59a.fixedZeta hκ u hu I N = 0) ∧
      ∀ (R : Finset ℕ) (k : ℕ) (Θ : ℤ → ℝ) (T : ℕ → ℝ),
        (∀ n ∈ I, 0 ≤ Θ n) → (∀ r ∈ R, 0 ≤ T r) →
        ∃ A : ℝ, 0 ≤ A ∧ ActualModelCorollaryR53a.EstimateWithZeta hκ
          (Bind7BDEF044H02.DEF044_final hκ u hu).mixed.chart.chart
          (higher (Bind7BDEF044H02.DEF044_final hκ u hu).mixed.dynamics.hierarchy)
          u I R k Θ T A (Prop025ProvenanceR59a.fixedZeta hκ u hu I) :=
  prop025_final hκ u hu (Bind7BDEF044H02.DEF044_final hκ u hu).mixed I

/-- At the realized DEF-044 interface, R56a form. -/
theorem prop025_at_DEF044 (hκ : 0 < κ) (u : Smooth L) (hu : ‖physical u‖ = 1)
    (I : Finset ℤ) (R : Finset ℕ) (k : ℕ) (Θ : ℤ → ℝ) (T : ℕ → ℝ)
    (hΘ : ∀ n ∈ I, 0 ≤ Θ n) (hT : ∀ r ∈ R, 0 ≤ T r) :
    ActualModelCorollaryR53a.MainEstimate hκ (Bind7BDEF044H02.DEF044_final hκ u hu).mixed.chart.chart
      (higher (Bind7BDEF044H02.DEF044_final hκ u hu).mixed.dynamics.hierarchy) u I R k Θ T :=
  prop025_final_R56a hκ u hu (Bind7BDEF044H02.DEF044_final hκ u hu).mixed I R k Θ T hΘ hT

/-- `Prop025OLow.prop025_actual` with both named inputs discharged: the actual chart and the actual
hierarchy built from the accepted R-7B122087 input. -/
theorem prop025_actual_final (hκ : 0 < κ)
    (u : Smooth L) (hu : ‖physical u‖ = 1) (I : Finset ℤ) (R : Finset ℕ) (k : ℕ) (Θ : ℤ → ℝ)
    (T : ℕ → ℝ) (hΘ : ∀ n ∈ I, 0 ≤ Θ n) (hT : ∀ r ∈ R, 0 ≤ T r) :
    ActualModelCorollaryR53a.MainEstimate hκ (ActualModelBindingR53a.chart (L := L) hκ)
      (higher (ActualModelBindingR53a.hierarchy_intermediate hκ
        (RB7BindFinal.hierarchyInputR25m_unconditional hκ)))
      u I R k Θ T :=
  ActualModelCorollaryR56a.cor_MP_actual_model_intermediate hκ (prop025_final_R56a hκ)
    (RB7BindFinal.hierarchyInputR25m_unconditional hκ) u hu I R k Θ T hΘ hT

/-- The printed "In particular": the left side tends to zero whenever `e_N → 0`. -/
theorem prop025_convergence (hκ : 0 < κ) (u : Smooth L) (hu : ‖physical u‖ = 1)
    (M : Def044BindingR26m.MixedInterface hκ u hu)
    (I : Finset ℤ) (R : Finset ℕ) (k : ℕ) (Θ : ℤ → ℝ) (T : ℕ → ℝ)
    (hΘ : ∀ n ∈ I, 0 ≤ Θ n) (hT : ∀ r ∈ R, 0 ≤ T r)
    (ψ : ∀ N : ℕ, BetheCoefficientTransform.HN L (N + 1)) (hψ : ∀ N, ‖ψ N‖ = 1)
    (hprep : Tendsto (fun N => ActualModelCorollaryR53a.preparationError u N (ψ N)) atTop (𝓝 0)) :
    Tendsto (fun N => if hk : k ≤ N + 1 then
      ActualModelCorollaryR53a.boxError hκ M.chart.chart (higher M.dynamics.hierarchy)
        u I R Θ T k N hk (ψ N) else 0) atTop (𝓝 0) :=
  ActualModelCorollaryR53a.convergence hκ _ _ u I R k Θ T
    (prop025_final_R56a hκ u hu M I R k Θ T hΘ hT) ψ hψ hprep

/-! ## Checks -/

open Lean Meta in
/-- Statement comparison: open both types fully; drop the old binders whose type head is one of
`drop`; the remaining old binder types and the old conclusion, after substitution, must be
alpha-equivalent (`==`) to the new ones, and the old conclusion must not mention a dropped binder. -/
private def dropCorrespondence (oldN newN : Name) (drop : List Name) :
    MetaM (Bool × Bool × Nat × Nat) := do
  let env ← getEnv
  let some oldCi := env.find? oldN | throwError "missing {oldN}"
  let some newCi := env.find? newN | throwError "missing {newN}"
  forallTelescope oldCi.type fun xs told =>
    forallTelescope newCi.type fun ys tnew => do
      let mut kept : Array Expr := #[]
      let mut dropped : Array Expr := #[]
      for x in xs do
        let t ← inferType x
        if drop.any (fun c => t.getAppFn.isConstOf c) then dropped := dropped.push x
        else kept := kept.push x
      if kept.size != ys.size then
        throwError "arity mismatch {oldN}: kept {kept.size}, new {ys.size}"
      if dropped.size != drop.length then
        throwError "dropped {dropped.size} binders, expected {drop.length}"
      let mut binders := true
      for i in [0:kept.size] do
        let tOld := (← inferType kept[i]!).replaceFVars kept ys
        let tNew ← inferType ys[i]!
        unless tOld == tNew do binders := false
      let concl := told.replaceFVars kept ys
      let indep := !concl.hasAnyFVar (fun f => dropped.any (fun d => d.fvarId! == f))
      let eqv := concl == tnew
      let defeq ← isDefEq concl tnew
      return (binders && indep && eqv, binders && indep && defeq, xs.size, ys.size)

open Lean Meta in
/-- Transitive closure of a root: held identifiers and non-standard axioms are rejected. -/
private def transitiveAudit (root : Name) : MetaM (Nat × List Name) := do
  let env ← getEnv
  let mut pending : Array Name := #[root]
  let mut seen : Std.HashSet Name := {}
  let mut axs : List Name := []
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn "HeldGP14Tonelli").length > 1 ||
          (n.toString.splitOn "RegularCut").length > 1 then
        throwError "held identifier in closure of {root}: {n}"
      let some ci := env.find? n | throwError "missing constant {n}"
      match ci with
      | .axiomInfo _ =>
        unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
          throwError "nonstandard axiom in closure of {root}: {n}"
        unless axs.contains n do axs := n :: axs
      | _ => pure ()
      pending := pending ++ ci.type.getUsedConstants
      if let some v := ci.value? (allowOpaque := true) then
        pending := pending ++ v.getUsedConstants
  return (seen.size, axs)

end QuantumNLS.Prop025FinalR01

set_option maxHeartbeats 16000000 in
open Lean Meta Elab Command in
run_cmd liftTermElabM do
  let drop := [``QuantumNLS.Prop025OInputs.Prop021Input, ``QuantumNLS.Prop025OInputs.WindowInput]
  for (oldN, newN) in [
      (``QuantumNLS.Prop025ProvenanceR59a.prop025_intermediate, ``QuantumNLS.Prop025FinalR01.prop025_final),
      (``QuantumNLS.Prop025OLow.prop025, ``QuantumNLS.Prop025FinalR01.prop025_final_R56a),
      (``QuantumNLS.Prop025OLow.prop025, ``QuantumNLS.Prop025FinalR01.prop025_final_OLow),
      (``QuantumNLS.Prop025OLow.prop025_actual, ``QuantumNLS.Prop025FinalR01.prop025_actual_final)] do
    let (eqv, defeq, nOld, nNew) ← QuantumNLS.Prop025FinalR01.dropCorrespondence oldN newN drop
    unless eqv do throwError "type comparison FAILED: {oldN} vs {newN} (defeq {defeq})"
    logInfo m!"type comparison PASS: {newN} = {oldN} minus Prop021Input/WindowInput binders ({nOld} → {nNew} binders; alpha-equivalent, defeq {defeq})"

set_option maxHeartbeats 16000000 in
open Lean Meta Elab Command in
run_cmd liftTermElabM do
  -- The R56a conclusion is literally the R56a consumer proposition.
  let some ci := (← getEnv).find? ``QuantumNLS.Prop025FinalR01.prop025_final_R56a | throwError "missing"
  forallTelescope ci.type fun _ t => do
    unless t.getAppFn.isConstOf ``QuantumNLS.ActualModelCorollaryR56a.PROP025Input do
      throwError "prop025_final_R56a does not conclude ActualModelCorollaryR56a.PROP025Input"
  let some ci := (← getEnv).find? ``QuantumNLS.Prop025FinalR01.prop025_final | throwError "missing"
  forallTelescope ci.type fun xs t => do
    unless t.getAppFn.isConstOf ``QuantumNLS.Prop025ProvenanceR59a.PROP025WithPacket do
      throwError "prop025_final does not conclude PROP025WithPacket"
    let explicit ← xs.filterM fun x => return (← x.fvarId!.getBinderInfo).isExplicit
    unless explicit.size == 1 do throwError "prop025_final has {explicit.size} explicit binders"
    logInfo m!"headline shape PASS: prop025_final has the single explicit hypothesis {← inferType explicit[0]!}"
  -- The PROP-021 discharge is the term used by the accepted PROP-021 proof.
  let some acc := (← getEnv).find? ``QuantumNLS.Prop021FinalR135.prop021_in_chart | throwError "missing"
  let some v := acc.value? (allowOpaque := true) | throwError "no value"
  let used := v.getUsedConstants
  for n in [``QuantumNLS.Prop021AssemblyR131.prop021, ``QuantumNLS.Prop021FinalR135.remainder_torus,
      ``QuantumNLS.Prop024FinalH1.printedConstant, ``QuantumNLS.Prop024FinalH1.printedConstant_nonneg] do
    unless used.contains n do throwError "accepted prop021_in_chart does not use {n}"
  let some f := (← getEnv).find? ``QuantumNLS.Prop021FinalR135.prop021_final | throwError "missing"
  let some fv := f.value? (allowOpaque := true) | throwError "no value"
  unless fv.getUsedConstants.contains ``QuantumNLS.Prop024FinalR135.prop024 do
    throwError "accepted prop021_final does not use Prop024FinalR135.prop024"
  logInfo "PROP-021 provenance PASS: Prop021AssemblyR131.prop021, remainder_torus and printedConstant occur in the accepted Prop021FinalR135.prop021_in_chart; prop024 in prop021_final."

set_option maxHeartbeats 64000000 in
open Lean Meta Elab Command in
run_cmd liftTermElabM do
  for root in [``QuantumNLS.Prop025FinalR01.prop025_final,
      ``QuantumNLS.Prop025FinalR01.prop025_final_R56a,
      ``QuantumNLS.Prop025FinalR01.prop025_final_OLow,
      ``QuantumNLS.Prop025FinalR01.prop025_final_R53a,
      ``QuantumNLS.Prop025FinalR01.prop025_at_DEF044_packet,
      ``QuantumNLS.Prop025FinalR01.prop025_at_DEF044,
      ``QuantumNLS.Prop025FinalR01.prop025_actual_final,
      ``QuantumNLS.Prop025FinalR01.prop025_convergence,
      ``QuantumNLS.Prop025FinalR01.prop021_torus,
      ``QuantumNLS.Prop025FinalR01.prop021_torus_via_WIdent,
      ``QuantumNLS.Prop025FinalR01.window] do
    let (n, axs) ← QuantumNLS.Prop025FinalR01.transitiveAudit root
    logInfo m!"audit PASS {root}: {n} transitive constants, axioms {axs}, no HeldGP14Tonelli/RegularCut"

#print axioms QuantumNLS.Prop025FinalR01.pair_family
#print axioms QuantumNLS.Prop025FinalR01.remainder_physical
#print axioms QuantumNLS.Prop025FinalR01.prop021_torus
#print axioms QuantumNLS.Prop025FinalR01.prop021_torus_via_WIdent
#print axioms QuantumNLS.Prop025FinalR01.window
#print axioms QuantumNLS.Prop025FinalR01.prop025_final
#print axioms QuantumNLS.Prop025FinalR01.prop025_final_R56a
#print axioms QuantumNLS.Prop025FinalR01.prop025_final_OLow
#print axioms QuantumNLS.Prop025FinalR01.prop025_final_R53a
#print axioms QuantumNLS.Prop025FinalR01.prop025_at_DEF044_packet
#print axioms QuantumNLS.Prop025FinalR01.prop025_at_DEF044
#print axioms QuantumNLS.Prop025FinalR01.prop025_actual_final
#print axioms QuantumNLS.Prop025FinalR01.prop025_convergence
#print QuantumNLS.Prop025ProvenanceR59a.PROP025WithPacket
#print QuantumNLS.ActualModelCorollaryR56a.PROP025Input
