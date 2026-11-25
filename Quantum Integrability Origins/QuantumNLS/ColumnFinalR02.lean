import QuantumNLS.ColumnR01
import QuantumNLS.ReconstructionFinalR35m

/-!
# ColumnFinalR02: R-AA5864B7 `cor:column` — FINAL BINDING (no named theorem inputs)

Source: `source-text/chapters/core/projective_reconstruction.tex` (sha256
`bc1188a07b52d3a19c337ef5ba61fb006d940f5d079d0defe2730801e679a60d`), statement lines 281-303, proof 304-324.
"Under Corollary thm:reconstruction, choose `b ∈ ℤ` with `r := |w_b(u)| > 0`. Let
`ε_N = sup_{t∈K} ‖Γ_N(t) - P(t)‖₁`. For all sufficiently large `N`, `p_N(t) := Γ_N(t)_{bb} > 0` uniformly on `K`.
The columns `c_N^{(b)}(t) = Γ_N(t)e_b/√p_N(t)` satisfy `sup_{t∈K} ‖c_N^{(b)}(t) - w(t) conj(w_b(t))/|w_b(t)|‖ → 0`.
The exactly normalized columns `ĉ_N^{(b)}(t) = Γ_N(t)e_b/‖Γ_N(t)e_b‖` are also defined for large `N` and have the
same limit, with error at most `2ε_N/r`."

## Binding
The reviewed intermediate `ColumnR01.column_intermediate` (r256 CONDITIONAL PASS) has the parameters chart `C`,
gauge `g`, hierarchy flows `(Fl, hFl)` and the single named input `ReconstructionFAF88C8AInput`. Here:
* `C := Def021ChartR41b.chart L κ hκ` (accepted DEF-021 / R-F5355ABD chart, the chart of R-FAF88C8A);
* `g := DynamicGaugeFinalR35m.gauge hκ` `= DynamicGaugePhysicalR34m.physicalGauge (RetargetSelectionR49b.sectorGauge hκ)`,
  the gauge of the R-D51987CA named pair `(sectorStage, sectorGauge)` (review record r105), as used by the
  R-8362E5EB and R-FAF88C8A finals of sol_multi r35;
* `Fl := ActualModelTargetR53a.flowMap F`, `hFl := ActualModelTargetR53a.flow_isHam F`, with
  `F := ReconstructionR33m.flows hκ (RB7BindFinal.hierarchyInputR25m_unconditional hκ)` (accepted hierarchy,
  RB7BindFinal), so `ColumnR01.flows Fl hFl R` is definitionally `ActualModelTargetR53a.hamFlows F R`;
* `ReconstructionFAF88C8AInput := ReconstructionFinalR35m.reconstruction hκ` (sol_multi r35 R-FAF88C8A final).
  Its type `ReconstructionR33m.Reconstruction hκ F g` is definitionally the named input at these parameters
  (checked by the kernel at the application, and by the `run_cmd` type comparison below).

The only hypothesis of the headline is the printed `κ > 0` (with the standing `L > 0`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped InnerProductSpace ComplexConjugate ComplexOrder ENNReal
open Filter Topology

noncomputable section

namespace QuantumNLS.ColumnFinalR02

open QuantumNLS.OccupationUnitary (OneParticle oneBasis)
open QuantumNLS.TraceClass (traceNorm)
open QuantumNLS.BetheCoefficientTransform (HN)
open QuantumNLS.Def033HierarchyR24m (Smooth physical jointSmooth)

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

/-- The accepted hierarchy flows (RB7BindFinal), as fixed by the R-FAF88C8A final. -/
abbrev hierarchyFlows (hκ : 0 < κ) : ActualModelTargetR53a.HigherFlows L κ :=
  ReconstructionR33m.flows hκ (RB7BindFinal.hierarchyInputR25m_unconditional (L := L) hκ)

/-- `Γ_N(t) = Γ_N[U_N(t)ψ_N]`, `N = 1+n`, exactly the R-FAF88C8A final's object at its gauge. -/
abbrev Gamma (hκ : 0 < κ) (R : Finset ℕ) (ψ : ∀ n : ℕ, HN L (1 + n)) (n : ℕ) (t : ℕ → ℝ) :
    OneParticle →L[ℂ] OneParticle :=
  ReconstructionR33m.density hκ (DynamicGaugeFinalR35m.gauge (L := L) hκ) n
    (ReconstructionR33m.U hκ R t n (ψ n))

/-- `w(t) = w(Φ_t u)`, exactly the R-FAF88C8A final's object at its flows. -/
abbrev w (hκ : 0 < κ) (u : Smooth L) (R : Finset ℕ) (t : ℕ → ℝ) : OneParticle :=
  ReconstructionR33m.w hκ (hierarchyFlows (L := L) hκ) u R t

/-- The named input of the intermediate, discharged by the R-FAF88C8A final (sol_multi r35). -/
theorem reconstruction_input (hκ : 0 < κ) :
    ColumnR01.ReconstructionFAF88C8AInput hκ (Def021ChartR41b.chart L κ hκ)
      (DynamicGaugeFinalR35m.gauge (L := L) hκ)
      (ActualModelTargetR53a.flowMap
        (ReconstructionR33m.flows hκ (RB7BindFinal.hierarchyInputR25m_unconditional (L := L) hκ)))
      (ActualModelTargetR53a.flow_isHam
        (ReconstructionR33m.flows hκ (RB7BindFinal.hierarchyInputR25m_unconditional (L := L) hκ))) :=
  ReconstructionFinalR35m.reconstruction (L := L) hκ

/-- **R-AA5864B7 `cor:column`, FINAL BINDING (headline).** The printed column statement
(`ColumnR01.ColumnAA5864B7Statement`) at the accepted chart, the R-D51987CA named gauge and the accepted
hierarchy flows; only hypothesis `κ > 0`. -/
theorem column_final (hκ : 0 < κ) :
    ColumnR01.ColumnAA5864B7Statement hκ (Def021ChartR41b.chart L κ hκ)
      (DynamicGaugeFinalR35m.gauge (L := L) hκ)
      (ActualModelTargetR53a.flowMap
        (ReconstructionR33m.flows hκ (RB7BindFinal.hierarchyInputR25m_unconditional (L := L) hκ)))
      (ActualModelTargetR53a.flow_isHam
        (ReconstructionR33m.flows hκ (RB7BindFinal.hierarchyInputR25m_unconditional (L := L) hκ))) :=
  ColumnR01.column_intermediate hκ (Def021ChartR41b.chart L κ hκ)
    (DynamicGaugeFinalR35m.gauge (L := L) hκ)
    (ActualModelTargetR53a.flowMap
      (ReconstructionR33m.flows hκ (RB7BindFinal.hierarchyInputR25m_unconditional (L := L) hκ)))
    (ActualModelTargetR53a.flow_isHam
      (ReconstructionR33m.flows hκ (RB7BindFinal.hierarchyInputR25m_unconditional (L := L) hκ)))
    (ReconstructionFinalR35m.reconstruction (L := L) hκ)

/-- **R-AA5864B7 `cor:column`, printed form**, written out on the objects of the R-FAF88C8A final
(`ReconstructionR33m.density`, `U`, `w`, `product`, `projector`): for the smooth unit profile `u`, finite `𝓡`,
compact `K`, normalized `ψ_N` with `‖ψ_N - u^{⊗N}‖ → 0` and every `b` with `r = |w_b(u)| > 0`:
(i) `∃ c > 0`, eventually `c ≤ p_N(t) = ⟨e_b, Γ_N(t)e_b⟩` on `K`;
(ii) `sup_K ‖Γ_N(t)e_b/√p_N(t) - w(t) conj(w_b(t))/|w_b(t)|‖ → 0`;
(iii) eventually, on `K`, `Γ_N(t)e_b ≠ 0` and `‖Γ_N(t)e_b/‖Γ_N(t)e_b‖ - target‖ ≤ 2ε_N/r`;
(iv) `sup_K ‖Γ_N(t)e_b/‖Γ_N(t)e_b‖ - target‖ → 0`.
Proved by `column_final` (definitional unfolding only). -/
theorem column_printed (hκ : 0 < κ) :
    ∀ (u : Smooth L), ‖physical u‖ = 1 →
    ∀ (R : Finset ℕ) (K : Set (ℕ → ℝ)), IsCompact K →
    ∀ (ψ : ∀ n : ℕ, HN L (1 + n)), (∀ n, ‖ψ n‖ = 1) →
      Tendsto (fun n => ‖ψ n - ReconstructionR33m.product u n‖) atTop (𝓝 0) →
    ∀ b : ℤ, 0 < ‖(Def021ChartR41b.chart L κ hκ).Φ (physical u) b‖ →
      (∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, ∀ t ∈ K,
          (c : ℂ) ≤ ⟪oneBasis b, Gamma hκ R ψ n t (oneBasis b)⟫_ℂ) ∧
      Tendsto (fun n => ⨆ t : K, ENNReal.ofReal
          ‖(((Real.sqrt ((Gamma hκ R ψ n t (oneBasis b)) b).re : ℝ) : ℂ))⁻¹ •
              Gamma hκ R ψ n t (oneBasis b) -
            (conj (w hκ u R t b) / ((‖w hκ u R t b‖ : ℝ) : ℂ)) • w hκ u R t‖)
        atTop (𝓝 0) ∧
      (∀ᶠ n in atTop, ∀ t ∈ K, Gamma hκ R ψ n t (oneBasis b) ≠ 0 ∧
          ‖(((‖Gamma hκ R ψ n t (oneBasis b)‖ : ℝ) : ℂ))⁻¹ • Gamma hκ R ψ n t (oneBasis b) -
              (conj (w hκ u R t b) / ((‖w hκ u R t b‖ : ℝ) : ℂ)) • w hκ u R t‖ ≤
            2 * (⨆ s : K, traceNorm (Gamma hκ R ψ n s -
              ReconstructionR33m.projector (w hκ u R s))).toReal /
              ‖(Def021ChartR41b.chart L κ hκ).Φ (physical u) b‖) ∧
      Tendsto (fun n => ⨆ t : K, ENNReal.ofReal
          ‖(((‖Gamma hκ R ψ n t (oneBasis b)‖ : ℝ) : ℂ))⁻¹ • Gamma hκ R ψ n t (oneBasis b) -
            (conj (w hκ u R t b) / ((‖w hκ u R t b‖ : ℝ) : ℂ)) • w hκ u R t‖)
        atTop (𝓝 0) :=
  column_final hκ

/-! ## Checks -/

open Lean Meta in
/-- Final-binding comparison. After its λ-binders, the value of `final` must be an application of `inter`
whose last argument has head `disch`. The type of `inter` applied to all other arguments must be a
NON-DEPENDENT arrow `I → S`, with `S` syntactically identical (`==`) to the conclusion of `final` and `I`
definitionally equal to the type of the discharging term. Returns the binder counts and `I == type`. -/
def bindingCheck (final inter disch : Name) : MetaM (Nat × Nat × Bool) := do
  let env ← getEnv
  let some fCi := env.find? final | throwError "missing {final}"
  let some iCi := env.find? inter | throwError "missing {inter}"
  let some v := fCi.value? (allowOpaque := true) | throwError "no value {final}"
  lambdaTelescope v fun xs body => do
    unless body.getAppFn.isConstOf inter do throwError "{final}: head is not {inter}"
    let args := body.getAppArgs
    let last := args.back!
    unless last.getAppFn.isConstOf disch do throwError "{final}: input is not discharged by {disch}"
    let part := mkAppN body.getAppFn args.pop
    let pt ← inferType part
    let .forallE _ dom concl _ := pt | throwError "{inter}: partial application is not an arrow"
    if concl.hasLooseBVars then throwError "{inter}: conclusion depends on the discharged input"
    let fT ← instantiateForall fCi.type xs
    unless concl == fT do throwError "{final}: conclusion differs from the instantiated {inter} conclusion"
    let dt ← inferType last
    unless ← isDefEq dom dt do throwError "{final}: {disch} does not have the input type of {inter}"
    let nInter ← forallTelescope iCi.type fun ys _ => pure ys.size
    return (nInter, xs.size, dom == dt)

open Lean Meta in
/-- Transitive closure of a root: held identifiers and non-standard axioms are rejected. -/
def transitiveAudit (root : Name) : MetaM (Nat × List Name) := do
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

end QuantumNLS.ColumnFinalR02

set_option maxHeartbeats 16000000 in
open Lean Meta Elab Command in
run_cmd liftTermElabM do
  let (nI, nF, syn) ← QuantumNLS.ColumnFinalR02.bindingCheck
    ``QuantumNLS.ColumnFinalR02.column_final ``QuantumNLS.ColumnR01.column_intermediate
    ``QuantumNLS.ReconstructionFinalR35m.reconstruction
  logInfo m!"type comparison PASS: column_final = ColumnR01.column_intermediate at (chart, R-D51987CA gauge, RB7BindFinal flows) with ReconstructionFAF88C8AInput discharged by ReconstructionFinalR35m.reconstruction ({nI} → {nF} binders; conclusion identical (==); input type defeq, syntactically identical: {syn})"
  let some ri := (← getEnv).find? ``QuantumNLS.ColumnFinalR02.reconstruction_input | throwError "missing"
  let some rf := (← getEnv).find? ``QuantumNLS.ReconstructionFinalR35m.reconstruction | throwError "missing"
  -- binder order differs ({L} [Fact] {κ} hκ here, {L} {κ} [Fact] hκ in R35m): instantiate by position
  let (ok, syn) ← forallTelescope ri.type fun xs t => do
    unless xs.size == 4 do throwError "reconstruction_input: unexpected binders"
    let tR ← instantiateForall rf.type #[xs[0]!, xs[2]!, xs[1]!, xs[3]!]
    return (← isDefEq t tR, t == tR)
  unless ok do
    throwError "ReconstructionFAF88C8AInput at the bound parameters is not defeq to the R35m type"
  logInfo m!"input comparison PASS: ColumnR01.ReconstructionFAF88C8AInput (chart, gauge, flows) ≡ ReconstructionR33m.Reconstruction hκ F g, the type of ReconstructionFinalR35m.reconstruction (defeq; syntactically identical: {syn})"
  let some ci := (← getEnv).find? ``QuantumNLS.ColumnFinalR02.column_final | throwError "missing"
  forallTelescope ci.type fun xs t => do
    unless t.getAppFn.isConstOf ``QuantumNLS.ColumnR01.ColumnAA5864B7Statement do
      throwError "column_final does not conclude ColumnAA5864B7Statement"
    let explicit ← xs.filterM fun x => return (← x.fvarId!.getBinderInfo).isExplicit
    unless explicit.size == 1 do throwError "column_final has {explicit.size} explicit binders"
    logInfo m!"headline shape PASS: column_final has the single explicit hypothesis {← inferType explicit[0]!}"
  let some cp := (← getEnv).find? ``QuantumNLS.ColumnFinalR02.column_printed | throwError "missing"
  let ok ← forallTelescope ci.type fun xs t => do
    isDefEq (← instantiateForall cp.type xs) t
  unless ok do throwError "column_printed is not definitionally column_final's statement"
  logInfo "printed form PASS: column_printed's statement is definitionally column_final's statement"

set_option maxHeartbeats 64000000 in
open Lean Meta Elab Command in
run_cmd liftTermElabM do
  for root in [``QuantumNLS.ColumnFinalR02.column_final,
      ``QuantumNLS.ColumnFinalR02.column_printed,
      ``QuantumNLS.ColumnFinalR02.reconstruction_input] do
    let (n, axs) ← QuantumNLS.ColumnFinalR02.transitiveAudit root
    logInfo m!"audit PASS {root}: {n} transitive constants, axioms {axs}, no HeldGP14Tonelli/RegularCut"

#check @QuantumNLS.ColumnFinalR02.column_final
#print QuantumNLS.ColumnR01.ColumnAA5864B7Statement
#print axioms QuantumNLS.ColumnFinalR02.reconstruction_input
#print axioms QuantumNLS.ColumnFinalR02.column_final
#print axioms QuantumNLS.ColumnFinalR02.column_printed
