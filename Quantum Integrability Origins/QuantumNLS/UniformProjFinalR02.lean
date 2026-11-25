import QuantumNLS.UniformStaticBridgeR50b
import QuantumNLS.DynamicGaugePhysicalR34m

/-!
# UniformProjFinalR02: R-98833BEE `thm:uniform-projective` — FINAL BINDING (no named theorem inputs)

Source: `source-text/chapters/core/projective_reconstruction.tex` (sha256
`bc1188a07b52d3a19c337ef5ba61fb006d940f5d079d0defe2730801e679a60d`), statement lines 369-376, proof 377-388;
`eq:uniform-projective-main` = `source-text/chapters/principal_correspondence.tex:25-30` (sha256 `6008c7e6…`).
"For every fixed `R`, equation `eq:uniform-projective-main` holds. The conclusion persists if normalized
preparations `ψ_N(u)` satisfy `sup_{u∈𝒰_R}‖ψ_N(u)-u^{⊗N}‖ → 0`. For every fixed coordinate `b` and `r>0`, the
normalized columns converge uniformly on `{u∈𝒰_R : |w_b(u)| ≥ r}` to `w(u)\overline{w_b(u)}/|w_b(u)|`. Their images
under the quantum-derived inverse converge uniformly in physical `L²` to `u\overline{w_b(u)}/|w_b(u)|`. No energy
preparation, positive-order Sobolev convergence or rate is asserted."

## Binding
The intermediate `UniformProjR01.uniform_projective_intermediate` (r96 CONDITIONAL PASS) has the schedule `j`, the
full gauge `q` and the single named input `UniformStaticD2F4CE8FInput hκ j q`. Here `j := sectorStage hκ`,
`q := toFullGauge (sectorGauge hκ)` (the selected Q06 witnesses, = the R-D51987CA named pair of review record r105),
and the input is discharged by sol_ext_b's `UniformStaticBridgeR50b.selected_projective_input hκ` (review record
r97 PASS), whose type is literally the named input at these witnesses. The schedule enters only the input; the
conclusion depends on the gauge only. The printed disclaimer sentence adds no conjunct. Only hypothesis: `κ > 0`.

`same_gauge`: the DEF-029 gauge `fullToGauge q₀` of the headline is `DynamicGaugePhysicalR34m.physicalGauge q₀`,
the gauge of the R-8362E5EB / R-FAF88C8A finals (`DynamicGaugeFinalR35m.gauge hκ` is the abbreviation
`physicalGauge (sectorGauge hκ)`); `uniform_projective_printed` restates the headline at that gauge
(the printed "same gauge" of `thm:main`(ii)).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped InnerProductSpace ComplexConjugate ENNReal
open Filter Topology

noncomputable section

namespace QuantumNLS.UniformProjFinalR02

open QuantumNLS.OccupationUnitary (OneParticle oneBasis)
open QuantumNLS.AuxiliaryDensity (rankOneOperator)
open QuantumNLS.TraceClass (traceNorm)
open QuantumNLS.BetheCoefficientTransform (HN)
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.UniformProjR01Compact (UR)

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

/-- **R-98833BEE `thm:uniform-projective`, FINAL BINDING (headline).** The printed statement
(`UniformProjR01.UniformProjectiveStatement98833BEE`) at the selected Q06 gauge; only hypothesis `κ > 0`. -/
theorem uniform_projective_final (hκ : 0 < κ) :
    UniformProjR01.UniformProjectiveStatement98833BEE (L := L) hκ
      (UniformStaticBridgeR50b.toFullGauge (RetargetSelectionR49b.sectorGauge (L := L) hκ)) :=
  UniformProjR01.uniform_projective_intermediate (L := L) hκ (RetargetSelectionR49b.sectorStage (L := L) hκ)
    (UniformStaticBridgeR50b.toFullGauge (RetargetSelectionR49b.sectorGauge (L := L) hκ))
    (UniformStaticBridgeR50b.selected_projective_input (L := L) hκ)

/-- The headline's DEF-029 gauge is the physical gauge of the R-D51987CA named pair. -/
theorem same_gauge (hκ : 0 < κ) :
    UniformProjR01Bridge.fullToGauge
        (UniformStaticBridgeR50b.toFullGauge (RetargetSelectionR49b.sectorGauge (L := L) hκ)) =
      DynamicGaugePhysicalR34m.physicalGauge
        (UniformStaticBridgeR50b.toFullGauge (RetargetSelectionR49b.sectorGauge (L := L) hκ)) := by
  funext N m
  cases N with
  | zero => rfl
  | succ n => rfl

/-- `Γ_N[ψ]`, `N = 1+n`, at the physical gauge of the R-D51987CA named pair. -/
abbrev Gamma (hκ : 0 < κ) (n : ℕ) (ψ : HN L (1 + n)) : OneParticle →L[ℂ] OneParticle :=
  PreparationStability.density (ColumnR01.basis (L := L) hκ n)
    (DynamicGaugePhysicalR34m.physicalGauge
      (UniformStaticBridgeR50b.toFullGauge (RetargetSelectionR49b.sectorGauge (L := L) hκ))) ψ

/-- `w = Φ^q_{L,κ}`, the accepted chart. -/
abbrev w (hκ : 0 < κ) (u : L2T L) : OneParticle := (Def021ChartR41b.chart L κ hκ).Φ u

/-- **R-98833BEE `thm:uniform-projective`, printed form at the R-8362E5EB / R-FAF88C8A gauge**: for every `R`,
(1) `sup_{u∈𝒰_R} ‖Γ_N[u^{⊗N}] - |w(u)⟩⟨w(u)|‖₁ → 0`; for every family `ψ_N(u)` normalized on `𝒰_R` with
`sup_{𝒰_R} ‖ψ_N(u) - u^{⊗N}‖ → 0`: (2) the same for `Γ_N[ψ_N(u)]`; and for every `b`, `r > 0`, uniformly on
`{u ∈ 𝒰_R : r ≤ |w_b(u)|}`: (3) `Γ_N e_b/‖Γ_N e_b‖ → w(u)conj(w_b(u))/|w_b(u)|`;
(4) `w⁻¹(Γ_N e_b/‖Γ_N e_b‖) → (conj(w_b(u))/|w_b(u)|) u` in `L²`. -/
theorem uniform_projective_printed (hκ : 0 < κ) :
    ∀ R : ℝ,
      Tendsto (fun n => ⨆ u : UR L R,
        traceNorm (Gamma hκ n (HighMomentsOps.wvec (1 + n) (u : L2T L)) - rankOneOperator (w (L := L) hκ u)))
        atTop (𝓝 0) ∧
      ∀ ψ : ∀ n : ℕ, L2T L → HN L (1 + n), (∀ n, ∀ u ∈ UR L R, ‖ψ n u‖ = 1) →
        Tendsto (fun n => ⨆ u : UR L R,
          ENNReal.ofReal ‖ψ n u - (HighMomentsOps.wvec (1 + n) (u : L2T L) : HN L (1 + n))‖)
          atTop (𝓝 0) →
        Tendsto (fun n => ⨆ u : UR L R, traceNorm (Gamma hκ n (ψ n u) - rankOneOperator (w (L := L) hκ u)))
          atTop (𝓝 0) ∧
        ∀ b : ℤ, ∀ r : ℝ, 0 < r →
          Tendsto (fun n => ⨆ u : ↥{u : L2T L | u ∈ UR L R ∧ r ≤ ‖w (L := L) hκ u b‖}, ENNReal.ofReal
              ‖(((‖Gamma hκ n (ψ n u) (oneBasis b)‖ : ℝ) : ℂ))⁻¹ • Gamma hκ n (ψ n u) (oneBasis b) -
                (conj (w (L := L) hκ u b) / ((‖w (L := L) hκ u b‖ : ℝ) : ℂ)) • w (L := L) hκ u‖) atTop (𝓝 0) ∧
          Tendsto (fun n => ⨆ u : ↥{u : L2T L | u ∈ UR L R ∧ r ≤ ‖w (L := L) hκ u b‖}, ENNReal.ofReal
              ‖(Def021ChartR41b.chart L κ hκ).Ψ
                  ((((‖Gamma hκ n (ψ n u) (oneBasis b)‖ : ℝ) : ℂ))⁻¹ • Gamma hκ n (ψ n u) (oneBasis b)) -
                (conj (w (L := L) hκ u b) / ((‖w (L := L) hκ u b‖ : ℝ) : ℂ)) • (u : L2T L)‖) atTop (𝓝 0) := by
  unfold Gamma
  rw [← same_gauge hκ]
  exact uniform_projective_final hκ

end QuantumNLS.UniformProjFinalR02

set_option maxHeartbeats 16000000 in
open Lean Meta Elab Command in
run_cmd liftTermElabM do
  -- Final-binding comparison (same procedure as `ColumnFinalR02.bindingCheck`, inlined to keep this module
  -- independent of the R-AA5864B7 / R-154AFD4C bindings).
  let env ← getEnv
  let final := ``QuantumNLS.UniformProjFinalR02.uniform_projective_final
  let inter := ``QuantumNLS.UniformProjR01.uniform_projective_intermediate
  let disch := ``QuantumNLS.UniformStaticBridgeR50b.selected_projective_input
  let some fCi := env.find? final | throwError "missing {final}"
  let some iCi := env.find? inter | throwError "missing {inter}"
  let some v := fCi.value? (allowOpaque := true) | throwError "no value"
  let (nI, nF, syn) ← lambdaTelescope v fun xs body => do
    unless body.getAppFn.isConstOf inter do throwError "head is not {inter}"
    let args := body.getAppArgs
    let last := args.back!
    unless last.getAppFn.isConstOf disch do throwError "input is not discharged by {disch}"
    let pt ← inferType (mkAppN body.getAppFn args.pop)
    let .forallE _ dom concl _ := pt | throwError "partial application is not an arrow"
    if concl.hasLooseBVars then throwError "conclusion depends on the discharged input"
    unless concl == (← instantiateForall fCi.type xs) do
      throwError "conclusion differs from the instantiated intermediate conclusion"
    let dt ← inferType last
    unless ← isDefEq dom dt do throwError "discharging term does not have the input type"
    let nI ← forallTelescope iCi.type fun ys _ => pure ys.size
    return (nI, xs.size, dom == dt)
  logInfo m!"type comparison PASS: uniform_projective_final = UniformProjR01.uniform_projective_intermediate at (j, q) = (sectorStage, toFullGauge sectorGauge) with UniformStaticD2F4CE8FInput discharged by UniformStaticBridgeR50b.selected_projective_input ({nI} → {nF} binders; conclusion identical (==); input type defeq, syntactically identical: {syn})"
  forallTelescope fCi.type fun xs t => do
    unless t.getAppFn.isConstOf ``QuantumNLS.UniformProjR01.UniformProjectiveStatement98833BEE do
      throwError "uniform_projective_final does not conclude UniformProjectiveStatement98833BEE"
    let explicit ← xs.filterM fun x => return (← x.fvarId!.getBinderInfo).isExplicit
    unless explicit.size == 1 do throwError "uniform_projective_final has {explicit.size} explicit binders"
    logInfo m!"headline shape PASS: uniform_projective_final has the single explicit hypothesis {← inferType explicit[0]!}"

set_option maxHeartbeats 64000000 in
open Lean Meta Elab Command in
run_cmd liftTermElabM do
  for root in [``QuantumNLS.UniformProjFinalR02.uniform_projective_final,
      ``QuantumNLS.UniformProjFinalR02.uniform_projective_printed,
      ``QuantumNLS.UniformProjFinalR02.same_gauge] do
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
    logInfo m!"audit PASS {root}: {seen.size} transitive constants, axioms {axs}, no HeldGP14Tonelli/RegularCut"

#check @QuantumNLS.UniformProjFinalR02.uniform_projective_final
#print QuantumNLS.UniformProjR01.UniformProjectiveStatement98833BEE
#print axioms QuantumNLS.UniformProjFinalR02.uniform_projective_final
#print axioms QuantumNLS.UniformProjFinalR02.same_gauge
#print axioms QuantumNLS.UniformProjFinalR02.uniform_projective_printed
