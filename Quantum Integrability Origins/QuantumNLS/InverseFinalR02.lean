import QuantumNLS.InverseR01
import QuantumNLS.ColumnFinalR02

/-!
# InverseFinalR02: R-154AFD4C `cor:inverse` — FINAL BINDING (no named theorem inputs)

Source: `source-text/chapters/core/projective_reconstruction.tex` (sha256
`bc1188a07b52d3a19c337ef5ba61fb006d940f5d079d0defe2730801e679a60d`), statement lines 338-345, proof 346-360.
"Applying the quantum-derived inverse `w⁻¹` to the unit columns `ĉ_N^{(b)}(t)` gives physical profiles converging in
`L²`, uniformly on `K`, to `conj(w_b(t)) Φ_t u/|w_b(t)|`. This assertion uses the previously proved continuous inverse
and its `U(1)` equivariance. Trace norm convergence alone supplies no Sobolev convergence of positive order."

## Binding
The intermediate `InverseR01.inverse_intermediate` has the same parameters as `cor:column` and the single named
input `ColumnAA5864B7Input : ColumnR01.ColumnAA5864B7Statement hκ C g Fl hFl`. The parameters are instantiated
exactly as in `ColumnFinalR02.column_final` (accepted chart, R-D51987CA named gauge
`DynamicGaugeFinalR35m.gauge hκ`, RB7BindFinal hierarchy flows), and the input is discharged by
`ColumnFinalR02.column_final hκ` (node R-AA5864B7, final binding). The trailing sentence of the printed statement
is a disclaimer and adds no conjunct. Only hypothesis: `κ > 0`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped InnerProductSpace ComplexConjugate ComplexOrder ENNReal
open Filter Topology

noncomputable section

namespace QuantumNLS.InverseFinalR02

open QuantumNLS.OccupationUnitary (OneParticle oneBasis)
open QuantumNLS.BetheCoefficientTransform (HN)
open QuantumNLS.Def033HierarchyR24m (Smooth physical jointSmooth)
open QuantumNLS.ColumnFinalR02 (Gamma w hierarchyFlows)

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

/-- **R-154AFD4C `cor:inverse`, FINAL BINDING (headline).** The printed inverse statement
(`InverseR01.InverseStatement154AFD4C`) at the accepted chart, the R-D51987CA named gauge and the accepted
hierarchy flows; only hypothesis `κ > 0`. -/
theorem inverse_final (hκ : 0 < κ) :
    InverseR01.InverseStatement154AFD4C hκ (Def021ChartR41b.chart L κ hκ)
      (DynamicGaugeFinalR35m.gauge (L := L) hκ)
      (ActualModelTargetR53a.flowMap
        (ReconstructionR33m.flows hκ (RB7BindFinal.hierarchyInputR25m_unconditional (L := L) hκ)))
      (ActualModelTargetR53a.flow_isHam
        (ReconstructionR33m.flows hκ (RB7BindFinal.hierarchyInputR25m_unconditional (L := L) hκ))) :=
  InverseR01.inverse_intermediate hκ (Def021ChartR41b.chart L κ hκ)
    (DynamicGaugeFinalR35m.gauge (L := L) hκ)
    (ActualModelTargetR53a.flowMap
      (ReconstructionR33m.flows hκ (RB7BindFinal.hierarchyInputR25m_unconditional (L := L) hκ)))
    (ActualModelTargetR53a.flow_isHam
      (ReconstructionR33m.flows hκ (RB7BindFinal.hierarchyInputR25m_unconditional (L := L) hκ)))
    (ColumnFinalR02.column_final (L := L) hκ)

/-- **R-154AFD4C `cor:inverse`, printed form**, on the objects of the R-FAF88C8A final: for the smooth unit
profile `u`, finite `𝓡`, compact `K`, normalized `ψ_N` with `‖ψ_N - u^{⊗N}‖ → 0` and every `b` with
`|w_b(u)| > 0`: `sup_{t∈K} ‖w⁻¹(Γ_N(t)e_b/‖Γ_N(t)e_b‖) - (conj(w_b(t))/|w_b(t)|) Φ_t u‖_{L²} → 0`,
where `Φ_t u = physical (jointSmooth (hamFlows F 𝓡) t u)` is the accepted joint hierarchy flow.
Proved by `inverse_final` (definitional unfolding only). -/
theorem inverse_printed (hκ : 0 < κ) :
    ∀ (u : Smooth L), ‖physical u‖ = 1 →
    ∀ (R : Finset ℕ) (K : Set (ℕ → ℝ)), IsCompact K →
    ∀ (ψ : ∀ n : ℕ, HN L (1 + n)), (∀ n, ‖ψ n‖ = 1) →
      Tendsto (fun n => ‖ψ n - ReconstructionR33m.product u n‖) atTop (𝓝 0) →
    ∀ b : ℤ, 0 < ‖(Def021ChartR41b.chart L κ hκ).Φ (physical u) b‖ →
      Tendsto (fun n => ⨆ t : K, ENNReal.ofReal
          ‖(Def021ChartR41b.chart L κ hκ).Ψ
              ((((‖Gamma hκ R ψ n t (oneBasis b)‖ : ℝ) : ℂ))⁻¹ • Gamma hκ R ψ n t (oneBasis b)) -
            (conj (w hκ u R t b) / ((‖w hκ u R t b‖ : ℝ) : ℂ)) •
              physical (jointSmooth (ActualModelTargetR53a.hamFlows (hierarchyFlows (L := L) hκ) R) t u)‖)
        atTop (𝓝 0) :=
  inverse_final hκ

/-- Same gauge across R-AA5864B7, R-154AFD4C and R-98833BEE: the gauge of the column/inverse finals equals the
DEF-029 gauge `fullToGauge q₀` through which `UniformProjR01.Γ` enters the R-98833BEE final at the Q06 witness
`q₀ = toFullGauge (sectorGauge hκ)` (frozen `FullWickO3.physicalGauge_eq_fullToGauge`). -/
theorem gauge_eq_uniform_gauge (hκ : 0 < κ) :
    DynamicGaugeFinalR35m.gauge (L := L) hκ =
      UniformProjR01Bridge.fullToGauge
        (UniformStaticBridgeR50b.toFullGauge (RetargetSelectionR49b.sectorGauge (L := L) hκ)) :=
  FullWickO3.physicalGauge_eq_fullToGauge _

end QuantumNLS.InverseFinalR02

set_option maxHeartbeats 16000000 in
open Lean Meta Elab Command in
run_cmd liftTermElabM do
  let (nI, nF, syn) ← QuantumNLS.ColumnFinalR02.bindingCheck
    ``QuantumNLS.InverseFinalR02.inverse_final ``QuantumNLS.InverseR01.inverse_intermediate
    ``QuantumNLS.ColumnFinalR02.column_final
  logInfo m!"type comparison PASS: inverse_final = InverseR01.inverse_intermediate at (chart, R-D51987CA gauge, RB7BindFinal flows) with ColumnAA5864B7Input discharged by ColumnFinalR02.column_final ({nI} → {nF} binders; conclusion identical (==); input type defeq, syntactically identical: {syn})"
  let some ci := (← getEnv).find? ``QuantumNLS.InverseFinalR02.inverse_final | throwError "missing"
  forallTelescope ci.type fun xs t => do
    unless t.getAppFn.isConstOf ``QuantumNLS.InverseR01.InverseStatement154AFD4C do
      throwError "inverse_final does not conclude InverseStatement154AFD4C"
    let explicit ← xs.filterM fun x => return (← x.fvarId!.getBinderInfo).isExplicit
    unless explicit.size == 1 do throwError "inverse_final has {explicit.size} explicit binders"
    logInfo m!"headline shape PASS: inverse_final has the single explicit hypothesis {← inferType explicit[0]!}"
  let some cp := (← getEnv).find? ``QuantumNLS.InverseFinalR02.inverse_printed | throwError "missing"
  let ok ← forallTelescope ci.type fun xs t => do
    isDefEq (← instantiateForall cp.type xs) t
  unless ok do throwError "inverse_printed is not definitionally inverse_final's statement"
  logInfo "printed form PASS: inverse_printed's statement is definitionally inverse_final's statement"

set_option maxHeartbeats 64000000 in
open Lean Meta Elab Command in
run_cmd liftTermElabM do
  for root in [``QuantumNLS.InverseFinalR02.inverse_final,
      ``QuantumNLS.InverseFinalR02.inverse_printed,
      ``QuantumNLS.InverseFinalR02.gauge_eq_uniform_gauge] do
    let (n, axs) ← QuantumNLS.ColumnFinalR02.transitiveAudit root
    logInfo m!"audit PASS {root}: {n} transitive constants, axioms {axs}, no HeldGP14Tonelli/RegularCut"

#check @QuantumNLS.InverseFinalR02.inverse_final
#print QuantumNLS.InverseR01.InverseStatement154AFD4C
#print axioms QuantumNLS.InverseFinalR02.inverse_final
#print axioms QuantumNLS.InverseFinalR02.inverse_printed
#print axioms QuantumNLS.InverseFinalR02.gauge_eq_uniform_gauge
