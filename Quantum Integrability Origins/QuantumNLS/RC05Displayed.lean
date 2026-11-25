import Mathlib
import QuantumNLS.RC05Parts

/-!
# RC05Displayed: R-C05E2420 `thm:global-full-transform`, displayed form WITHOUT the frequency-covariance input

Source: `source-text/chapters/principal_global.tex` (sha256 `ffab02b87a4f4b4608263dea38489a8deca1724fd5c4abe69d7deaa874175f0b`),
printed statement lines 2-64; printed proof `source-text/chapters/global/main_theorem.tex`
(sha256 `e80840d4a4c7386dd2e3377f2d2b55b68da3fd35256de7b550bde8bf1b644c80`).

The displayed theorem has six numbered items. `PrintedTransform` states them for one extending family `Φ, Ψ` of the
reviewed local maps at one period `L`, for every `κ > 0`:

* (1) item 1: `GlobalClauses` (the explicit chart part of R-F5355ABD `RF535Final.GlobalStatement`, second conjunct), together with
  strong symplecticity (DEF-016) and the global-chart characterization `IsGlobalChart` (uniqueness data of item 6).
* (2)-(4) items 2-4: `∃ hs, PhysDyn hκ hs` (R-EF8C2837 `REF88Final.global_physical_dynamics`).
* (5) items 5 and 6 (covariances, scaling, joint analyticity, `C¹` limit, uniqueness): `Compatibility` (R-CA92819A).
* (6) item 6, the necessity of the real identity: `RephasingFreedom` for every real `c ≠ 0` (R-8DD5AE6E).

The top-level theorem `global_full_transform` additionally states, as printed in items 5 and 6, the physical-period conversion
`PeriodConversion` (`norm:period-coupling-formula`, R-71F7DDC8) and the accepted rephasing headline `RephasingStatement`
(`norm:rephasing`, R-8DD5AE6E) for every `c ≠ 0`, `κ > 0`.

There is NO hypothesis: the named input `hcov` of `RC05Main.global_full_transform_of_input` (R-877E839C,
`RC05Statement.FreqCovInput`) and its extra conjunct `∃ ν, PhysicalFrequency ∧ FreqCovClauses` are absent. That conjunct is
the proof-cited, non-displayed item 5b and is kept separately (module `RC05FreqCov`, statement only).

The statement is the reviewer formulation `printed_transform` (review record round 72), with the same six clauses in the same
order and the same quantifier structure; the proof below is written here from the frozen `RC05Parts` bridges and the accepted
headlines, and no reviewer file is imported.

The conjunct (1) uses `GlobalClauses`, which is the second conjunct of `GlobalStatement`, not an equivalence with it.
Only the forward direction (`RC05Parts.global_clauses_of_family`) is used here; that direction discards the torus conjunct.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ENNReal Topology ComplexConjugate
open Filter Set Metric

namespace QuantumNLS.RC05Displayed

open QuantumNLS.StrongSymplectic QuantumNLS.REF88PrintedChartLocal QuantumNLS.RC05Statement QuantumNLS.RC05Parts
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.D01LocalPrimitive (K)
open QuantumNLS.RF535Final (Local023Body)
open QuantumNLS.GlobalCompatR47a (Family Compatibility)

/-- The six displayed clauses of `thm:global-full-transform` for one extending family `Φ, Ψ` of the reviewed local maps
`Φl, Ψl` (LOCAL-023 data `d, CL`) at period `L`, for every coupling `κ > 0`. -/
def PrintedTransform (L : ℝ) [Fact (0 < L)] (d CL : ℝ) (Φl : ℝ → L2T L → K) (Ψl : ℝ → K → L2T L)
    (Φ : ℝ → L2T L → K) (Ψ : ℝ → K → L2T L) : Prop :=
  -- (1) item 1: the map of `thm:global-actual-chart`, strongly symplectic (DEF-016), characterized as the global chart
  (∀ (κ : ℝ) (hκ : 0 < κ), GlobalClauses L κ hκ d (Φl κ) (Ψl κ) (Φ κ) (Ψ κ) ∧
    IsStronglySymplectic (Φ κ) ∧ IsGlobalChart L κ hκ (Φ κ)) ∧
  -- (2), (3), (4) items 2-4: the physical dynamics, frequencies and Sobolev statements (R-EF8C2837)
  (∀ (κ : ℝ) (hκ : 0 < κ), ∃ hs : IsStronglySymplectic (Φ κ), PhysDyn hκ hs) ∧
  -- (5) items 5 and 6: covariances, scaling, joint analyticity, free limit with bounds, uniqueness (R-CA92819A)
  Compatibility d CL Φ Ψ ∧
  -- (6) item 6: necessity of the real identity, the action-dependent canonical phase freedom (R-8DD5AE6E)
  (∀ (κ : ℝ) (hκ : 0 < κ) (c : ℝ), c ≠ 0 → RephasingFreedom hκ (Φ κ) c)

/-- **R-C05E2420 `thm:global-full-transform`, displayed form, no `hcov`.**
For every `L > 0` the LOCAL-023 data and the reviewed local maps exist, an extending family exists, and every extending
family satisfies the six displayed clauses `PrintedTransform`; the period conversion `norm:period-coupling-formula`
(item 5) and the rephasing headline `norm:rephasing` (item 6) hold. -/
theorem global_full_transform :
    (∀ (L : ℝ) [Fact (0 < L)], ∃ d CL : ℝ, 0 < d ∧ 0 ≤ CL ∧
      ∃ (Φl : ℝ → L2T L → K) (Ψl : ℝ → K → L2T L),
        Local023Body L d CL Φl Ψl ∧ (∃ (Φ : ℝ → L2T L → K) (Ψ : ℝ → K → L2T L), Family d Φl Ψl Φ Ψ) ∧
        ∀ (Φ : ℝ → L2T L → K) (Ψ : ℝ → K → L2T L), Family d Φl Ψl Φ Ψ → PrintedTransform L d CL Φl Ψl Φ Ψ) ∧
    PeriodConversion ∧
    (∀ (c κ : ℝ) (hc : c ≠ 0) (hκ : 0 < κ), RephasingStatement c κ hc hκ) := by
  refine ⟨fun L _ => ?_, period_conversion, fun c κ hc hκ => QuantumNLS.RephasingFlow.norm_rephasing c κ hc hκ⟩
  obtain ⟨d, CL, hd, hCL, Φl, Ψl, hl, hex, hcompat⟩ := QuantumNLS.GlobalCompatR47a.global_compatibility L
  refine ⟨d, CL, hd, hCL, Φl, Ψl, hl, hex, fun Φ Ψ hf => ?_⟩
  have hcomp : Compatibility d CL Φ Ψ := hcompat Φ Ψ hf
  have hP : ∀ (κ : ℝ) (hκ : 0 < κ), PrintedChartLocal hκ (Φ κ) :=
    fun κ hκ => printedChartLocal hf hcomp hκ
  refine ⟨fun κ hκ => ⟨global_clauses_of_family hd hCL hl hf hκ, (hf κ hκ).strong, ?_⟩,
    fun κ hκ => ⟨(hP κ hκ).symp, physDyn_of hκ (hP κ hκ)⟩, hcomp, ?_⟩
  · obtain ⟨-, -, -, hreal, -⟩ := hcomp.1 κ hκ
    exact ⟨(hP κ hκ).symp, (hP κ hκ).analytic, (hP κ hκ).moduli, (hP κ hκ).fourier, hreal⟩
  · intro κ hκ c hc0
    obtain ⟨-, -, hplane, hreal, -⟩ := hcomp.1 κ hκ
    exact rephasing_freedom hκ (hP κ hκ) hplane (fun u => by rw [(hf κ hκ).norm u])
      (fun z => ⟨Ψ κ z, (hf κ hκ).right_inv z⟩) hreal c hc0

end QuantumNLS.RC05Displayed

#print axioms QuantumNLS.RC05Displayed.global_full_transform

/-! Closure audit: standard axioms only, and none of the held identifiers in the proof closure. -/
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[``QuantumNLS.RC05Displayed.global_full_transform]
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      let s := n.toString
      if (s.splitOn "HeldGP14Tonelli").length > 1 || (s.splitOn "RegularCut").length > 1 then
        throwError "Held identifier in closure: {n}"
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"RC05Displayed closure audit PASS: {seen.size} transitive constants; standard axioms only; no HeldGP14Tonelli/RegularCut."
