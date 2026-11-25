import QuantumNLS.AuditGapsS01Core
import QuantumNLS.Bind7BDEF033H02

/-!
# AuditGapsS01Headline: R-10EE6421 `lem:audit-gaps`, printed form

PRINTED SOURCE: `source-text/chapters/core/weighted_actions_and_same_gauge_dynamics.tex`, lines 261-294
(`\begin{lemma}[Actual adjacent differences from these dynamic symbols]`, `\ReportID{R-10EE6421}`,
`\label{lem:audit-gaps}`).

PRINTED STATEMENT: "For each fixed positive-action donor-receiver pair and every fixed charge order, the
rebuilt-gauge dynamical symbols imply the master's receiver-minus-donor adjacent-difference convergence in
probability under the original product law. Finite families converge jointly. No moment convergence follows
from this argument."

CLAUSE MAP.
* "rebuilt-gauge dynamical symbols": the named hypothesis `hD : ReconstructionR33m.RD8362E5EBInput hκ F g`
  (the frozen formalization of the exact printed statement of the UNACCEPTED R-8362E5EB
  `prop:audit-dynamic-gauge`, lines 155-164; NOT re-proved or redefined here), with the single rebuilt
  gauge `g` and the fixed hierarchy flows `F` as context parameters exactly as in `RD8362E5EBInput`.
* "the master's receiver-minus-donor adjacent-difference convergence in probability under the original
  product law": `Def033CoreR24m.DifferenceLimit hκ (physical u) hu r a b (D.ω r u) missing`, the reviewed
  DEF-033 definition (receiver minus donor, original Born law `originalBorn` at `N + 1`, missing-donor
  convention `missing` ARBITRARY), with target `ω_{r,b}(u) - ω_{r,a}(u)` (`Def033CoreR24m.target`).
* "each fixed positive-action donor-receiver pair": `ha`, `hb`, `0 < a_n(u)` (`RootIndexedMasses.masses`), for
  every `a, b : ℤ` (including `a = b`, where the difference vanishes);
* "every fixed charge order": every `r : ℕ`;
* "Finite families converge jointly": `audit_gaps_joint`, the union bound, for every finite family of
  pairs and orders.
* "No moment convergence follows": nothing beyond convergence in probability is stated or used.
* DEF-033 objects `ω`, the flows and the active-frequency identity `w_n(Φ_t^{(r)}u) = e^{-itω_{r,n}(u)} w_n(u)`
  come from `D : Bind7BDEF033H02.DEF033Package hκ (chart).Φ` (the H02 structure; used only through its fields
  `ω`, `active`, `flow_unique`); `F` is identified with `D.flow` by `flow_unique`.

SCOPE PREDECESSORS: R-09DDF6D2 (accepted) is not used by the printed proof as a theorem (only the exact
multiplier identity, reproved in `AuditGapsS01Analytic`/`Level` from the frozen `DiagonalMultiplier`
lemmas); R-8362E5EB enters only as the named input `RD8362E5EBInput`; DEF-033 through the reviewed
definitions and the H02 package (no DEF-033 claim beyond the active-frequency clause is used).

No acceptance claim.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
noncomputable section
open Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace ENNReal Classical

namespace QuantumNLS.AuditGapsS01Headline
open QuantumNLS.BetheLabels QuantumNLS.BetheCoefficientTransform QuantumNLS.BetheOccupationGauge
open QuantumNLS.TerraMultiRound12Definitions QuantumNLS.Def033CoreR24m
open QuantumNLS.Occupation (DonorOK)
open QuantumNLS.ActualModelTargetR53a (HigherFlows hamFlows flowMap)
open QuantumNLS.Def033HierarchyR24m (Smooth physical jointSmooth)
open QuantumNLS.AuditGapsS01Level (tv)

variable {L κ : ℝ} [Fact (0 < L)]

theorem jointSmooth_single_val (F : HigherFlows L κ) (r : ℕ) (s : ℝ) (u : Smooth L) :
    (jointSmooth (hamFlows F {r}) (tv r s) u).val = flowMap F r s u.val := by
  have h : jointSmooth (hamFlows F {r}) (tv r s) u =
      Def033HierarchyR24m.smoothStep (hamFlows F {r}) r (tv r s r) u := by
    simp [jointSmooth, Finset.sort_singleton]
  rw [h]
  simp [Def033HierarchyR24m.smoothStep, hamFlows, tv]

/-- **R-10EE6421 `lem:audit-gaps`.** -/
theorem audit_gaps_printed (hκ : 0 < κ) (F : HigherFlows L κ) (g : Gauge)
    (hD : ReconstructionR33m.RD8362E5EBInput hκ F g)
    (D : Bind7BDEF033H02.DEF033Package hκ (Def021ChartR41b.chart L κ hκ).Φ)
    (u : Smooth L) (hu : ‖physical u‖ = 1) (r : ℕ) (a b : ℤ)
    (ha : 0 < (QuantumNLS.RootIndexedMasses.masses hκ (physical u)).1 a)
    (hb : 0 < (QuantumNLS.RootIndexedMasses.masses hκ (physical u)).1 b)
    (missing : ∀ N, MArr (N + 1) → ℝ) :
    DifferenceLimit hκ (physical u) hu r a b (D.ω r u) missing := by
  have hact : ∀ n : ℤ, 0 < (QuantumNLS.RootIndexedMasses.masses hκ (physical u)).1 n →
      ActiveFrequency (fun s : ℝ => (ReconstructionR33m.w hκ F u {r} (tv r s)) n)
        (((Def021ChartR41b.chart L κ hκ).Φ (physical u)) n) (D.ω r u n) := by
    intro n hn
    have h := D.active r u n hn
    have hfun : (fun s : ℝ => (ReconstructionR33m.w hκ F u {r} (tv r s)) n) =
        (fun t => ((Def021ChartR41b.chart L κ hκ).Φ
          (physical ⟨D.flow r t u.val, ((D.isFlow r u.val u.property).2.2 t).1⟩)) n) := by
      funext s
      have hsm : jointSmooth (hamFlows F {r}) (tv r s) u =
          ⟨D.flow r s u.val, ((D.isFlow r u.val u.property).2.2 s).1⟩ := by
        apply Subtype.ext
        rw [jointSmooth_single_val]
        exact D.flow_unique r (flowMap F r) (ActualModelTargetR53a.flow_isHam F r) u.val
          u.property s
      show ((Def021ChartR41b.chart L κ hκ).Φ (physical (jointSmooth (hamFlows F {r}) (tv r s) u))) n = _
      rw [hsm]
    rw [hfun]
    exact h
  exact AuditGapsS01Core.audit_gaps_core hκ F g hD u hu r a b (D.ω r u) (hact a ha) (hact b hb)
    missing

/-- **Finite families converge jointly** (the printed union bound): for every finite family of fixed
positive-action pairs and charge orders, the probability that some adjacent difference deviates from its
target by more than `ε` tends to zero. -/
theorem audit_gaps_joint (hκ : 0 < κ) (F : HigherFlows L κ) (g : Gauge)
    (hD : ReconstructionR33m.RD8362E5EBInput hκ F g)
    (D : Bind7BDEF033H02.DEF033Package hκ (Def021ChartR41b.chart L κ hκ).Φ)
    (u : Smooth L) (hu : ‖physical u‖ = 1) {ι : Type} [Fintype ι]
    (r : ι → ℕ) (a b : ι → ℤ)
    (ha : ∀ i, 0 < (QuantumNLS.RootIndexedMasses.masses hκ (physical u)).1 (a i))
    (hb : ∀ i, 0 < (QuantumNLS.RootIndexedMasses.masses hκ (physical u)).1 (b i))
    (missing : ι → ∀ N, MArr (N + 1) → ℝ) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun N => originalBorn hκ (physical u) hu N
      {m | ∃ i, ε < |withMissing L κ (N + 1) (r i) (a i) (b i) (missing i N) m -
        target (D.ω (r i) u) (a i) (b i)|}) atTop (𝓝 0) := by
  have hone : ∀ i, Tendsto (fun N => originalBorn hκ (physical u) hu N
      {m | ε < |withMissing L κ (N + 1) (r i) (a i) (b i) (missing i N) m -
        target (D.ω (r i) u) (a i) (b i)|}) atTop (𝓝 0) :=
    fun i => audit_gaps_printed hκ F g hD D u hu (r i) (a i) (b i) (ha i) (hb i) (missing i) ε hε
  have hsum : Tendsto (fun N => ∑ i, originalBorn hκ (physical u) hu N
      {m | ε < |withMissing L κ (N + 1) (r i) (a i) (b i) (missing i N) m -
        target (D.ω (r i) u) (a i) (b i)|}) atTop (𝓝 0) := by
    simpa using tendsto_finset_sum Finset.univ (fun i _ => hone i)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => bot_le) (fun N => ?_)
  refine le_trans (measure_mono ?_) (measure_iUnion_fintype_le _ _)
  intro m hm
  obtain ⟨i, hi⟩ := hm
  exact Set.mem_iUnion.2 ⟨i, hi⟩

end QuantumNLS.AuditGapsS01Headline

#print axioms QuantumNLS.AuditGapsS01Headline.audit_gaps_printed
#print axioms QuantumNLS.AuditGapsS01Headline.audit_gaps_joint

set_option maxHeartbeats 24000000 in
run_cmd do
  let env ← Lean.getEnv
  let modules := #[`QuantumNLS.AuditGapsS01Analytic, `QuantumNLS.AuditGapsS01Level,
    `QuantumNLS.AuditGapsS01Core]
  let some root := env.find? ``QuantumNLS.AuditGapsS01Headline.audit_gaps_printed
    | throwError "Missing headline"
  let mut type := root.type
  let mut binders : Array Lean.Name := #[]
  let mut usesInput := false
  let mut usesPackage := false
  while let .forallE binder dom body _ := type do
    binders := binders.push binder
    if dom.getUsedConstants.contains ``QuantumNLS.ReconstructionR33m.RD8362E5EBInput then
      usesInput := true
    if dom.getUsedConstants.contains ``QuantumNLS.Bind7BDEF033H02.DEF033Package then
      usesPackage := true
    type := body
  Lean.logInfo m!"HEADLINE_BINDERS {binders}"
  unless type.getUsedConstants.contains ``QuantumNLS.Def033CoreR24m.DifferenceLimit do
    throwError "Headline conclusion does not mention DifferenceLimit"
  unless usesInput do throwError "The dynamic hypothesis is not RD8362E5EBInput"
  unless usesPackage do throwError "The DEF-033 hypothesis is not DEF033Package"
  let mut pending : Array Lean.Name := #[``QuantumNLS.AuditGapsS01Headline.jointSmooth_single_val,
    ``QuantumNLS.AuditGapsS01Headline.audit_gaps_printed,
    ``QuantumNLS.AuditGapsS01Headline.audit_gaps_joint]
  for n in modules do
    let some idx := env.header.moduleNames.idxOf? n
      | throwError "Missing module {n}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty author module {n}"
    Lean.logInfo m!"AUDIT_MODULE {n} DECLARATIONS {names.size}"
    pending := pending ++ names
  let mut seen : Std.HashSet Lean.Name := {}
  let mut axioms : Std.HashSet Lean.Name := {}
  let mut heldHits : Array Lean.Name := #[]
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn "HeldGP14Tonelli").length > 1 ||
          n.components.any (fun c => c.toString == "RegularCut") ||
          n.toString.startsWith "QuantumNLS.RB7BindFinal." ||
          n.toString.startsWith "QuantumNLS.Bind7BDEF033H02.DEF033_package" then
        heldHits := heldHits.push n
      let some ci := env.find? n | throwError "Missing dependency {n}"
      if let .axiomInfo _ := ci then
        unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
          throwError "Nonstandard axiom {n}"
        axioms := axioms.insert n
      pending := pending ++ ci.type.getUsedConstants
      if let some v := ci.value? (allowOpaque := true) then
        pending := pending ++ v.getUsedConstants
  Lean.logInfo m!"AXIOM_AUDIT PASS constants={seen.size} axioms={axioms.toList} heldHits={heldHits}"
