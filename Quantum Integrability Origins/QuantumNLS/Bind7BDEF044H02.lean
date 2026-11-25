import QuantumNLS.Bind7BDEF044H01
import QuantumNLS.Bind7BDEF033H02
import QuantumNLS.Def044WindowR26m

/-!
# Bind7BDEF044H02: DEF-044 with the DEF-033 adapter and the window-functional identification discharged

PRINTED SOURCE: `source-text/chapters/propagation/mixed_propagation.tex`, lines 12-39 (`\begin{definition}` at 12,
`\DefinitionID{DEF-044}` at 13, `\end{definition}` at 39;
label `def:PF-mixed-interfaces`, "Interfaces for the mixed propagation theorem"; `scope.json` `statement_location`
file `chapters/propagation/mixed_propagation.tex`, line 12, offset 544; file SHA-256
`24ab083b54ff60951edb92acc0c86cfcde5274bfe6a0a875985ce19d9a6e69df`).

This module discharges the two qualifications left by review record r84 / r91 on `Bind7BDEF044H01`:
 (a) "a checked DEF-033 adapter ... to the same physical trajectory and chart, endpoint frequencies and
     receiver-minus-donor phase/sign, all-order and order-2 conventions, original Born law and missing-donor
     convention": the structure `DEF044Final` carries the accepted-API object `DEF033Package` (Bind7BDEF033H02,
     all printed DEF-033 clauses) at the chart of the DEF-044 mixed interface, together with the adapter fields
     `chart_is_actual`, `printed_chart`, `chart_unique`, `action_eq`, `same_flow`, `endpoints`, `phase_sign`,
     `total_eq`, `adjacent_eq`, `born_eq`;
 (b) "the direct window-functional identification was source-inspected rather than independently kernel-checked":
     the field `window_identification`, proved by `Q07GradientRemovalR24.T_eq_printed` composed with the canonical
     Sobolev inclusion `Sobolev.H02.mono` (the functional of the printed estimate is `windowError`, which is
     `T` after the canonical inclusion; at every represented smooth profile it equals the real charge minus the
     full-mass window contour).

The `mixed` field is exactly the frozen H01 value `Bind7BDEF044H01.DEF044_bound hκ u hu` (`mixed_eq`), so the
three printed DEF-044 clauses (spectral, chart, dynamics = hierarchy + window differentials) are the H01 ones,
with the shared hierarchy input discharged by `RB7BindFinal.hierarchyInputR25m_unconditional`.  This is a
`def` returning a structure, as is H01.

Remaining hypotheses: `hκ : 0 < κ`, `u : Smooth L`, `hu : ‖physical u‖ = 1` (as H01).  No acceptance claim;
R-7B122087 is held for the owner ruling on the DEF-024 predecessor gate.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Filter MeasureTheory Topology
namespace QuantumNLS.Bind7BDEF044H02
open QuantumNLS.PhysicalTensor QuantumNLS.ClassicalCharges QuantumNLS.HierarchyFlow
open QuantumNLS.Def033HierarchyR24m (Smooth physical)
open QuantumNLS.Def033CoreR24m (ActiveFrequency phase)
open QuantumNLS.Def044InterfacesR51a (windowError regularity_mono)
open QuantumNLS.Q07TailBindingR24 (regularity)
open QuantumNLS.SmoothScalarMomentsPhysical (smoothL2)
variable {L κ : ℝ} [Fact (0 < L)]

/-- (b) The functional of the printed window estimate, at every represented smooth profile `f` of a
point `u` of the common `H^{2d+4}` ball space, is the real charge minus the full-mass window contour. -/
def WindowIdentification (hκ : 0 < κ) : Prop :=
  ∀ (d r : ℕ) (hr : r ≤ d) (h : ℝ) (l : ℕ) (u : Sobolev.H02 L (regularity d))
    (f : ℝ → ℂ) (hf : SmoothPeriodic L f), u.val = smoothL2 hf →
    windowError hκ d r hr h l u = (charge L κ f (r + 1)).re -
      QuantumNLS.Q07IntegratedHessiansR16.windowContour hκ r (QuantumNLS.PROP017UniformN.cutSeq L l) h u.val

/-- (b), proved. -/
theorem window_identification (hκ : 0 < κ) : WindowIdentification (L := L) hκ := by
  intro d r hr h l u f hf hu
  -- `rfl` for this projection equality is accepted by the elaborator but exhausts the kernel; the rfl-lemma
  -- `fieldIncl_val` (with `H02.mono` unfolded by one delta step) is checked instantly.
  have hmv : (Sobolev.H02.mono (L := L) (regularity_mono hr) u).val = u.val :=
    Sobolev.fieldIncl_val (Sobolev.def002 L _) (Sobolev.def002 L _) zero_le_one
      (Sobolev.def002_le_of_le L (regularity_mono hr)) u
  have key := QuantumNLS.Q07GradientRemovalR24.T_eq_printed (L := L) hκ r l h
    (Sobolev.H02.mono (regularity_mono hr) u) hf (hmv.trans hu)
  rw [hmv] at key
  exact key

/-- DEF-044 at a physical unit profile: the three-clause mixed interface of H01, the checked DEF-033 adapter,
and the window-functional identification. -/
structure DEF044Final (hκ : 0 < κ) (u : Smooth L) (hu : ‖physical u‖ = 1) : Type where
  /-- The three printed clauses, exactly the frozen H01 value. -/
  mixed : QuantumNLS.Def044BindingR26m.MixedInterface hκ u hu
  mixed_eq : mixed = QuantumNLS.Bind7BDEF044H01.DEF044_bound hκ u hu
  /-- (a) The chart of the mixed interface is the actual DEF-021 chart, and it is a printed chart. -/
  chart_is_actual : mixed.chart.chart = QuantumNLS.Def021ChartR41b.chart L κ hκ
  printed_chart : QuantumNLS.REF88PrintedChart.PrintedChart hκ mixed.chart.chart.Φ
  /-- (a) Every printed chart (the chart parameter of DEF-033) is this chart. -/
  chart_unique : ∀ w : L2T L → QuantumNLS.REF88Chart.K,
    QuantumNLS.REF88PrintedChart.PrintedChart hκ w → w = mixed.chart.chart.Φ
  /-- (a) All printed DEF-033 clauses, at the chart of DEF-044. -/
  def033 : QuantumNLS.Bind7BDEF033H02.DEF033Package hκ mixed.chart.chart.Φ
  /-- (a) The DEF-044 action is the DEF-033 indexed mass. -/
  action_eq : ∀ (v : L2T L) (n : ℤ),
    QuantumNLS.Def044ChartR51a.action hκ v n = (QuantumNLS.RootIndexedMasses.masses hκ v).1 n
  /-- (a) Same physical trajectory: every family of smooth Hamiltonian flows of the DEF-044 hierarchy
  (orders `r ≥ 2`) is the DEF-033 flow. -/
  same_flow : ∀ (Φ' : ℕ → ℝ → (ℝ → ℂ) → (ℝ → ℂ))
    (_ : ∀ r, 2 ≤ r → IsHamFlow L (hamiltonian L κ r) (Φ' r)) (r : ℕ), 2 ≤ r →
    ∀ (v : Smooth L) (t : ℝ), Φ' r t v.val = def033.flow r t v.val
  /-- (a) Endpoint frequencies on the same trajectory and chart: for positive-action endpoints the DEF-044
  `ActiveTarget` along any DEF-044 hierarchy flow is exactly the DEF-033 target `ω_{r,b}(v) - ω_{r,a}(v)`,
  and it is the only one. -/
  endpoints : ∀ (Φ' : ℕ → ℝ → (ℝ → ℂ) → (ℝ → ℂ))
    (hΦ' : ∀ r, 2 ≤ r → IsHamFlow L (hamiltonian L κ r) (Φ' r)) (r : ℕ) (hr : 2 ≤ r)
    (v : Smooth L) (a b : ℤ),
    0 < QuantumNLS.Def044ChartR51a.action hκ (physical v) a →
    0 < QuantumNLS.Def044ChartR51a.action hκ (physical v) b →
    QuantumNLS.Def044BindingR26m.ActiveTarget
      (fun n t => mixed.chart.chart.Φ (physical ⟨Φ' r t v.val, ((hΦ' r hr v.val v.property).2.2 t).1⟩) n)
      (fun n => mixed.chart.chart.Φ (physical v) n) a b
      (QuantumNLS.Def033CoreR24m.target (def033.ω r v) a b) ∧
    ∀ c : ℝ, QuantumNLS.Def044BindingR26m.ActiveTarget
      (fun n t => mixed.chart.chart.Φ (physical ⟨Φ' r t v.val, ((hΦ' r hr v.val v.property).2.2 t).1⟩) n)
      (fun n => mixed.chart.chart.Φ (physical v) n) a b c →
      c = QuantumNLS.Def033CoreR24m.target (def033.ω r v) a b
  /-- (a) Receiver-minus-donor sign of the quantum phase ratio. -/
  phase_sign : ∀ r (v : Smooth L) (a b : ℤ) (t : ℝ),
    0 < QuantumNLS.Def044ChartR51a.action hκ (physical v) a →
    0 < QuantumNLS.Def044ChartR51a.action hκ (physical v) b →
    phase t (def033.ω r v b) / phase t (def033.ω r v a) =
      phase t (QuantumNLS.Def033CoreR24m.target (def033.ω r v) a b)
  /-- (a) The DEF-044 total/adjacent abbreviations and the original Born law are the DEF-033 ones. -/
  adjacent_eq : ∀ (N r : ℕ) (a b : ℤ) (m : QuantumNLS.BetheLabels.MArr N)
    (hd : QuantumNLS.Occupation.DonorOK a (QuantumNLS.BetheCoefficientTransform.marrArr N m).1),
    QuantumNLS.Def044BindingR26m.adjacent (L := L) (κ := κ) N r a b m hd =
      QuantumNLS.TerraMultiRound12Definitions.adjacentDifference L κ N r a b m hd
  total_eq : ∀ (N r : ℕ) (a b : ℤ) (missing : QuantumNLS.BetheLabels.MArr N → ℝ)
    (m : QuantumNLS.BetheLabels.MArr N),
    QuantumNLS.Def044BindingR26m.total (L := L) (κ := κ) N r a b missing m =
      QuantumNLS.Def033CoreR24m.withMissing L κ N r a b missing m
  born_eq : ∀ (v : L2T L) (hv : ‖v‖ = 1) (N : ℕ),
    QuantumNLS.Def044BindingR26m.originalBorn hκ v hv N = QuantumNLS.Def033CoreR24m.originalBorn hκ v hv N
  /-- (b) The window-functional identification. -/
  window_identification : WindowIdentification (L := L) hκ

/-- DEF-044 with both qualifications discharged. -/
def DEF044_final (hκ : 0 < κ) (u : Smooth L) (hu : ‖physical u‖ = 1) : DEF044Final hκ u hu :=
  let M := QuantumNLS.Bind7BDEF044H01.DEF044_bound hκ u hu
  have hP : QuantumNLS.REF88PrintedChart.PrintedChart hκ M.chart.chart.Φ :=
    QuantumNLS.Def044ChartR28m.printed_chart hκ M.chart.chart
  let P := QuantumNLS.Bind7BDEF033H02.DEF033_package hκ M.chart.chart.Φ hP
  have hsame : ∀ (Φ' : ℕ → ℝ → (ℝ → ℂ) → (ℝ → ℂ))
      (_ : ∀ r, 2 ≤ r → IsHamFlow L (hamiltonian L κ r) (Φ' r)) (r : ℕ), 2 ≤ r →
      ∀ (v : Smooth L) (t : ℝ), Φ' r t v.val = P.flow r t v.val :=
    fun Φ' hΦ' r hr v t => P.flow_unique r (Φ' r) (hΦ' r hr) v.val v.property t
  have htraj : ∀ (Φ' : ℕ → ℝ → (ℝ → ℂ) → (ℝ → ℂ))
      (hΦ' : ∀ r, 2 ≤ r → IsHamFlow L (hamiltonian L κ r) (Φ' r)) (r : ℕ) (hr : 2 ≤ r)
      (v : Smooth L) (n : ℤ),
      (fun t => M.chart.chart.Φ (physical ⟨Φ' r t v.val, ((hΦ' r hr v.val v.property).2.2 t).1⟩) n) =
      (fun t => M.chart.chart.Φ
        (physical ⟨P.flow r t v.val, ((P.isFlow r v.val v.property).2.2 t).1⟩) n) := by
    intro Φ' hΦ' r hr v n
    funext t
    have hs : (⟨Φ' r t v.val, ((hΦ' r hr v.val v.property).2.2 t).1⟩ : Smooth L) =
        ⟨P.flow r t v.val, ((P.isFlow r v.val v.property).2.2 t).1⟩ :=
      Subtype.ext (hsame Φ' hΦ' r hr v t)
    rw [hs]
  have hact : ∀ (r : ℕ) (v : Smooth L) (a : ℤ),
      0 < QuantumNLS.Def044ChartR51a.action hκ (physical v) a →
      0 < (QuantumNLS.RootIndexedMasses.masses hκ (physical v)).1 a := fun _ _ _ h => h
  { mixed := M
    mixed_eq := rfl
    chart_is_actual :=
      QuantumNLS.Def044PhysicalBindingR54a.chart_eq hκ u hu
        (QuantumNLS.RB7BindFinal.hierarchyInputR25m_unconditional (L := L) hκ)
    printed_chart := hP
    chart_unique := fun w hw =>
      (QuantumNLS.Def044ChartR28m.printed_chart_maps hκ M.chart.chart w hw).1
    def033 := P
    action_eq := fun v n => rfl
    same_flow := hsame
    endpoints := fun Φ' hΦ' r hr v a b ha hb => by
      have hta := P.active r v a (hact r v a ha)
      have htb := P.active r v b (hact r v b hb)
      have hcα : ∀ n, (fun t => M.chart.chart.Φ
          (physical ⟨Φ' r t v.val, ((hΦ' r hr v.val v.property).2.2 t).1⟩) n) =
          (fun t => M.chart.chart.Φ
            (physical ⟨P.flow r t v.val, ((P.isFlow r v.val v.property).2.2 t).1⟩) n) :=
        fun n => htraj Φ' hΦ' r hr v n
      have hT : QuantumNLS.Def044BindingR26m.ActiveTarget
          (fun n t => M.chart.chart.Φ (physical ⟨Φ' r t v.val, ((hΦ' r hr v.val v.property).2.2 t).1⟩) n)
          (fun n => M.chart.chart.Φ (physical v) n) a b
          (QuantumNLS.Def033CoreR24m.target (P.ω r v) a b) := by
        refine ⟨P.ω r v a, P.ω r v b, ?_, ?_, P.target_eq r v a b (hact r v a ha) (hact r v b hb)⟩
        · simpa only [hcα a] using hta
        · simpa only [hcα b] using htb
      exact ⟨hT, fun c hc => QuantumNLS.Def044BindingR26m.active_target_unique hc hT⟩
    phase_sign := fun r v a b t ha hb => by
      rw [P.target_eq r v a b (hact r v a ha) (hact r v b hb)]
      exact QuantumNLS.Def033CoreR24m.phase_difference t (P.ω r v b) (P.ω r v a)
    adjacent_eq := fun N r a b m hd => rfl
    total_eq := fun N r a b missing m => rfl
    born_eq := fun v hv N => rfl
    window_identification := window_identification hκ }

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

open Lean Meta in
/-- The structure type mentions the reviewed definitions of the adapter and the window identification. -/
private def mentionsAll (n : Name) (required : List Name) : MetaM (List Name) := do
  let env ← getEnv
  let some ci := env.find? n | throwError "missing {n}"
  let used := ci.type.getUsedConstants
  return required.filter fun c => !used.contains c

end QuantumNLS.Bind7BDEF044H02

set_option maxHeartbeats 16000000 in
open Lean Meta Elab Command in
run_cmd liftTermElabM do
  let missing ← QuantumNLS.Bind7BDEF044H02.mentionsAll ``QuantumNLS.Bind7BDEF044H02.DEF044Final.mk
    [``QuantumNLS.Def044BindingR26m.MixedInterface, ``QuantumNLS.Bind7BDEF044H01.DEF044_bound,
     ``QuantumNLS.Bind7BDEF033H02.DEF033Package, ``QuantumNLS.Def044BindingR26m.ActiveTarget,
     ``QuantumNLS.Def033CoreR24m.target, ``QuantumNLS.Def033CoreR24m.phase,
     ``QuantumNLS.Def044BindingR26m.total, ``QuantumNLS.Def044BindingR26m.adjacent,
     ``QuantumNLS.Def044BindingR26m.originalBorn, ``QuantumNLS.Bind7BDEF044H02.WindowIdentification,
     ``QuantumNLS.REF88PrintedChart.PrintedChart, ``QuantumNLS.Def021ChartR41b.chart]
  unless missing.isEmpty do throwError "DEF044Final does not mention: {missing}"
  let (n1, a1) ← QuantumNLS.Bind7BDEF044H02.transitiveAudit ``QuantumNLS.Bind7BDEF044H02.DEF044_final
  let (n2, a2) ← QuantumNLS.Bind7BDEF044H02.transitiveAudit ``QuantumNLS.Bind7BDEF044H02.window_identification
  logInfo m!"Bind7BDEF044H02 PASS: DEF044_final closure {n1} constants ({a1} standard axioms); window_identification closure {n2} constants ({a2} standard axioms); no held identifiers."

#print axioms QuantumNLS.Bind7BDEF044H02.window_identification
#print axioms QuantumNLS.Bind7BDEF044H02.DEF044_final

end
