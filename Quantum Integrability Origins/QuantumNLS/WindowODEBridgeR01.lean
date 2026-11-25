import QuantumNLS.WindowBindingR46b
import QuantumNLS.AllOrderEnergyFinalR57a

/-! # WindowODEBridgeR01: the R-E59628C9 window trajectory in R-568BCDF8 (R57a)

Author-side support for the one open R57a item ("identification of the accepted
window trajectory with the physical ODE formulation"). Nothing frozen is edited.

* Trajectory object.  The accepted-route statement `Prop025OInputs.WindowInput`
  (R-E59628C9, reviewed terra_review r242, bound by `Bind7BE59628C9H01.window_bound`)
  and R57a's `AllOrderEnergyPredecessorsR57a.WindowRate` use the SAME constant
  `Prop025OInputs.IsWindowTrajectory` (the auxiliary-time solution of
  `y(0) = u`, `ẏ = -i ∇(Σ_r t_r h_{r,a})(y)` on `[0,1]`), the same cut sequence
  `PROP017UniformN.cutSeq`, the same carrier `physical`, and the same joint flow
  `Def033HierarchyR24m.jointSmooth`.  This is checked at the constant level by the
  `run_cmd` block below, and in Lean by `windowRate_iff_windowInput_form` (`Iff.rfl`
  after the frozen cutoff equivalence).
* Statement.  `windowRate_of_windowInput` derives R57a's rate, at the actual
  hierarchy flows, from the accepted statement `WindowInput` itself (orders `r ≥ 2`).
  `windowInput_r57a` derives the full R57a named input `WindowRE59628C9Input`
  (all orders, including the staged orders 0 and 1, every `HamFlows` family) from
  the frozen `WindowAssemblyR46b.window_all_orders_intermediate` and the shared
  hierarchy input.  `window_trajectory_exists` records that the trajectories
  quantified in R57a's rate exist (the rate is not vacuous).
* Consumption.  `energy_allorder_energy_window_bound` is R57a's
  `energy_allorder_energy_intermediate` with the R-E59628C9 input discharged. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Filter Topology

namespace QuantumNLS.WindowODEBridgeR01
open PhysicalTensor Def033HierarchyR24m HierarchyFlow ClassicalCharges
open ActualModelBindingR53a ActualModelTargetR53a
open AllOrderEnergyInputsR56a (flows)
open AllOrderEnergyPredecessorsR57a PROP017UniformN
variable {L κ : ℝ} [Fact (0 < L)]

/-- Trajectory identification.  R57a's rate, read through the frozen cutoff
equivalence, is the indexed rate over exactly `Prop025OInputs.IsWindowTrajectory`
at the cut `cutSeq L l`, from `physical u`, compared with
`physical (jointSmooth F t u)` — the trajectory, cut, initial value and target of
the accepted `Prop025OInputs.WindowInput`. -/
theorem windowRate_iff_windowInput_form {R : Finset ℕ} (F : HamFlows L κ R)
    (T : ℕ → ℝ) (K : Set (Smooth L)) :
    WindowRate F T K ↔ ∃ C : ℝ, 0 ≤ C ∧ ∃ l0 : ℕ, ∀ l : ℕ, l0 ≤ l → ∀ u ∈ K,
      ∀ t : ℕ → ℝ, (∀ r ∈ R, |t r| ≤ T r) →
      ∀ y : ℝ → L2T L,
        Prop025OInputs.IsWindowTrajectory (L := L) κ R t (cutSeq L l) (physical u) y →
        ‖y 1 - physical (jointSmooth F t u)‖ ≤ C * (cutSeq L l) ^ (-(1/4 : ℝ)) :=
  windowRate_iff_indexed F T K

/-- From the accepted statement.  `Prop025OInputs.WindowInput` (R-E59628C9, at the
actual chart, Sobolev homeomorphisms and the accepted R-C5645D32 antecedent, with
the actual hierarchy flows) gives R57a's `WindowRate` at the actual flows
`hamFlows (flows hκ H) R` for every family of orders `r ≥ 2`, every compact box and
every compact smooth class. -/
theorem windowRate_of_windowInput (hκ : 0 < κ)
    (HierarchyR7B122087Input : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ)
    (WindowInput : Prop025OInputs.WindowInput (L := L) hκ)
    (R : Finset ℕ) (hR : ∀ r ∈ R, 2 ≤ r) (T : ℕ → ℝ) (hT : ∀ r, 0 ≤ T r)
    (K : Set (Smooth L)) (hK : IsCompact K) :
    WindowRate (hamFlows (flows hκ HierarchyR7B122087Input) R) T K := by
  let d := max 2 (R.sup id)
  have hRd (r : ℕ) (hr : r ∈ R) : 2 ≤ r ∧ r ≤ d :=
    ⟨hR r hr, (Finset.le_sup (f := id) hr).trans (le_max_right _ _)⟩
  have h := WindowInput (chart (L := L) hκ).Φ (printed_chart hκ) (sobolev hκ)
    (Prop025OInputs.gradient_removal hκ)
    (flowMap (flows hκ HierarchyR7B122087Input))
    (fun r _ => flow_isHam (flows hκ HierarchyR7B122087Input) r)
    d (le_max_left _ _) R hRd T hT K hK
  exact (windowRate_iff_indexed _ T K).2 h

/-- The full R57a named input, all orders.  R57a's `WindowRE59628C9Input` (every
`HamFlows` family, every finite family with largest order at most `d`, including
the staged orders 0 and 1; fixed-datum and compact-class clauses) follows from the
shared hierarchy input through the frozen
`WindowAssemblyR46b.window_all_orders_intermediate`. -/
theorem windowInput_r57a (hκ : 0 < κ)
    (HierarchyR7B122087Input : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ) :
    WindowRE59628C9Input (L := L) hκ := by
  intro w hw _hsob _hgrad d _hd R hR F T hT
  have hrate (K : Set (Smooth L)) (hK : IsCompact K) : WindowRate F T K := by
    obtain ⟨A, hA, l0, h⟩ := WindowAssemblyR46b.window_all_orders_intermediate hκ
      HierarchyR7B122087Input w hw d R hR F T hT K hK
    exact (windowRate_iff_indexed F T K).2 ⟨A, hA, l0, fun l hl u hu t ht => (h l hl u hu t ht).2⟩
  exact ⟨fun u => hrate {u} isCompact_singleton, fun K hK _ => hrate K hK⟩

/-- Non-vacuity.  At the actual hierarchy flows, for every finite family and every
compact box and class, eventually in the cut index a physical window trajectory in
the sense of `Prop025OInputs.IsWindowTrajectory` exists for every datum and time. -/
theorem window_trajectory_exists (hκ : 0 < κ)
    (HierarchyR7B122087Input : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ)
    (R : Finset ℕ) (T : ℕ → ℝ) (hT : ∀ r, 0 ≤ T r) (K : Set (Smooth L)) (hK : IsCompact K) :
    ∃ l0 : ℕ, ∀ l ≥ l0, ∀ u ∈ K, ∀ t : ℕ → ℝ, (∀ r ∈ R, |t r| ≤ T r) →
      ∃ y, Prop025OInputs.IsWindowTrajectory (L := L) κ R t (cutSeq L l) (physical u) y := by
  let d := max 2 (R.sup id)
  have hRd (r : ℕ) (hr : r ∈ R) : r ≤ d :=
    (Finset.le_sup (f := id) hr).trans (le_max_right _ _)
  obtain ⟨_, _, l0, h⟩ := WindowAssemblyR46b.window_all_orders_intermediate hκ
    HierarchyR7B122087Input (chart (L := L) hκ).Φ (printed_chart hκ) d R hRd
    (hamFlows (flows hκ HierarchyR7B122087Input) R) T hT K hK
  exact ⟨l0, fun l hl u hu t ht => (h l hl u hu t ht).1⟩

/-- R57a consumption.  `energy_allorder_energy_intermediate` with the R-E59628C9
named input supplied by `windowInput_r57a`; the remaining named inputs are the
hierarchy, actual-model and weighted inputs, unchanged. -/
theorem energy_allorder_energy_window_bound (hκ : 0 < κ)
    (HierarchyR7B122087Input : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ)
    (ActualModelRE679E41DInput :
      AllOrderEnergyInputsR57a.ActualModelRE679E41DInput (L := L) hκ HierarchyR7B122087Input)
    (WeightedR115CAA16Input : WeightedR115CAA16Input (L := L) hκ)
    (u : Smooth L) (hu : ‖physical u‖ = 1) (R : Finset ℕ)
    (K : Set (ℕ → ℝ)) (hK : IsCompact K) :
    (∀ (ψ : ∀ N, TensorCarrier.HilbertTensorPower ℂ (L2T L) N)
      (hψ : EnergyPreparationDef.EnergyPreparation κ (physical u) ψ) (k : ℕ), 1 ≤ k →
      AllOrderEnergyAssemblyR57a.EnergyLimit hκ HierarchyR7B122087Input u
        (fun n => ⟨ψ (n+1), hψ.mem_sector (n+1)⟩) R K k) ∧
    EnergyPreparationDef.EnergyPreparation κ (physical u)
      (fun N => TensorCarrier.htpow N (physical u)) ∧
    AllOrderEnergyPacketsR57a.CommonEnergyPackets hκ u ∧
    (∀ T : ℕ → ℝ, (∀ r, 0 ≤ T r) →
      WindowRate (hamFlows (flows hκ HierarchyR7B122087Input) R) T {u}) :=
  AllOrderEnergyFinalR57a.energy_allorder_energy_intermediate hκ HierarchyR7B122087Input
    (windowInput_r57a hκ HierarchyR7B122087Input) ActualModelRE679E41DInput
    WeightedR115CAA16Input u hu R K hK

end QuantumNLS.WindowODEBridgeR01

#print axioms QuantumNLS.WindowODEBridgeR01.windowRate_iff_windowInput_form
#print axioms QuantumNLS.WindowODEBridgeR01.windowRate_of_windowInput
#print axioms QuantumNLS.WindowODEBridgeR01.windowInput_r57a
#print axioms QuantumNLS.WindowODEBridgeR01.window_trajectory_exists
#print axioms QuantumNLS.WindowODEBridgeR01.energy_allorder_energy_window_bound

-- Constant-level identification: the trajectory, cut, carrier and joint flow
-- constants used by R57a's `WindowRate` coincide with those of the accepted
-- `Prop025OInputs.WindowInput` and of `WindowAssemblyR46b.window_all_orders_intermediate`.
run_cmd do
  let env ← Lean.getEnv
  let get (n : Lean.Name) : Lean.Elab.Command.CommandElabM Lean.Expr := do
    match env.find? n with
    | some ci => pure ci.type
    | none => throwError "missing {n}"
  let val (n : Lean.Name) : Lean.Elab.Command.CommandElabM Lean.Expr := do
    match env.find? n with
    | some ci => match ci.value? with
      | some v => pure v
      | none => throwError "no value {n}"
    | none => throwError "missing {n}"
  let rate ← val ``QuantumNLS.AllOrderEnergyPredecessorsR57a.WindowRate
  let accepted ← val ``QuantumNLS.Prop025OInputs.WindowInput
  let allOrders ← get ``QuantumNLS.WindowAssemblyR46b.window_all_orders_intermediate
  let shared : List Lean.Name :=
    [``QuantumNLS.Prop025OInputs.IsWindowTrajectory, ``QuantumNLS.PROP017UniformN.cutSeq,
     ``QuantumNLS.Def033HierarchyR24m.physical, ``QuantumNLS.Def033HierarchyR24m.jointSmooth]
  for c in shared do
    for (lbl, e) in [("R57a WindowRate", rate), ("accepted WindowInput", accepted),
        ("window_all_orders_intermediate", allOrders)] do
      unless e.getUsedConstants.contains c do
        throwError "{lbl} does not use {c}"
  let alt : List Lean.Name :=
    [`QuantumNLS.ActualModelHierarchyR52a.jointSmooth, `QuantumNLS.PROP017CutFamily.cutSeq,
     `QuantumNLS.Def044InterfacesR51a.physical]
  for c in alt do
    for (lbl, e) in [("R57a WindowRate", rate), ("accepted WindowInput", accepted),
        ("window_all_orders_intermediate", allOrders)] do
      if e.getUsedConstants.contains c then
        throwError "{lbl} uses the alternative constant {c}"
  Lean.logInfo m!"WindowODEBridgeR01 trajectory identification PASS: R57a WindowRate, accepted WindowInput and window_all_orders_intermediate share IsWindowTrajectory, cutSeq, physical and jointSmooth."

-- Recursive type/value audit of every own declaration.
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.WindowODEBridgeR01." ||
        n.toString.startsWith "_private.QuantumNLS.WindowODEBridgeR01." then
      pending := pending.push n
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn "HeldGP14Tonelli").length > 1 ||
          n.components.any (fun c => c.toString == "RegularCut") then
        throwError "Held dependency: {n}"
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
  Lean.logInfo m!"WindowODEBridgeR01 aggregate audit PASS: {own} own constants; {seen.size} transitive constants; standard axioms only; no held identifiers."
