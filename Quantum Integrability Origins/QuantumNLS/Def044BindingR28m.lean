import QuantumNLS.Def044ChartR28m
import QuantumNLS.Def044BindingR26m

/-! DEF-044 uses the same printed R-7B122087 input as DEF-033. The R26m
actual-chart input is equivalent at every DEF-021 chart. The new intermediates
reuse the frozen R26m conclusions and constructors. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

namespace QuantumNLS.Def044BindingR28m

open PhysicalTensor (L2T)
open Def033HierarchyR24m (Smooth physical)
open Def033CoreR24m (ActiveFrequency)
open HierarchyFlow (IsHamFlow hamiltonian)
open Def044D1SpectralR51a (QuantumRequirements ScalarRequirements)

variable {L κ : ℝ} [Fact (0 < L)]

/-- Specialize the exact shared predecessor to the actual chart. The indexed
mass in the shared conclusion is definitionally the R26m action. -/
theorem actual_input_of_shared (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ)
    (HierarchyR7B122087Input : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ) :
    Def044HierarchyR26m.HierarchyR7B122087Input hκ C :=
  fun hS hU hM => HierarchyR7B122087Input C.Φ (Def044ChartR28m.printed_chart hκ C)
    ((Def044ChartR28m.sobolev_iff hκ C).mp hS) hU hM

/-- Every normalized printed chart is the same physical chart. This also
transports the R26m conditional statement back to the full shared statement. -/
theorem shared_input_iff_actual (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ) :
    HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ ↔
      Def044HierarchyR26m.HierarchyR7B122087Input hκ C := by
  refine ⟨actual_input_of_shared hκ C, ?_⟩
  intro h w hw hS hU hM
  obtain ⟨he, _⟩ := Def044ChartR28m.printed_chart_maps hκ C w hw
  subst w
  exact h ((Def044ChartR28m.sobolev_iff hκ C).mpr hS) hU hM

theorem hierarchy_intermediate (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ)
    (HierarchyR7B122087Input : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ) :
    HierarchyInputR25m.HierarchyConclusion (κ := κ) C.Φ (Def044ChartR51a.action hκ) :=
  Def044HierarchyR26m.hierarchy_intermediate hκ C (actual_input_of_shared hκ C HierarchyR7B122087Input)

theorem dynamics_intermediate (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ)
    (HierarchyR7B122087Input : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ) :
    Def044HierarchyR26m.DynamicsInterface hκ C :=
  Def044HierarchyR26m.dynamics_intermediate hκ C (actual_input_of_shared hκ C HierarchyR7B122087Input)

theorem DEF033_higher_intermediate (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ)
    (HierarchyR7B122087Input : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ) :
    ∃ (Φ : ℕ → ℝ → (ℝ → ℂ) → (ℝ → ℂ))
      (hΦ : ∀ r, 2 ≤ r → IsHamFlow L (hamiltonian L κ r) (Φ r)),
      ∀ r (hr : 2 ≤ r) (u : Smooth L) n, 0 < Def044ChartR51a.action hκ (physical u) n →
        ∃! freq : ℝ, ActiveFrequency
          (fun t => C.Φ (physical ⟨Φ r t u.val, ((hΦ r hr u.val u.property).2.2 t).1⟩) n)
          (C.Φ (physical u) n) freq :=
  Def044HierarchyR26m.DEF033_higher_intermediate hκ C
    (actual_input_of_shared hκ C HierarchyR7B122087Input)

theorem active_targets_intermediate (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ)
    (HierarchyR7B122087Input : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ) :
    ∃ (Φ : ℕ → ℝ → (ℝ → ℂ) → (ℝ → ℂ))
      (hΦ : ∀ r, 2 ≤ r → IsHamFlow L (hamiltonian L κ r) (Φ r)),
      ∀ r (hr : 2 ≤ r) (u : Smooth L) (a b : ℤ),
        0 < Def044ChartR51a.action hκ (physical u) a →
        0 < Def044ChartR51a.action hκ (physical u) b →
        ∃! c : ℝ, Def044BindingR26m.ActiveTarget
          (fun n t => C.Φ (physical ⟨Φ r t u.val, ((hΦ r hr u.val u.property).2.2 t).1⟩) n)
          (fun n => C.Φ (physical u) n) a b c :=
  Def044BindingR26m.active_targets_intermediate hκ C
    (actual_input_of_shared hκ C HierarchyR7B122087Input)

/-- The three-clause constructor with the single shared hierarchy input.
The separately typed spectral requirements are the R26m requirements. -/
def DEF044_intermediate (hκ : 0 < κ) (u : Smooth L) (hu : ‖physical u‖ = 1)
    (C : Def021ChartR41b.Chart L κ hκ)
    (quantum : QuantumRequirements (L := L) hκ)
    (scalar : ScalarRequirements hκ (physical u) hu)
    (HierarchyR7B122087Input : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ) :
    Def044BindingR26m.MixedInterface hκ u hu :=
  Def044BindingR26m.DEF044_intermediate hκ u hu C quantum scalar
    (actual_input_of_shared hκ C HierarchyR7B122087Input)

end QuantumNLS.Def044BindingR28m

#print axioms QuantumNLS.Def044BindingR28m.actual_input_of_shared
#print axioms QuantumNLS.Def044BindingR28m.shared_input_iff_actual
#print axioms QuantumNLS.Def044BindingR28m.hierarchy_intermediate
#print axioms QuantumNLS.Def044BindingR28m.dynamics_intermediate
#print axioms QuantumNLS.Def044BindingR28m.DEF033_higher_intermediate
#print axioms QuantumNLS.Def044BindingR28m.active_targets_intermediate
#print axioms QuantumNLS.Def044BindingR28m.DEF044_intermediate

set_option maxHeartbeats 24000000 in
run_cmd do
  let env ← Lean.getEnv
  for n in #[``QuantumNLS.Def044BindingR28m.hierarchy_intermediate,
      ``QuantumNLS.Def044BindingR28m.dynamics_intermediate,
      ``QuantumNLS.Def044BindingR28m.DEF033_higher_intermediate,
      ``QuantumNLS.Def044BindingR28m.active_targets_intermediate,
      ``QuantumNLS.Def044BindingR28m.DEF044_intermediate] do
    let some ci := env.find? n | throwError "Missing intermediate: {n}"
    let mut typ := ci.type
    let mut shared : Nat := 0
    while true do
      match typ with
      | .forallE binder domain body _ =>
        if domain.getAppFn.isConstOf ``QuantumNLS.HierarchyInputR25m.HierarchyR7B122087Input then
          unless binder.toString == "HierarchyR7B122087Input" do
            throwError "Unexpected shared input binder in {n}: {binder}"
          shared := shared + 1
        if domain.getAppFn.isConstOf ``QuantumNLS.Def044HierarchyR26m.HierarchyR7B122087Input then
          throwError "Unexpected separate actual-chart input in {n}"
        typ := body
      | _ => break
    unless shared == 1 do
      throwError "Expected one shared input in {n}, found {shared}"
    Lean.logInfo m!"Single shared hierarchy input PASS: {n}"

  let prefixes := #["QuantumNLS.Def044BindingR28m.", "QuantumNLS.Def044ChartR28m."]
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if prefixes.any (fun pre => n.toString.startsWith pre ||
      n.toString.startsWith ("_private." ++ pre)) then
      pending := pending.push n
  let roots := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if ["HeldGP14Tonelli", "RegularCut"].any (fun s => (n.toString.splitOn s).length > 1) then
        throwError "Rejected dependency: {n}"
      let some ci := env.find? n | throwError "Missing dependency: {n}"
      match ci with
      | .axiomInfo _ =>
        unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
          throwError "Nonstandard axiom: {n}"
      | _ => pure ()
      pending := pending ++ ci.type.getUsedConstants
      if let some value := ci.value? (allowOpaque := true) then
        pending := pending ++ value.getUsedConstants
  Lean.logInfo m!"R28m aggregate audit PASS: {roots} own constants, {seen.size} reachable constants."
