import QuantumNLS.ActualModelCorollaryR53a

/-! R-E679E41D with the fixed-box quantifier order of PROP-025
(mixed_propagation.tex:68–100). -/
set_option autoImplicit false
noncomputable section
open Filter Topology
namespace QuantumNLS.ActualModelCorollaryR56a
open Def033HierarchyR24m BetheCoefficientTransform
open ActualModelTargetR53a ActualModelCorollaryR53a

variable {L κ : ℝ} [Fact (0 < L)]

/-- Fix the profile, sets, marginal rank and both boxes before choosing
the constant, finite-action error sequence and particle threshold. -/
def PROP025Input (hκ : 0 < κ) : Prop :=
  ∀ (u : Smooth L) (hu : ‖physical u‖ = 1)
    (M : Def044BindingR26m.MixedInterface hκ u hu)
    (I : Finset ℤ) (R : Finset ℕ) (k : ℕ) (Θ : ℤ → ℝ) (T : ℕ → ℝ),
    (∀ n ∈ I, 0 ≤ Θ n) → (∀ r ∈ R, 0 ≤ T r) →
    MainEstimate hκ M.chart.chart (higher M.dynamics.hierarchy) u I R k Θ T

/-- The actual-model corollary at each fixed box, with the constructed
actual DEF-044 interface and the explicit printed predecessor inputs. -/
theorem cor_MP_actual_model_intermediate (hκ : 0 < κ)
    (PROP025Input : PROP025Input (L := L) hκ)
    (HierarchyInput : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ)
    (u : Smooth L) (hu : ‖physical u‖ = 1)
    (I : Finset ℤ) (R : Finset ℕ) (k : ℕ) (Θ : ℤ → ℝ) (T : ℕ → ℝ)
    (hΘ : ∀ n ∈ I, 0 ≤ Θ n) (hT : ∀ r ∈ R, 0 ≤ T r) :
    MainEstimate hκ (ActualModelBindingR53a.chart (L := L) hκ)
      (higher (ActualModelBindingR53a.hierarchy_intermediate hκ HierarchyInput)) u I R k Θ T :=
  PROP025Input u hu (ActualModelBindingR53a.DEF044_intermediate hκ HierarchyInput u hu)
    I R k Θ T hΘ hT

/-- Include the source proof's window verification at the same hierarchy. -/
theorem actual_model_intermediate (hκ : 0 < κ)
    (PROP025Input : PROP025Input (L := L) hκ)
    (HierarchyInput : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ)
    (WindowInput : Prop025OInputs.WindowInput (L := L) hκ)
    (u : Smooth L) (hu : ‖physical u‖ = 1)
    (I : Finset ℤ) (R : Finset ℕ) (k : ℕ) (Θ : ℤ → ℝ) (T : ℕ → ℝ)
    (hΘ : ∀ n ∈ I, 0 ≤ Θ n) (hT : ∀ r ∈ R, 0 ≤ T r) :
    let F := higher (ActualModelBindingR53a.hierarchy_intermediate hκ HierarchyInput)
    WindowEstimate F ∧ MainEstimate hκ (ActualModelBindingR53a.chart (L := L) hκ)
      F u I R k Θ T :=
  ⟨actual_window_intermediate hκ WindowInput _,
    cor_MP_actual_model_intermediate hκ PROP025Input HierarchyInput u hu I R k Θ T hΘ hT⟩

end QuantumNLS.ActualModelCorollaryR56a

#print axioms QuantumNLS.ActualModelCorollaryR56a.cor_MP_actual_model_intermediate
#print axioms QuantumNLS.ActualModelCorollaryR56a.actual_model_intermediate
#print QuantumNLS.ActualModelCorollaryR56a.PROP025Input
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.ActualModelCorollaryR56a." ||
        n.toString.startsWith "_private.QuantumNLS.ActualModelCorollaryR56a." then
      pending := pending.push n
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn "HeldGP14Tonelli").length > 1 ||
          n.components.any (fun c => c.toString == "RegularCut") ||
          n == ``QuantumNLS.ActualModelCorollaryR53a.PROP025Input ||
          n == ``QuantumNLS.ActualModelCorollaryR53a.PacketEstimate ||
          n == ``QuantumNLS.Def044HierarchyR26m.HierarchyR7B122087Input ||
          n == ``QuantumNLS.ActualModelHierarchyR52a.HierarchyInput ||
          n == ``QuantumNLS.Def044InterfacesR51a.Def033Input then
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
  Lean.logInfo m!"R56a recursive audit PASS: {own} own constants; {seen.size} transitive constants; standard only."
