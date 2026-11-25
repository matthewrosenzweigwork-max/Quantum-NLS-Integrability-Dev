import QuantumNLS.Def044PhysicalSpectralR54a
import QuantumNLS.Def044BindingR28m

/-! Insert the physical spectral witnesses into the frozen R28m entry
point at the actual DEF-021 chart. The only pending input is the exact
shared R-7B122087 proposition already used by R28m. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

namespace QuantumNLS.Def044PhysicalBindingR54a

open Def033HierarchyR24m (Smooth physical)

variable {L κ : ℝ} [Fact (0 < L)]

/-- The R28m constructor now receives both spectral requirements from
the physical assembly at this profile. -/
def DEF044_physical_intermediate (hκ : 0 < κ) (u : Smooth L) (hu : ‖physical u‖ = 1)
    (HierarchyR7B122087Input : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ) :
    Def044BindingR26m.MixedInterface hκ u hu :=
  let S := Def044PhysicalSpectralR54a.spectral hκ u hu
  Def044BindingR28m.DEF044_intermediate hκ u hu (Def021ChartR41b.chart L κ hκ)
    S.quantum S.scalar HierarchyR7B122087Input

/-- The mixed carrier retains the exact spectral record at this profile. -/
theorem spectral_eq (hκ : 0 < κ) (u : Smooth L) (hu : ‖physical u‖ = 1)
    (HierarchyR7B122087Input : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ) :
    (DEF044_physical_intermediate hκ u hu HierarchyR7B122087Input).spectral =
      Def044PhysicalSpectralR54a.spectral hκ u hu := rfl

/-- The chart in the mixed carrier is the physical chart supplied to R28m. -/
theorem chart_eq (hκ : 0 < κ) (u : Smooth L) (hu : ‖physical u‖ = 1)
    (HierarchyR7B122087Input : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ) :
    (DEF044_physical_intermediate hκ u hu HierarchyR7B122087Input).chart.chart =
      Def021ChartR41b.chart L κ hκ := rfl

/-- The two frozen entry points agree on the physical witnesses under the
checked R28m shared-input equivalence. -/
theorem agrees_with_R26m (hκ : 0 < κ) (u : Smooth L) (hu : ‖physical u‖ = 1)
    (HierarchyR7B122087Input : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ) :
    DEF044_physical_intermediate hκ u hu HierarchyR7B122087Input =
      Def044BindingR26m.DEF044_intermediate hκ u hu (Def021ChartR41b.chart L κ hκ)
        (Def044PhysicalSpectralR54a.spectral hκ u hu).quantum
        (Def044PhysicalSpectralR54a.spectral hκ u hu).scalar
        ((Def044BindingR28m.shared_input_iff_actual hκ (Def021ChartR41b.chart L κ hκ)).mp
          HierarchyR7B122087Input) := rfl

end QuantumNLS.Def044PhysicalBindingR54a

#print axioms QuantumNLS.Def044PhysicalBindingR54a.DEF044_physical_intermediate
#print axioms QuantumNLS.Def044PhysicalBindingR54a.spectral_eq
#print axioms QuantumNLS.Def044PhysicalBindingR54a.chart_eq
#print axioms QuantumNLS.Def044PhysicalBindingR54a.agrees_with_R26m

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let names := #[``QuantumNLS.Def044PhysicalSpectralR54a.spectral,
    ``QuantumNLS.Def044PhysicalBindingR54a.DEF044_physical_intermediate]
  for n in names do
    let some ci := env.find? n | throwError "Missing assembly: {n}"
    let mut typ := ci.type
    let mut shared : Nat := 0
    let mut binders : Nat := 0
    while true do
      match typ with
      | .forallE binder domain body _ =>
        binders := binders + 1
        if domain.getAppFn.isConstOf ``QuantumNLS.HierarchyInputR25m.HierarchyR7B122087Input then
          unless binder.toString == "HierarchyR7B122087Input" do
            throwError "Unexpected hierarchy binder name in {n}: {binder}"
          shared := shared + 1
        typ := body
      | _ => break
    let expected : Nat := if n == names[0]! then 0 else 1
    unless shared == expected && binders == 6 + expected do
      throwError "Unexpected binder count in {n}: {shared} hierarchy, {binders} total"
    Lean.logInfo m!"Round54 assembly binders PASS: {n}: {shared} hierarchy, {binders} total."

  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Def044PhysicalBindingR54a." ||
        n.toString.startsWith "_private.QuantumNLS.Def044PhysicalBindingR54a." then
      pending := pending.push n
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn "HeldGP14Tonelli").length > 1 ||
          (n.toString.splitOn "RegularCut").length > 1 then
        throwError "Rejected dependency: {n}"
      let some ci := env.find? n | throwError "Missing dependency: {n}"
      match ci with
      | .axiomInfo _ =>
        unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
          throwError "Nonstandard dependency: {n}"
      | _ => pure ()
      pending := pending ++ ci.type.getUsedConstants
      if let some v := ci.value? (allowOpaque := true) then
        pending := pending ++ v.getUsedConstants
  Lean.logInfo m!"Round54 aggregate audit PASS: {own} own constants; {seen.size} transitive constants; standard only."
