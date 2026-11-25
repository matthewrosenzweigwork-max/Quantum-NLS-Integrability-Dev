import QuantumNLS.HierarchyInputR25m
import QuantumNLS.Def033SobolevR25m
import QuantumNLS.Reg015HFinal

/-! Exact printed R-7B122087 input, shared with sol_multi's now-frozen R25m
interface (4371326e). The incomplete R24m ambient-conclusion candidate is
not substituted for it. REG-015 is accepted and imported directly. This
INTERMEDIATE theorem has the missing predecessor as an explicit Lean
hypothesis. It proves no hierarchy theorem without that hypothesis. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.WindowHierarchyInputR45b
variable {L κ : ℝ} [Fact (0 < L)]

theorem hierarchy_intermediate (hκ : 0 < κ)
    (w : QuantumNLS.PhysicalTensor.L2T L → QuantumNLS.REF88Chart.K)
    (hw : QuantumNLS.REF88PrintedChart.PrintedChart hκ w)
    (HierarchyInput : QuantumNLS.HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ) :
    QuantumNLS.HierarchyInputR25m.HierarchyConclusion (κ := κ) w
      (fun u n => (QuantumNLS.RootIndexedMasses.masses hκ u).1 n) :=
  HierarchyInput w hw (QuantumNLS.Def033SobolevR25m.sobolev_homeomorphisms hκ w hw)
    (QuantumNLS.HierarchyInputR25m.scalar_uniqueness hκ)
    (QuantumNLS.HierarchyInputR25m.scalar_moments hκ)

end QuantumNLS.WindowHierarchyInputR45b
#print QuantumNLS.HierarchyInputR25m.HierarchyR7B122087Input
#print QuantumNLS.WindowHierarchyInputR45b.hierarchy_intermediate
#print axioms QuantumNLS.WindowHierarchyInputR45b.hierarchy_intermediate

-- Recursive type/value audit of every own declaration, including generated declarations.
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.WindowHierarchyInputR45b." ||
        n.toString.startsWith "_private.QuantumNLS.WindowHierarchyInputR45b." then
      pending := pending.push n
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn "HeldGP14Tonelli").length > 1 then
        throwError "Rejected dependency: {n}"
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
  Lean.logInfo m!"R45b aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only."
