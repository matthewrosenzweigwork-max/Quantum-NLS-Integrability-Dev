import QuantumNLS.Ext025GP04ContractR30m
import QuantumNLS.Ext025GP04ApplicationsR30m

/-! Author-side transitive declaration audit for the package and application lemmas. -/
set_option maxHeartbeats 14000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    let label := n.toString
    if label.startsWith "QuantumNLS.Ext025GP04" || label.startsWith "_private.QuantumNLS.Ext025GP04" ||
        label.startsWith "QuantumNLS.Local014ActualUseR29m." ||
        label.startsWith "QuantumNLS.Local014KernelFieldR29m." then
      pending := pending.push n
  let roots := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      let parts := n.toString.splitOn "."
      if parts.contains "HeldGP14Tonelli" || parts.contains "RegularCut" then
        throwError "Held dependency: {n}"
      let some ci := env.find? n | throwError "Missing dependency: {n}"
      if let .axiomInfo _ := ci then
        unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
          throwError "Nonstandard axiom: {n}"
      pending := pending ++ ci.type.getUsedConstants
      if let some body := ci.value? (allowOpaque := true) then
        pending := pending ++ body.getUsedConstants
  Lean.logInfo m!"GP-04 author audit passed: {roots} roots, {seen.size} transitive constants, standard axioms only."
