import QuantumNLS.TerraMultiFinalR94

/-! Physical interfaces of the same named gauge and schedule. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.defProp false
noncomputable section
namespace QuantumNLS.TerraMultiPhysicalR94
variable {L κ : ℝ} [Fact (0 < L)]

def named_cartesian (hκ : 0 < κ) :=
  RetargetPhysicalR48b.physical_cartesian_limit hκ
    (RetargetSelectionR49b.sectorStage (L := L) hκ)
    (RetargetSelectionR49b.sectorGauge (L := L) hκ) (FullWickO5.gauge_conclusion_named hκ)

def named_phase (hκ : 0 < κ) :=
  RetargetPhysicalR48b.physical_phase_limit hκ
    (RetargetSelectionR49b.sectorStage (L := L) hκ)
    (RetargetSelectionR49b.sectorGauge (L := L) hκ) (FullWickO5.gauge_conclusion_named hκ)

def named_schedule_monotone (hκ : 0 < κ) :=
  RetargetPhysicalR48b.physicalSchedule_monotone (FullWickO5.gauge_conclusion_named (L := L) hκ).1

def named_schedule_tendsto (hκ : 0 < κ) :=
  RetargetPhysicalR48b.physicalSchedule_tendsto (FullWickO5.gauge_conclusion_named (L := L) hκ).2.1

def named_phase_ratio (hκ : 0 < κ) (n : ℕ) (a b : ℤ)
    (m : BetheLabels.MArr (n+1)) :=
  RetargetPhysicalR48b.physical_phase_ratio (L := L) hκ n (RetargetSelectionR49b.sectorGauge (L := L) hκ) a b m

def named_cartesian_diagonal (hκ : 0 < κ) (n : ℕ) (a : ℤ) :=
  RetargetPhysicalR48b.cartesian_count (L := L) hκ n (RetargetSelectionR49b.sectorGauge (L := L) hκ n) a

#print axioms named_cartesian
#print axioms named_phase
#print axioms named_schedule_monotone
#print axioms named_schedule_tendsto
#print axioms named_phase_ratio
#print axioms named_cartesian_diagonal
end QuantumNLS.TerraMultiPhysicalR94

set_option maxHeartbeats 20000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.TerraMultiFinalR94." ||
       n.toString.startsWith "QuantumNLS.TerraMultiPhysicalR94." then
      pending := pending.push n
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  let mut axioms : Array Lean.Name := #[]
  let mut flags : Array Lean.Name := #[]
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn "HeldGP14Tonelli").length > 1 ||
          n.components.any (fun c => c.toString == "RegularCut") then
        flags := flags.push n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            axioms := axioms.push n
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"Round 94 audit: {own} roots; {seen.size} transitive constants; nonstandard axioms {axioms}; flagged identifiers {flags}"
  unless axioms.isEmpty do throwError "Nonstandard axioms found"
  unless flags.isEmpty do throwError "Flagged identifiers found"
