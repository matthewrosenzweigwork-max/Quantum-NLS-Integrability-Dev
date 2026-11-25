import QuantumNLS.UniformStaticR49b
import QuantumNLS.UniformProjR01

/-! Transport the rebuilt Q06 static theorem to the predicate used by the
uniform projective corollary. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open Filter Topology
open scoped ComplexConjugate

namespace QuantumNLS.UniformStaticBridgeR50b

open BetheLabels BetheCoefficientTransform RetargetSelectionR49b
variable {L κ : ℝ} [Fact (0 < L)]

/-- The R31m index `n` denotes the physical particle number `n + 1`. -/
def toSectorSchedule (j : ℕ → ℕ) : ℕ → ℕ := fun n => j (n + 1)

/-- Both static predicates use the phase multiplying the occupation coefficient. -/
abbrev toFullGauge (q : UniformStaticR49b.SectorGauge) : UniformStaticR31m.FullGauge := q

/-- Reindexing the chosen particle schedule recovers the original Q06 stage. -/
theorem selected_schedule (hκ : 0 < κ) :
    toSectorSchedule (particleStage (L := L) hκ) = sectorStage (L := L) hκ := by
  funext n
  change sectorStage (L := L) hκ (n + 1 - 1) = sectorStage (L := L) hκ n
  rw [Nat.add_sub_cancel]

/-- The projective statement writes the same particle number as `1 + n`. -/
theorem projective_schedule (j : ℕ → ℕ) (n : ℕ) :
    toSectorSchedule j n = j (1 + n) := congrArg j (Nat.add_comm n 1)

/-- The gauge on basis vectors used by the projective statement is conjugate
to the Q06 coefficient gauge, on the entire corrected array space. -/
theorem fullToGauge_eq_conj (q : UniformStaticR49b.SectorGauge) (n : ℕ) (m : MArr (n + 1)) :
    (UniformProjR01Bridge.fullToGauge (toFullGauge q) (n + 1) m).val =
      conj ((RetargetPhysicalR48b.gauge q (n + 1) m).val) := rfl

theorem selected_projective_gauge (hκ : 0 < κ) (n : ℕ) (m : MArr (n + 1)) :
    (UniformProjR01Bridge.fullToGauge (toFullGauge (sectorGauge (L := L) hκ)) (n + 1) m).val =
      conj ((particleGauge (L := L) hκ (n + 1) m).val) :=
  fullToGauge_eq_conj _ n m

/-- The finite set of pairs enumerates precisely the two subtype labels used
in the finite-cell estimates. -/
theorem mem_pairs_iff_labels (j : ℕ) (p : ℤ × ℤ) :
    p ∈ UniformStaticR31m.pairs j ↔
      ∃ a b : ↥(RetargetAnglesR48b.labels j), (a.val, b.val) = p := by
  change p ∈ UniformStaticR49b.pairs j ↔ _
  constructor
  · intro hp
    obtain ⟨ha, hb⟩ := UniformStaticR49b.mem_pairs.mp hp
    exact ⟨⟨p.1, ha⟩, ⟨p.2, hb⟩, rfl⟩
  · rintro ⟨a, b, rfl⟩
    exact UniformStaticR49b.mem_pairs.mpr ⟨a.property, b.property⟩

/-- The same Cartesian operator is used in the projective entry bound. Its
basis-vector gauge is converted by `fullToGauge`. -/
theorem cartesian_eq_projective_physical (hκ : 0 < κ) (q : UniformStaticR49b.SectorGauge)
    (n : ℕ) (p : ℤ × ℤ) :
    UniformStaticR49b.E (L := L) hκ q n p =
      CartesianOccupationTransfer.physical (Def044D1SpectralR51a.basis hκ n)
        (UniformProjR01Bridge.fullToGauge (toFullGauge q)) p.1 p.2 := by
  change UniformStaticR31m.E (L := L) hκ (toFullGauge q) n p = _
  exact UniformProjR01Bridge.E_eq_physical hκ (toFullGauge q) n p

/-- The residuals, phase tests and full-array quantities agree in the positive
sectors. Restrict the schedule and exterior property to those sectors. -/
theorem to_uniform_static (hκ : 0 < κ) (j : ℕ → ℕ) (q : UniformStaticR49b.SectorGauge)
    (h : UniformStaticR49b.UniformStatic (L := L) hκ j q) :
    UniformStaticR31m.UniformStatic (L := L) hκ (toSectorSchedule j) (toFullGauge q) := by
  obtain ⟨hj, hlim, hext, hcart, hphase⟩ := h
  exact ⟨fun _ _ hab => hj (Nat.succ_le_succ hab), hlim.comp (tendsto_add_atTop_nat 1),
    fun n => hext (n + 1), hcart, hphase⟩

/-- The largest eligible Q06 stage and the static bounds for its literal gauge. -/
theorem selected_printed_static (hκ : 0 < κ) :
    (∀ N, IsGreatest {k | particleThreshold (L := L) hκ k ≤ N} (particleStage (L := L) hκ N)) ∧
      UniformStaticR49b.UniformStatic (L := L) hκ (particleStage (L := L) hκ)
        (sectorGauge (L := L) hκ) :=
  ⟨printed_selection hκ, UniformStaticR49b.selected_uniform_static hκ⟩

/-- The frozen R31m predicate holds at the selected Q06 witnesses. -/
theorem selected_uniform_static (hκ : 0 < κ) :
    UniformStaticR31m.UniformStatic (L := L) hκ (sectorStage (L := L) hκ)
      (toFullGauge (sectorGauge (L := L) hκ)) := by
  rw [← selected_schedule (L := L) hκ]
  exact to_uniform_static hκ _ _ (UniformStaticR49b.selected_uniform_static hκ)

/-- The exact input type of `UniformProjR01.uniform_projective_intermediate`. -/
theorem selected_projective_input (hκ : 0 < κ) :
    UniformProjR01.UniformStaticD2F4CE8FInput (L := L) hκ (sectorStage (L := L) hκ)
      (toFullGauge (sectorGauge (L := L) hκ)) :=
  selected_uniform_static hκ

end QuantumNLS.UniformStaticBridgeR50b

#print axioms QuantumNLS.UniformStaticBridgeR50b.to_uniform_static
#print axioms QuantumNLS.UniformStaticBridgeR50b.selected_printed_static
#print axioms QuantumNLS.UniformStaticBridgeR50b.selected_uniform_static
#print axioms QuantumNLS.UniformStaticBridgeR50b.selected_projective_input

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "QuantumNLS.UniformStaticBridgeR50b." ||
        name.toString.startsWith "_private.QuantumNLS.UniformStaticBridgeR50b." then
      pending := pending.push name
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    unless seen.contains name do
      seen := seen.insert name
      if (name.toString.splitOn "HeldGP14Tonelli").length > 1 ||
          name.components.any (fun c => c.toString == "RegularCut") ||
          name == ``QuantumNLS.UniformStaticR31m.GaugeRetargetingRD51987CAInput ||
          name == ``QuantumNLS.UniformStaticR31m.uniform_static_intermediate ||
          name == ``QuantumNLS.UniformStaticR49b.retarget_and_uniform_static_intermediate ||
          name == ``QuantumNLS.UniformStaticR49b.uniform_static_intermediate then
        throwError "Excluded dependency: {name}"
      if let some info := env.find? name then
        match info with
        | .axiomInfo _ =>
          unless name == ``propext || name == ``Classical.choice || name == ``Quot.sound do
            throwError "Nonstandard dependency: {name}"
        | _ => pure ()
        pending := pending ++ info.type.getUsedConstants
        if let some value := info.value? (allowOpaque := true) then
          pending := pending ++ value.getUsedConstants
      else
        throwError "Missing dependency: {name}"
  Lean.logInfo m!"R50b aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only."
