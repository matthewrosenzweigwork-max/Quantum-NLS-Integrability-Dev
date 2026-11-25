import QuantumNLS.FullWickO3

/-! FullWickO5 (opus_tensor): explicit-witness version of the R93 / R48b R-D51987CA gauge conclusion.

`TerraMultiRound93Chain.chain_intermediate` (terra_multi R93, frozen `c403dcd2…`) and the R48b intermediate
`RetargetPhysicalR48b.retarget_with_seed_intermediate` conclude the R-D51987CA gauge statement existentially:
`∃ s q, RetargetFinalProofR48b.GaugeConclusion hκ s q`. This module proves that the witnesses can be taken to be
the NAMED R49b pair, with the conclusion at that pair stated explicitly:
* `gauge_conclusion_named`: `GaugeConclusion hκ (sectorStage hκ) (sectorGauge hκ)` (sector-indexed schedule);
* `named_schedule_eq`: `sectorStage hκ = toSectorSchedule (particleStage hκ)`, i.e. the schedule of the pair
  `(sectorGauge hκ, particleStage hκ)` used by R49b/`UniformStatic`, re-indexed from particle number `n+1` to
  sector `n` (the R48b `GaugeConclusion` and R31m statements are sector-indexed);
* `gauge_conclusion_named_particle`: the same with the schedule written as `toSectorSchedule (particleStage hκ)`;
* `gauge_existential_witnessed`: the R93/R48b existential with the witnesses pinned
  (`∃ s q, s = sectorStage hκ ∧ q = sectorGauge hκ ∧ GaugeConclusion hκ s q`);
* `retarget_with_seed_named`: the R48b intermediate (the source of R93's gauge conjunct) with the existential
  replaced by the named conjunct, same hypotheses; `pin_gauge_conjunct`: any `P ∧ ∃ s q, GaugeConclusion hκ s q`
  (the shape of R93 `chain_intermediate` / `chain_r58_intermediate`) yields `P ∧ GaugeConclusion` at the named
  pair. The R93 modules themselves are NOT imported: their closure contains the held identifier
  `RB7BindFinal.hierarchyInputR25m_unconditional` (via `Bind7BR300B8640A01.hierFlow`,
  `TerraMultiRound93Compose.selected`); the one-line binding `pin_gauge_conjunct hκ (chain_intermediate …)` is
  for the final module once that hold is lifted;
* `named_pair_all_interfaces`: at the same named pair, simultaneously: R48b `GaugeConclusion`, R49b
  `UniformStatic` (particle schedule), R31m `UniformStatic` (sector schedule), the written-out R31m body of
  R-D51987CA (`FullWickO3.rd51987ca_body_at_Q06`), and the identity of the R-8362E5EB gauge conversion with the
  static Wick gauge (`FullWickO3.physicalGauge_Q06`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

open Filter Topology
open QuantumNLS.PhysicalTensor QuantumNLS.Def033HierarchyR24m QuantumNLS.ActualModelTargetR53a
open QuantumNLS.RetargetFinalProofR48b

namespace QuantumNLS.FullWickO5

variable {L κ : ℝ} [Fact (0 < L)]

/-- R48b `GaugeConclusion` at the named R49b pair. -/
theorem gauge_conclusion_named (hκ : 0 < κ) :
    GaugeConclusion (L := L) hκ (RetargetSelectionR49b.sectorStage (L := L) hκ)
      (RetargetSelectionR49b.sectorGauge (L := L) hκ) :=
  RetargetBallR49b.selected_gauge_conclusion hκ

/-- The sector schedule is the particle schedule `particleStage` re-indexed by `n ↦ n+1`. -/
theorem named_schedule_eq (hκ : 0 < κ) :
    RetargetSelectionR49b.sectorStage (L := L) hκ =
      UniformStaticBridgeR50b.toSectorSchedule (RetargetSelectionR49b.particleStage (L := L) hκ) :=
  (UniformStaticBridgeR50b.selected_schedule hκ).symm

theorem gauge_conclusion_named_particle (hκ : 0 < κ) :
    GaugeConclusion (L := L) hκ
      (UniformStaticBridgeR50b.toSectorSchedule (RetargetSelectionR49b.particleStage (L := L) hκ))
      (RetargetSelectionR49b.sectorGauge (L := L) hκ) := by
  rw [← named_schedule_eq]
  exact gauge_conclusion_named hκ

/-- The R93/R48b existential gauge conclusion, with its witnesses pinned to the named pair. -/
theorem gauge_existential_witnessed (hκ : 0 < κ) :
    ∃ (s : ℕ → ℕ) (q : ∀ n, QuantumNLS.Occupation.Arr (n+1) → QuantumNLS.FullOccupationAffinity.Phase),
      s = RetargetSelectionR49b.sectorStage (L := L) hκ ∧ q = RetargetSelectionR49b.sectorGauge (L := L) hκ ∧
      GaugeConclusion (L := L) hκ s q :=
  ⟨_, _, rfl, rfl, gauge_conclusion_named hκ⟩

section Predecessor

open DynSeedInputR47b DynSeedClassicalR47b

/-- **R48b `retarget_with_seed_intermediate` with the named gauge witnesses** (same hypotheses as the frozen
theorem). This is the source of the existential gauge conjunct of R93 `chain_intermediate` /
`chain_r58_intermediate` (their gauge conjunct is `(retarget_with_seed_intermediate …).2`). -/
theorem retarget_with_seed_named (hκ : 0 < κ) (F : HigherFlows L κ)
    (u : Smooth L) (hu : ‖Def033HierarchyR24m.physical u‖ = 1)
    (R : Finset ℕ) (lo hi : ℕ → ℝ) (a b : ℤ) (hab : a ≠ b)
    (flow_actions : ∀ t : TimeBox R lo hi,
      classicalOrbit hκ F u R t.val ∈ torus hκ (Def033HierarchyR24m.physical u))
    (mixed : MixedFinite hκ F u R)
    (PredecessorInput : DynftFullTorusInput hκ F u R) :
    DynSeedR47b.SeedStatement hκ F u R lo hi a b ∧
      GaugeConclusion (L := L) hκ (RetargetSelectionR49b.sectorStage (L := L) hκ)
        (RetargetSelectionR49b.sectorGauge (L := L) hκ) :=
  ⟨(RetargetPhysicalR48b.retarget_with_seed_intermediate hκ F u hu R lo hi a b hab flow_actions mixed
      PredecessorInput).1, gauge_conclusion_named hκ⟩

end Predecessor

/-- Pinning rule for any conclusion of the R93/R48b shape `P ∧ ∃ s q, GaugeConclusion hκ s q`: the existential
conjunct may always be replaced by the named-pair conjunct. -/
theorem pin_gauge_conjunct (hκ : 0 < κ) {P : Prop}
    (h : P ∧ ∃ (s : ℕ → ℕ) (q : ∀ n, QuantumNLS.Occupation.Arr (n+1) → QuantumNLS.FullOccupationAffinity.Phase),
      GaugeConclusion (L := L) hκ s q) :
    P ∧ GaugeConclusion (L := L) hκ (RetargetSelectionR49b.sectorStage (L := L) hκ)
      (RetargetSelectionR49b.sectorGauge (L := L) hκ) :=
  ⟨h.1, gauge_conclusion_named hκ⟩

/-- **One named pair across the interfaces.** -/
theorem named_pair_all_interfaces (hκ : 0 < κ) :
    GaugeConclusion (L := L) hκ (RetargetSelectionR49b.sectorStage (L := L) hκ)
        (RetargetSelectionR49b.sectorGauge (L := L) hκ) ∧
    UniformStaticR49b.UniformStatic (L := L) hκ (RetargetSelectionR49b.particleStage (L := L) hκ)
        (RetargetSelectionR49b.sectorGauge (L := L) hκ) ∧
    UniformStaticR31m.UniformStatic (L := L) hκ (RetargetSelectionR49b.sectorStage (L := L) hκ)
        (UniformStaticBridgeR50b.toFullGauge (RetargetSelectionR49b.sectorGauge (L := L) hκ)) ∧
    RetargetSelectionR49b.sectorStage (L := L) hκ =
        UniformStaticBridgeR50b.toSectorSchedule (RetargetSelectionR49b.particleStage (L := L) hκ) ∧
    DynamicGaugePhysicalR34m.physicalGauge
        (UniformStaticBridgeR50b.toFullGauge (RetargetSelectionR49b.sectorGauge (L := L) hκ)) =
      FullWickO1.staticGauge (RetargetSelectionR49b.sectorGauge (L := L) hκ) :=
  ⟨gauge_conclusion_named hκ, UniformStaticR49b.selected_uniform_static hκ,
    UniformStaticBridgeR50b.selected_uniform_static hκ, named_schedule_eq hκ,
    FullWickO3.physicalGauge_Q06 hκ⟩

end QuantumNLS.FullWickO5

#print axioms QuantumNLS.FullWickO5.gauge_conclusion_named
#print axioms QuantumNLS.FullWickO5.named_schedule_eq
#print axioms QuantumNLS.FullWickO5.gauge_conclusion_named_particle
#print axioms QuantumNLS.FullWickO5.gauge_existential_witnessed
#print axioms QuantumNLS.FullWickO5.retarget_with_seed_named
#print axioms QuantumNLS.FullWickO5.pin_gauge_conjunct
#print axioms QuantumNLS.FullWickO5.named_pair_all_interfaces
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "QuantumNLS.FullWickO5." ||
        name.toString.startsWith "_private.QuantumNLS.FullWickO5." then
      pending := pending.push name
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    unless seen.contains name do
      seen := seen.insert name
      if (name.toString.splitOn "HeldGP14Tonelli").length > 1 ||
          (name.toString.splitOn "RB7BindFinal").length > 1 ||
          (name.toString.splitOn "DEF033_package").length > 1 ||
          name.components.any (fun c => c.toString == "RegularCut") ||
          name == ``QuantumNLS.UniformStaticR31m.GaugeRetargetingRD51987CAInput ||
          name == ``QuantumNLS.UniformStaticR31m.uniform_static_intermediate ||
          name == ``QuantumNLS.UniformStaticR49b.retarget_and_uniform_static_intermediate ||
          name == ``QuantumNLS.UniformStaticR49b.uniform_static_intermediate ||
          name == ``QuantumNLS.DynamicGaugeR34m.dynamic_gauge_ofInput ||
          name == ``QuantumNLS.DynamicGaugeR34m.dynamic_gauge_successor_ofInput then
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
  Lean.logInfo m!"FullWickO5 aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only; no held identifiers."
