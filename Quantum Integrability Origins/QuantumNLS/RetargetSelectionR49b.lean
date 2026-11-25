import QuantumNLS.RetargetFinalProofR48b

/-! The witness-retaining form of the rebuilt Q06 selection. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
open Set Filter

namespace QuantumNLS.RetargetSelectionR49b
open PhysicalTensor Occupation FullOccupationAffinity FiniteCellGauge
open RetargetAnglesR48b RetargetStageR48b RetargetCellR48b RetargetTuneR48b
open RetargetAssemblyR48b
variable {L κ : ℝ} [Fact (0 < L)]

/-- The frozen stage argument, retaining one cell width for the entire tail
of sectors and the completed seeds for each of those sectors. -/
private theorem cell_stage_event (hκ : 0 < κ) (j : ℕ) (hj : 0 < j) :
    ∃ ell : ℕ, 2 ≤ ell ∧ ∀ᶠ n in atTop, ell ≤ n+1 ∧
      ∃ c : SelectedSeeds (labels j) (n+1),
        Stage (L := L) hκ j n (q_N (labels j) ell c) := by
  let I := labels j
  let ε := stageBound j
  have hε : 0 < ε := by unfold ε stageBound; positivity
  have hI : 2 ≤ I.card := labels_card j hj
  obtain ⟨ell, δ, hell, hδ, hcut, hbudget⟩ := tune I ε ε hε hε
  refine ⟨ell, hell, ?_⟩
  filter_upwards [eventually_ge_atTop ell, eventual_actions (L := L) hκ j I δ hδ,
    eventual_completed_seeds (L := L) hκ j I (by omega) ell (by omega) δ hδ] with n hN ha hc
  obtain ⟨c, hc⟩ := hc
  have hN' : ell ≤ n+1 := hN.trans (Nat.le_succ _)
  refine ⟨hN', c, ?_⟩
  intro u hu a b
  let w := fun i : ↥I => coordinate hκ u i.1
  let g := coefficients hκ n u
  have h := cell_cartesian I ell hI hell hN' c g w δ δ hδ.le hδ.le
    (coefficients_unit hκ n u hu.2.1) (fun i => coordinate_le_one hκ u hu.2.1 i.1)
    (ha u hu) (hc u hu)
  have hinv : ((n+1 : ℕ) : ℝ)⁻¹ ≤ (ell : ℝ)⁻¹ :=
    inv_anti₀ (by exact_mod_cast (show 0 < ell by omega)) (by exact_mod_cast hN')
  refine ⟨(h.1 a b).trans ?_, fun hab hza hzb => ?_⟩
  · exact (show max δ (Real.sqrt (2*δ + ((n+1 : ℕ) : ℝ)⁻¹) +
        max (FiniteCellFinal.printedBound I ell δ δ) (2 * Real.sqrt (4 / (ell : ℝ)))) ≤
        budget I ell δ from by unfold budget; gcongr).trans hbudget.le
  · exact (h.2 a b hab (hcut.le.trans hza) (hcut.le.trans hzb)).trans
      ((phase_le_budget I ell δ).trans hbudget.le)

/-- Choose the cell width once per stage, before the particle number and
before the profiles. -/
def stageWidth (hκ : 0 < κ) (j : ℕ) : ℕ :=
  if hj : 0 < j then (cell_stage_event (L := L) hκ j hj).choose else 2

/-- A stage gauge retains the complete-array finite-cell construction. -/
def CellStage (hκ : 0 < κ) (j n : ℕ) (q : Arr (n+1) → Phase) : Prop :=
  Stage (L := L) hκ j n q ∧ 2 ≤ stageWidth (L := L) hκ j ∧
    stageWidth (L := L) hκ j ≤ n+1 ∧
    ∃ c : SelectedSeeds (labels j) (n+1), q = q_N (labels j) (stageWidth (L := L) hκ j) c

theorem cell_stage_exists (hκ : 0 < κ) (j : ℕ) (hj : 0 < j) :
    ∀ᶠ n in atTop, ∃ q, CellStage (L := L) hκ j n q := by
  obtain ⟨hWidth, hTail⟩ := (cell_stage_event (L := L) hκ j hj).choose_spec
  filter_upwards [hTail] with n hn
  obtain ⟨hN, c, hc⟩ := hn
  refine ⟨q_N (labels j) (stageWidth (L := L) hκ j) c, ?_⟩
  unfold CellStage stageWidth
  rw [dite_eq_left hj]
  exact ⟨hc, hWidth, hN, c, rfl⟩

private theorem cutoff_exists (hκ : 0 < κ) (j : ℕ) :
    ∃ M : ℕ, 0 < j → ∀ n, M ≤ n → ∃ q, CellStage (L := L) hκ j n q := by
  by_cases hj : 0 < j
  · obtain ⟨M, hM⟩ := eventually_atTop.1 (cell_stage_exists (L := L) hκ j hj)
    exact ⟨M, fun _ => hM⟩
  · exact ⟨0, fun h => False.elim (hj h)⟩

/-- Stage cutoffs are chosen before testing a profile. The index is N−1. -/
def required (hκ : 0 < κ) (j : ℕ) : ℕ := (cutoff_exists (L := L) hκ j).choose

/-- The same largest-stage operator used by the frozen `select_family`. -/
def sectorStage (hκ : 0 < κ) : ℕ → ℕ :=
  RetargetScheduleR48b.stage (required (L := L) hκ)

theorem sector_stage_exists (hκ : 0 < κ) (n : ℕ) (hn : 0 < sectorStage (L := L) hκ n) :
    ∃ q, CellStage (L := L) hκ (sectorStage (L := L) hκ n) n q :=
  (cutoff_exists (L := L) hκ _).choose_spec hn n
    ((RetargetScheduleR48b.thresholds_required _ hn).trans
      (RetargetScheduleR48b.stage_threshold _ n))

/-- At the selected stage, choose one complete-array gauge for the whole sector. -/
def sectorGauge (hκ : 0 < κ) (n : ℕ) : Arr (n+1) → Phase :=
  if hn : 0 < sectorStage (L := L) hκ n then
    (sector_stage_exists (L := L) hκ n hn).choose
  else fun _ => phaseOne

theorem sector_gauge_stage (hκ : 0 < κ) (n : ℕ) (hn : 0 < sectorStage (L := L) hκ n) :
    CellStage (L := L) hκ (sectorStage (L := L) hκ n) n (sectorGauge (L := L) hκ n) := by
  rw [sectorGauge, dite_eq_left hn]
  exact (sector_stage_exists (L := L) hκ n hn).choose_spec

/-- The conclusion of the frozen `select_family`, retaining the selected
functions and the finite-cell provenance of each positive-stage gauge. -/
theorem select_family_explicit (hκ : 0 < κ) :
    Monotone (sectorStage (L := L) hκ) ∧ Tendsto (sectorStage (L := L) hκ) atTop atTop ∧
      ∀ n, 0 < sectorStage (L := L) hκ n →
        CellStage (L := L) hκ (sectorStage (L := L) hκ n) n (sectorGauge (L := L) hκ n) :=
  ⟨RetargetScheduleR48b.stage_mono _, RetargetScheduleR48b.stage_tendsto _, sector_gauge_stage hκ⟩

def particleStage (hκ : 0 < κ) : ℕ → ℕ :=
  RetargetPhysicalR48b.physicalSchedule (sectorStage (L := L) hκ)

def particleGauge (hκ : 0 < κ) : BetheOccupationGauge.Gauge :=
  RetargetPhysicalR48b.gauge (sectorGauge (L := L) hκ)

/-- Translate the positive-sector thresholds to the literal particle number, with
stage zero available from the vacuum onward. -/
def particleThreshold (hκ : 0 < κ) (j : ℕ) : ℕ :=
  if j = 0 then 0 else RetargetScheduleR48b.thresholds (required (L := L) hκ) j + 1

theorem particleThreshold_strict (hκ : 0 < κ) : StrictMono (particleThreshold (L := L) hκ) := by
  intro i j hij
  have hj : j ≠ 0 := by omega
  by_cases hi : i = 0
  · simp [particleThreshold, hi, hj]
  · simpa only [particleThreshold, ite_eq_right hi, ite_eq_right hj, Nat.add_lt_add_iff_right] using
      RetargetScheduleR48b.thresholds_strict (required (L := L) hκ) hij

/-- The printed largest-stage rule with the actual selected thresholds. -/
theorem printed_selection (hκ : 0 < κ) (N : ℕ) :
    IsGreatest {j | particleThreshold (L := L) hκ j ≤ N} (particleStage (L := L) hκ N) := by
  let D := required (L := L) hκ
  let s := RetargetScheduleR48b.stage D (N-1)
  change IsGreatest _ s
  have hstage : RetargetScheduleR48b.thresholds D s ≤ N-1 :=
    RetargetScheduleR48b.stage_threshold D (N-1)
  have hge := RetargetScheduleR48b.thresholds_ge D
  refine ⟨?_, ?_⟩
  · change particleThreshold (L := L) hκ s ≤ N
    by_cases hs : s = 0
    · simp [particleThreshold, hs]
    · rw [particleThreshold, ite_eq_right hs]
      change RetargetScheduleR48b.thresholds D s + 1 ≤ N
      have hs' := hge s
      omega
  · intro j hj
    change particleThreshold (L := L) hκ j ≤ N at hj
    by_cases hzero : j = 0
    · simp [hzero]
    · rw [particleThreshold, ite_eq_right hzero] at hj
      change RetargetScheduleR48b.thresholds D j + 1 ≤ N at hj
      have h : RetargetScheduleR48b.thresholds D j ≤ N-1 := by omega
      exact Nat.le_findGreatest ((hge j).trans h) h

theorem printed_selection_iff (hκ : 0 < κ) (N j : ℕ) :
    j = particleStage (L := L) hκ N ↔
      IsGreatest {k | particleThreshold (L := L) hκ k ≤ N} j := by
  constructor
  · rintro rfl
    exact printed_selection hκ N
  · intro hj
    have hs := printed_selection (L := L) hκ N
    exact le_antisymm (hs.2 hj.1) (hj.2 hs.1)

end QuantumNLS.RetargetSelectionR49b

#print axioms QuantumNLS.RetargetSelectionR49b.printed_selection_iff

#print axioms QuantumNLS.RetargetSelectionR49b.select_family_explicit

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "QuantumNLS.RetargetSelectionR49b." ||
        name.toString.startsWith "_private.QuantumNLS.RetargetSelectionR49b." then
      pending := pending.push name
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    unless seen.contains name do
      seen := seen.insert name
      if (name.toString.splitOn "HeldGP14Tonelli").length > 1 then
        throwError "Rejected dependency: {name}"
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
  Lean.logInfo m!"R49b aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only."
