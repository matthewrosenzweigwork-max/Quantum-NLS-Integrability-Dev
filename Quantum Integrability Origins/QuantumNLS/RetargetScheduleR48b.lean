import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Data.Nat.Find

/-! One schedule for every radius and all the active labels. -/
set_option autoImplicit false
namespace QuantumNLS.RetargetScheduleR48b
open Filter

/-- Stage zero supplies the initial gauge. Stage (j+1) waits for its own
threshold, its own minimum particle number, and the end of stage (j). -/
def thresholds (required : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => max (thresholds required j + 1) (required (j + 1))

theorem thresholds_strict (required : ℕ → ℕ) : StrictMono (thresholds required) := by
  apply strictMono_nat_of_lt_succ
  intro j
  exact (Nat.lt_succ_self _).trans_le (le_max_left _ _)

theorem thresholds_ge (required : ℕ → ℕ) (j : ℕ) : j ≤ thresholds required j :=
  (thresholds_strict required).id_le j

theorem thresholds_required (required : ℕ → ℕ) {j : ℕ} (hj : 0 < j) :
    required j ≤ thresholds required j := by
  cases j with
  | zero => omega
  | succ j => exact le_max_right _ _

/-- The largest stage whose threshold has been reached. -/
def stage (required : ℕ → ℕ) (N : ℕ) : ℕ :=
  Nat.findGreatest (fun j => thresholds required j ≤ N) N

theorem stage_threshold (required : ℕ → ℕ) (N : ℕ) :
    thresholds required (stage required N) ≤ N :=
  Nat.findGreatest_spec (P := fun j => thresholds required j ≤ N)
    (m := 0) (Nat.zero_le N) (Nat.zero_le N)

theorem stage_mono (required : ℕ → ℕ) : Monotone (stage required) := by
  intro N M h
  exact Nat.findGreatest_mono (fun _ hj => hj.trans h) h

theorem stage_tendsto (required : ℕ → ℕ) : Tendsto (stage required) atTop atTop := by
  refine tendsto_atTop.2 fun j => ?_
  filter_upwards [eventually_ge_atTop (thresholds required j)] with N hN
  exact Nat.le_findGreatest (le_trans (thresholds_ge required j) hN) hN

/-- A simultaneous stage event, applied after the largest stage has been chosen. -/
theorem select (P : ℕ → ℕ → Prop)
    (h : ∀ j, 0 < j → ∀ᶠ N in atTop, P j N) :
    ∃ s : ℕ → ℕ, Monotone s ∧ Tendsto s atTop atTop ∧ ∀ N, 0 < s N → P (s N) N := by
  classical
  have bounds : ∀ j : ℕ, ∃ cutoff : ℕ, 0 < j → ∀ N, cutoff ≤ N → P j N := by
    intro j
    by_cases hj : 0 < j
    · obtain ⟨M, hM⟩ := eventually_atTop.1 (h j hj)
      exact ⟨M, fun _ => hM⟩
    · exact ⟨0, fun h => False.elim (hj h)⟩
  choose cutoff hcutoff using bounds
  refine ⟨stage cutoff, stage_mono cutoff, stage_tendsto cutoff, fun N hN => ?_⟩
  exact hcutoff (stage cutoff N) hN N ((thresholds_required cutoff hN).trans (stage_threshold cutoff N))

/-- The stage choice selects one object in each sector independently of all
parameters quantified in the stage predicate. -/
theorem select_family {A : ℕ → Type} (initial : ∀ N, A N)
    (P : ℕ → ∀ N, A N → Prop)
    (h : ∀ j, 0 < j → ∀ᶠ N in atTop, ∃ q, P j N q) :
    ∃ (s : ℕ → ℕ) (q : ∀ N, A N),
      Monotone s ∧ Tendsto s atTop atTop ∧ ∀ N, 0 < s N → P (s N) N (q N) := by
  classical
  obtain ⟨s, hs, hlim, hsP⟩ := select (fun j N => ∃ q, P j N q) h
  let q (N : ℕ) : A N := if hN : 0 < s N then (hsP N hN).choose else initial N
  refine ⟨s, q, hs, hlim, fun N hN => ?_⟩
  simp only [q, dite_eq_left hN]
  exact (hsP N hN).choose_spec

end QuantumNLS.RetargetScheduleR48b

#print axioms QuantumNLS.RetargetScheduleR48b.select
#print axioms QuantumNLS.RetargetScheduleR48b.select_family

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "QuantumNLS.RetargetScheduleR48b." ||
        name.toString.startsWith "_private.QuantumNLS.RetargetScheduleR48b." then
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
  Lean.logInfo m!"R48b aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only."
