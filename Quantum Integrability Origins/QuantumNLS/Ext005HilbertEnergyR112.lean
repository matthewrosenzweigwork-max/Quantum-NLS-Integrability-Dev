import QuantumNLS.Ext005GramConvergenceR112

/-! Native D3 energy bounds on an arbitrary Hilbert form-domain embedding.
Measurability of the form lift is derived from norm measurability and the
constructed Gram regularizers; it is not an extra competitor hypothesis. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open scoped InnerProductSpace Topology
open ContinuousLinearMap InnerProductSpace Set Filter MeasureTheory
namespace QuantumNLS.Ext005HilbertEnergyR112
open Ext005GramResolventR112 Ext005GramConvergenceR112
variable {Q H : Type*}
variable [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Native essential form bound, before any coordinate measurability has been proved. -/
def EnergyBounded (i : Q →L[ℝ] H) (U : Set ℝ) (x : ℝ → H) : Prop :=
  ∃ E : ℝ, 0 ≤ E ∧ ∀ᵐ t ∂volume.restrict U, ∃ u : Q, i u = x t ∧ ‖u‖ ≤ E

/-- Zero off the form domain. Only a.e. form-domain values enter D3. -/
def lift (i : Q →L[ℝ] H) (x : H) : Q := by
  classical
  exact if h : ∃ u : Q, i u = x then h.choose else 0

omit [CompleteSpace Q] [CompleteSpace H] in
lemma lift_eq (i : Q →L[ℝ] H) (hinj : Function.Injective i) (u : Q) :
    lift i (i u) = u := by
  classical
  have h : ∃ v : Q, i v = i u := ⟨u, rfl⟩
  simp only [lift, dite_eq_left h]
  exact hinj h.choose_spec

lemma lift_measurable (i : Q →L[ℝ] H) (hinj : Function.Injective i)
    (μ : Measure ℝ) (x : ℝ → H) (hx : AEStronglyMeasurable x μ)
    (hd : ∀ᵐ t ∂μ, ∃ u : Q, i u = x t) :
    AEStronglyMeasurable (fun t => lift i (x t)) μ := by
  apply aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun n t => inverse i (epsilon n) (epsilon_pos n) (i.adjoint (x t)))
  · intro n
    exact (inverse i _ _).continuous.comp_aestronglyMeasurable
      (i.adjoint.continuous.comp_aestronglyMeasurable hx)
  · filter_upwards [hd] with t ht
    obtain ⟨u, hu⟩ := ht
    rw [← hu, lift_eq i hinj u]
    exact C_tendsto i hinj u

/-- Native D3 hypotheses imply the measurable bounded form coordinates used
in the norm chain rule, on any measurable time interval. -/
theorem energy_coordinates (i : Q →L[ℝ] H) (hinj : Function.Injective i)
    (U : Set ℝ) (hU : MeasurableSet U) (x : ℝ → H)
    (hx : AEStronglyMeasurable x (volume.restrict U)) (hb : EnergyBounded i U x) :
    AEStronglyMeasurable (U.indicator (fun t => lift i (x t))) volume ∧
    ∃ E : ℝ, 0 ≤ E ∧ ∀ᵐ t, t ∈ U →
      i (U.indicator (fun t => lift i (x t)) t) = x t ∧
      ‖U.indicator (fun t => lift i (x t)) t‖ ≤ E := by
  obtain ⟨E, hE, hb⟩ := hb
  have hm := lift_measurable i hinj (volume.restrict U) x hx
    (hb.mono fun _ ht => ⟨_, ht.choose_spec.1⟩)
  refine ⟨(aestronglyMeasurable_indicator_iff hU).mpr hm, E, hE, ?_⟩
  have hg := (ae_restrict_iff' hU).mp hb
  filter_upwards [hg] with t ht htU
  obtain ⟨u, hu, hbu⟩ := ht htU
  rw [indicator_of_mem htU, ← hu, lift_eq i hinj u]
  exact ⟨rfl, hbu⟩

end QuantumNLS.Ext005HilbertEnergyR112
#print axioms QuantumNLS.Ext005HilbertEnergyR112.lift_measurable
#print axioms QuantumNLS.Ext005HilbertEnergyR112.energy_coordinates

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005HilbertEnergyR112." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005HilbertEnergyR112." then
      pending := pending.push n
  let roots := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
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
  Lean.logInfo m!"R112 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
