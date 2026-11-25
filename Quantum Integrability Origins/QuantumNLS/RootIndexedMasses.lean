import QuantumNLS.RootIndexedPhase
import QuantumNLS.TranslationInvariance

/-! R-950BFB30, ROOT_indexed_masses.tex:96: proved clauses at the printed
positive coupling and arbitrary physical L2 input. This module does not
claim the free-coupling, plane-wave, or Galilean clauses. See round6 gaps. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Set Filter Topology
namespace QuantumNLS.RootIndexedMasses
open PhysicalTensor (L2T)
variable {L κ : ℝ} [Fact (0 < L)]
abbrev masses (hκ : 0 < κ) (u : L2T L) := (PhysicalSourceFinal.sourceFacts hκ u).masses

/-- Equality of quantum measures fixes the selected physical boundary phase. -/
theorem boundary_eq_of_measure_eq {u v : L2T L} (hκ : 0 < κ)
    (he : PhysicalQuantumMeasure.measure hκ u = PhysicalQuantumMeasure.measure hκ v) :
    PhysicalContinuousBoundary.boundary hκ u = PhysicalContinuousBoundary.boundary hκ v := by
  funext x
  have : NeBot (𝓝[PhysicalPhaseHolomorphic.upper] (x : ℂ)) := ComplexCosineBoundary.upper_neBot x
  have ht := PhysicalContinuousBoundary.boundary_limit hκ u x
  rw [he] at ht
  exact tendsto_nhds_unique ht (PhysicalContinuousBoundary.boundary_limit hκ v x)

theorem separator_eq_of_measure_eq {u v : L2T L} (hκ : 0 < κ)
    (he : PhysicalQuantumMeasure.measure hκ u = PhysicalQuantumMeasure.measure hκ v) (n : ℤ) :
    RootIndexedPhase.separator hκ u n = RootIndexedPhase.separator hκ v n := by
  apply (PhysicalSourceFinal.sourceFacts hκ v).phase.separator_unique
  change (PhysicalContinuousBoundary.boundary hκ v _).re = _
  rw [← boundary_eq_of_measure_eq hκ he]
  exact (PhysicalSourceFinal.sourceFacts hκ u).phase.separator_spec n

theorem masses_eq_of_measure_eq {u v : L2T L} (hκ : 0 < κ)
    (he : PhysicalQuantumMeasure.measure hκ u = PhysicalQuantumMeasure.measure hκ v) :
    masses hκ u = masses hκ v := by
  apply Subtype.ext
  apply Subtype.ext
  funext n
  change (PhysicalQuantumMeasure.measure hκ u
      (Ioo (RootIndexedPhase.separator hκ u (n-1)) (RootIndexedPhase.separator hκ u n))).toReal =
    (PhysicalQuantumMeasure.measure hκ v
      (Ioo (RootIndexedPhase.separator hκ v (n-1)) (RootIndexedPhase.separator hκ v n))).toReal
  rw [he, separator_eq_of_measure_eq hκ he (n-1), separator_eq_of_measure_eq hκ he n]

/-- Every mass is invariant under common phase, on the actual L2 carrier. -/
theorem masses_phase (hκ : 0 < κ) (u : L2T L) {c : ℂ} (hc : ‖c‖ = 1) :
    masses hκ (c • u) = masses hκ u := by
  apply masses_eq_of_measure_eq hκ
  rw [PhysicalL2Normalization.measure_eq_Mmeas, PhysicalL2Normalization.measure_eq_Mmeas]
  exact FullMass.Mmeas_phase hκ u hc

/-- Every mass is invariant under the literal torus translation. -/
theorem masses_translation (hκ : 0 < κ) (u : L2T L) (a : ℝ) :
    masses hκ (BornTranslation.trans a u) = masses hκ u := by
  apply masses_eq_of_measure_eq hκ
  rw [PhysicalL2Normalization.measure_eq_Mmeas, PhysicalL2Normalization.measure_eq_Mmeas]
  exact TranslationInvariance.Mmeas_translate κ u a

/-- The nonnegative ell1, full normalization, joint continuity, collapsed
interval, common-phase and translation clauses of the printed theorem.
The remaining three printed clauses are explicitly not claimed here. -/
theorem root_indexed_masses_proved_clauses (hκ : 0 < κ) (u : L2T L) :
    (∀ n : ℤ, (masses hκ u).1 n =
      (PhysicalQuantumMeasure.measure hκ u (Ioo
        (RootIndexedPhase.separator hκ u (n-1)) (RootIndexedPhase.separator hκ u n))).toReal) ∧
    (∀ n : ℤ, 0 ≤ (masses hκ u).1 n) ∧
    Summable (fun n => (masses hκ u).1 n) ∧
    (∑' n, (masses hκ u).1 n) = ‖u‖^2 ∧
    Continuous (fun p : DEF014Phase.Param L => masses p.1.2 p.2) ∧
    (∀ n : ℤ, PhysicalQuantumMeasure.measure hκ u (Ioo
      (RootIndexedPhase.separator hκ u (n-1)) (RootIndexedPhase.separator hκ u n)) = 0 →
      (masses hκ u).1 n = 0) ∧
    (∀ c : ℂ, ‖c‖ = 1 → masses hκ (c • u) = masses hκ u) ∧
    (∀ a : ℝ, masses hκ (BornTranslation.trans a u) = masses hκ u) := by
  obtain ⟨_, _, hi, hn, hs, ht⟩ := PhysicalSourceFinal.«DEF-014» hκ u
  exact ⟨hi, hn, hs, ht, DEF014Continuity.continuous_masses,
    (fun n hz => by rw [hi n, hz]; rfl),
    (fun _ hc => masses_phase hκ u hc), masses_translation hκ u⟩
end QuantumNLS.RootIndexedMasses
#print axioms QuantumNLS.RootIndexedMasses.root_indexed_masses_proved_clauses

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.RootIndexedMasses." ||
        n.toString.startsWith "_private.QuantumNLS.RootIndexedMasses." then
      pending := pending.push n
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
  Lean.logInfo m!"RootIndexedMasses audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
