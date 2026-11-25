import QuantumNLS.PhysicalContinuousBoundary

/-! Unconditional physical DEF-014: the canonical quantum measure and actual
L2 discriminant furnish every source field. No source facts are supplied. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Set Filter Topology MeasureTheory
namespace QuantumNLS.PhysicalSourceFinal
variable {L κ : ℝ} [Fact (0 < L)]

def sourceFacts (hκ : 0 < κ) (u : PhysicalTensor.L2T L) :
    PhysicalIndexedMasses.SourceFacts L κ u where
  M := PhysicalQuantumMeasure.measure hκ u
  finite := inferInstance
  full_mass := PhysicalQuantumMeasure.full_mass hκ u
  atomless := PhysicalUnconditionalTrace.atomless hκ u
  γ := PhysicalContinuousBoundary.boundary hκ u
  boundary := by
    intro x
    have hz : Tendsto (fun ε : ℝ => (x : ℂ) + (ε : ℂ) * Complex.I)
        (𝓝[>] 0) (𝓝[PhysicalPhaseHolomorphic.upper] (x : ℂ)) := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · have hc : Continuous (fun ε : ℝ => (x : ℂ) + (ε : ℂ) * Complex.I) := by fun_prop
        simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with ε hε
        simpa [PhysicalPhaseHolomorphic.upper] using hε
    exact (PhysicalContinuousBoundary.boundary_limit hκ u x).comp hz
  continuous := PhysicalContinuousBoundary.continuous_boundary hκ u
  monotone := PhysicalContinuousBoundary.monotone_all hκ u
  onto := PhysicalContinuousBoundary.onto_all hκ u
  continuous_discriminant := L2DiscriminantRegularity.continuous_discriminant κ u
  real_discriminant := L2DiscriminantRegularity.discriminant_real κ u
  quantum_identity := fun _ hz => PhysicalUnconditionalTrace.upper_cosine hκ u hz
  positive_band_derivative := PhysicalContinuousBoundary.positive_band_derivative_all hκ u
  gap_constancy := fun _ _ hab hg => PhysicalContinuousBoundary.gap_constancy hκ u hab hg

/-- The previously named analytic existence obligation, now proved. -/
theorem physicalSourceExistence : PhysicalIndexedMasses.PhysicalSourceExistence := by
  intro L _ κ hκ u
  exact ⟨sourceFacts hκ u⟩

/-- The single arbitrary-L2 DEF-014 theorem, without a supplied SourceFacts argument. -/
theorem «DEF-014» (hκ : 0 < κ) (u : PhysicalTensor.L2T L) :
    let D := sourceFacts hκ u
    (∀ n : ℤ, ∃! b : ℝ, (PhysicalContinuousBoundary.boundary hκ u b).re =
      MonotoneIndexedMasses.level n) ∧
    StrictMono D.phase.separator ∧
    (∀ n, D.masses.1 n =
      (PhysicalQuantumMeasure.measure hκ u
        (Ioo (D.phase.separator (n - 1)) (D.phase.separator n))).toReal) ∧
    (∀ n, 0 ≤ D.masses.1 n) ∧ Summable (fun n => D.masses.1 n) ∧
    (∑' n, D.masses.1 n) = ‖u‖ ^ 2 :=
  PhysicalIndexedMasses.«DEF-014» u (sourceFacts hκ u)

end QuantumNLS.PhysicalSourceFinal

#print axioms QuantumNLS.PhysicalSourceFinal.sourceFacts
#print axioms QuantumNLS.PhysicalSourceFinal.physicalSourceExistence
#print axioms QuantumNLS.PhysicalSourceFinal.«DEF-014»

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.PhysicalSourceFinal." then
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
  Lean.logInfo m!"Result aggregate audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
