import QuantumNLS.RootTraceSymbolUpper
import QuantumNLS.PhysicalPhaseHeightBoundary
import QuantumNLS.PhysicalVacuumSourceFacts

/-! TS1 instantiated on the literal arbitrary-L2 canonical measure.
No boundary real-part or SourceFacts conclusion is an input. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Filter Topology Set MeasureTheory
namespace QuantumNLS.PhysicalUnconditionalTrace
variable {L κ : ℝ} [Fact (0 < L)]

/-- The physical cosine identity, including the vacuum. -/
theorem upper_cosine (hκ : 0 < κ) (u : PhysicalTensor.L2T L)
    {z : ℂ} (hz : 0 < z.im) :
    2 * Complex.cos (SpatialTransfer.boundaryPhase L κ
      (PhysicalQuantumMeasure.measure hκ u) z) = L2SpatialTransfer.discriminant κ u z := by
  by_cases hu : u = 0
  · subst u
    simpa [SpatialTransfer.boundaryPhase, EmpiricalRapidity.cauchyTransform] using
      (PhysicalVacuumSourceFacts.discriminant_zero (L := L) κ z).symm
  · exact RootTraceSymbolUpper.upper_cosine hκ hu hz

/-- Atomlessness of the canonical quantum measure for every L2 input. -/
theorem atomless (hκ : 0 < κ) (u : PhysicalTensor.L2T L) :
    NullSingletonClass (PhysicalQuantumMeasure.measure hκ u) :=
  PhysicalPhaseAtomlessness.canonical_atomless_of_upper_cosine hκ u
    (fun _ hz => upper_cosine hκ u hz)

/-- Actual continuous phase height on the entire closed upper half-plane. -/
theorem height_eq_im (hκ : 0 < κ) (u : PhysicalTensor.L2T L)
    {z : ℂ} (hz : 0 < z.im) :
    PhysicalPhaseHeightBoundary.canonicalHeight κ u z =
      (SpatialTransfer.boundaryPhase L κ (PhysicalQuantumMeasure.measure hκ u) z).im := by
  unfold PhysicalPhaseHeightBoundary.canonicalHeight
  rw [← upper_cosine hκ u hz]
  exact PhysicalPhaseHeightBoundary.height_cos (PhysicalQuantumMeasure.im_phase_pos hκ u hz).le

/-- Unrestricted upper approach to the source imaginary boundary, including edges. -/
theorem boundary_height (hκ : 0 < κ) (u : PhysicalTensor.L2T L) (x : ℝ) :
    Tendsto (fun z : ℂ =>
      (SpatialTransfer.boundaryPhase L κ (PhysicalQuantumMeasure.measure hκ u) z).im)
      (𝓝[PhysicalPhaseHolomorphic.upper] (x : ℂ))
      (𝓝 (RootDensity.hfun |(L2SpatialTransfer.discriminant κ u (x : ℂ)).re|)) := by
  have hr : L2SpatialTransfer.discriminant κ u (x : ℂ) =
      ((L2SpatialTransfer.discriminant κ u (x : ℂ)).re : ℂ) := by
    apply Complex.ext <;> simp [L2DiscriminantRegularity.discriminant_real κ u x]
  have he : PhysicalPhaseHeightBoundary.canonicalHeight κ u (x : ℂ) =
      RootDensity.hfun |(L2SpatialTransfer.discriminant κ u (x : ℂ)).re| := by
    unfold PhysicalPhaseHeightBoundary.canonicalHeight
    exact (congrArg PhysicalPhaseHeightBoundary.height hr).trans
      (PhysicalPhaseHeightBoundary.height_real _)
  rw [← he]
  apply ((PhysicalPhaseHeightBoundary.continuous_canonicalHeight κ u).continuousAt.tendsto.mono_left
    nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact height_eq_im hκ u hz

/-- The cosine has no branch points in the open upper half-plane. -/
theorem discriminant_ne_edge (hκ : 0 < κ) (u : PhysicalTensor.L2T L)
    {z : ℂ} (hz : 0 < z.im) :
    L2SpatialTransfer.discriminant κ u z ≠ 2 ∧
      L2SpatialTransfer.discriminant κ u z ≠ -2 := by
  let w := SpatialTransfer.boundaryPhase L κ (PhysicalQuantumMeasure.measure hκ u) z
  have hp : 0 < w.im := PhysicalQuantumMeasure.im_phase_pos hκ u hz
  have hcos := upper_cosine hκ u hz
  have hf := PhysicalPhaseHeightBoundary.focal_distances w
  have hb : 1 < Real.cosh w.im := Real.one_lt_cosh.mpr hp.ne'
  constructor
  · intro he
    have hw : Complex.cos w = 1 := by dsimp [w]; linear_combination (hcos + he) / 2
    simp only [hw] at hf
    norm_num at hf
    linarith [hf.1, hf.2]
  · intro he
    have hw : Complex.cos w = -1 := by dsimp [w]; linear_combination (hcos + he) / 2
    simp only [hw] at hf
    norm_num at hf
    linarith [hf.1, hf.2]

end QuantumNLS.PhysicalUnconditionalTrace

#print axioms QuantumNLS.PhysicalUnconditionalTrace.upper_cosine

#print axioms QuantumNLS.PhysicalUnconditionalTrace.atomless

#print axioms QuantumNLS.PhysicalUnconditionalTrace.height_eq_im

#print axioms QuantumNLS.PhysicalUnconditionalTrace.boundary_height

#print axioms QuantumNLS.PhysicalUnconditionalTrace.discriminant_ne_edge

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.PhysicalUnconditionalTrace." then
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
