import QuantumNLS.BandPhaseBridge
import QuantumNLS.L2SpatialTransfer
import QuantumNLS.MonotoneMassConsumers

/-!
DEF-014 on the actual L2 carrier and L2ST1 discriminant, conditional on the
explicit source phase facts below. No SourceFacts instance is constructed
here. In particular, the theorem named DEF-014 is conditional and is not an
unqualified physical realization. Its remaining construction obligation is
Nonempty (SourceFacts L κ u) for every positive L, κ and every L2 input.
The source arguments in BandPhaseBridge derive uniqueness; SourceFacts has
no separator, unique-level, interval-mass or global StrictMono field.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal
namespace QuantumNLS.PhysicalIndexedMasses
open QuantumNLS.MonotoneIndexedMasses
variable (L κ : ℝ) [Fact (0 < L)]

/-- Prior source facts for the actual L2 transfer. These remain explicit inputs.
The measure is not identified with the quantum limit by these fields alone. -/
structure SourceFacts (u : QuantumNLS.PhysicalTensor.L2T L) where
  M : Measure ℝ
  finite : IsFiniteMeasure M
  full_mass : (M univ).toReal = ‖u‖ ^ 2
  atomless : NullSingletonClass M
  γ : ℝ → ℂ
  boundary : ∀ x : ℝ, Tendsto (fun ε : ℝ =>
    QuantumNLS.SpatialTransfer.boundaryPhase L κ M ((x : ℂ) + (ε : ℂ) * Complex.I))
      (𝓝[>] 0) (𝓝 (γ x))
  continuous : Continuous γ
  monotone : Monotone fun x => (γ x).re
  onto : Function.Surjective fun x => (γ x).re
  continuous_discriminant : Continuous (QuantumNLS.L2SpatialTransfer.discriminant κ u)
  real_discriminant : ∀ x : ℝ,
    (QuantumNLS.L2SpatialTransfer.discriminant κ u (x : ℂ)).im = 0
  quantum_identity : ∀ z : ℂ, 0 < z.im →
    2 * Complex.cos (QuantumNLS.SpatialTransfer.boundaryPhase L κ M z) =
      QuantumNLS.L2SpatialTransfer.discriminant κ u z
  positive_band_derivative : ∀ x : ℝ,
    |(QuantumNLS.L2SpatialTransfer.discriminant κ u (x : ℂ)).re| < 2 →
      0 < deriv (fun y => (γ y).re) x
  gap_constancy : ∀ a b : ℝ, a < b →
    (∀ x ∈ Ioo a b, 2 < |(QuantumNLS.L2SpatialTransfer.discriminant κ u (x : ℂ)).re|) →
      ∃ k : ℤ, ∀ x ∈ Ioo a b, (γ x).re = (k : ℝ) * Real.pi

variable {L κ}
namespace SourceFacts
variable {u : QuantumNLS.PhysicalTensor.L2T L} (D : SourceFacts L κ u)

/-- Transfer the upper-half-plane identity to the actual boundary, using limits. -/
theorem boundary_cosine (x : ℝ) :
    2 * Complex.cos (D.γ x) = QuantumNLS.L2SpatialTransfer.discriminant κ u (x : ℂ) := by
  have hc : Tendsto (fun ε : ℝ => 2 * Complex.cos
      (QuantumNLS.SpatialTransfer.boundaryPhase L κ D.M
        ((x : ℂ) + (ε : ℂ) * Complex.I))) (𝓝[>] 0) (𝓝 (2 * Complex.cos (D.γ x))) :=
    tendsto_const_nhds.mul (Complex.continuous_cos.continuousAt.tendsto.comp (D.boundary x))
  have hz : Tendsto (fun ε : ℝ => (x : ℂ) + (ε : ℂ) * Complex.I)
      (𝓝[>] 0) (𝓝 (x : ℂ)) := by
    have h : Continuous (fun ε : ℝ => (x : ℂ) + (ε : ℂ) * Complex.I) := by fun_prop
    simpa using (h.tendsto (0 : ℝ)).mono_left
      (show (𝓝[>] (0 : ℝ)) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hd := D.continuous_discriminant.continuousAt.tendsto.comp hz
  apply tendsto_nhds_unique hc
  apply hd.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  apply (D.quantum_identity _ ?_).symm
  simpa using hε

/-- This instance uses the actual L2ST1 trace, not the frozen continuous-profile trace. -/
def phase : BoundaryPhase :=
  QuantumNLS.BandPhaseBridge.phase D.γ
    (fun x => (QuantumNLS.L2SpatialTransfer.discriminant κ u (x : ℂ)).re)
    D.monotone (Complex.continuous_re.comp D.continuous) D.onto
    (Complex.continuous_re.comp (D.continuous_discriminant.comp Complex.continuous_ofReal))
    (fun x => congrArg Complex.re (D.boundary_cosine x)) D.positive_band_derivative

/-- Separators lie in the open bands of the actual physical discriminant. -/
theorem separator_zero (n : ℤ) :
    (QuantumNLS.L2SpatialTransfer.discriminant κ u (D.phase.separator n : ℂ)).re = 0 :=
  QuantumNLS.BandPhaseBridge.half_level_zero
    (fun x => congrArg Complex.re (D.boundary_cosine x)) (D.phase.separator_spec n)

theorem separator_complex_zero (n : ℤ) :
    QuantumNLS.L2SpatialTransfer.discriminant κ u (D.phase.separator n : ℂ) = 0 := by
  apply Complex.ext
  · simpa using D.separator_zero n
  · simpa using D.real_discriminant (D.phase.separator n)

theorem separator_in_band (n : ℤ) :
    |(QuantumNLS.L2SpatialTransfer.discriminant κ u (D.phase.separator n : ℂ)).re| < 2 := by
  rw [D.separator_zero]; norm_num

/-- The faithful phase has exactly the real boundary value of DEF-013. -/
theorem phase_isBoundaryRealPart :
    QuantumNLS.IndexedMasses.IsBoundaryRealPart L κ D.M D.phase.φ := by
  intro x
  exact Complex.continuous_re.continuousAt.tendsto.comp (D.boundary x)

/-- The selected-phase consumer also uses the new faithful interface. -/
def selectedPhase : QuantumNLS.MonotoneMassConsumers.SelectedPhase L κ D.M :=
  { D.phase with boundary := D.phase_isBoundaryRealPart }

/-- Real nonnegative ell1 indexed masses on the physical L2 carrier. -/
def masses : QuantumNLS.ActionTorus.PosL1 := by
  letI := D.finite
  exact D.phase.massVector D.M

/-- The full-mass identity needs no mass at the countable separator set. -/
theorem sum_masses : ∑' n, D.phase.indexedMassReal D.M n = ‖u‖ ^ 2 := by
  have := D.finite
  have := D.atomless
  rw [D.phase.tsum_indexedMassReal_eq D.M ((Set.countable_range _).measure_zero D.M),
    D.full_mass]

/-- The source's flat gaps are admissible and exclude a frozen StrictMono instance. -/
theorem not_strictMono_on_nonempty_gap {a b : ℝ} (hab : a < b)
    (hg : ∀ x ∈ Ioo a b,
      2 < |(QuantumNLS.L2SpatialTransfer.discriminant κ u (x : ℂ)).re|) :
    ¬StrictMono D.phase.φ := by
  obtain ⟨k, hk⟩ := D.gap_constancy a b hab hg
  exact QuantumNLS.BandPhaseBridge.not_strictMono_of_gap hab hk

end SourceFacts

/-- DEF-014 for arbitrary L2 input, conditional on the listed source facts.
Existence of SourceFacts for the physical quantum measure is still OPEN. -/
theorem «DEF-014» (u : QuantumNLS.PhysicalTensor.L2T L) (D : SourceFacts L κ u) :
    (∀ n : ℤ, ∃! b : ℝ, (D.γ b).re = level n) ∧
    StrictMono D.phase.separator ∧
    (∀ n, (D.masses).1 n =
      (D.M (Ioo (D.phase.separator (n - 1)) (D.phase.separator n))).toReal) ∧
    (∀ n, 0 ≤ (D.masses).1 n) ∧
    Summable (fun n => (D.masses).1 n) ∧
    (∑' n, (D.masses).1 n) = ‖u‖ ^ 2 := by
  have := D.finite
  refine ⟨D.phase.exists_unique_separator, D.phase.separator_strictMono,
    fun _ => rfl, fun n => (D.masses).2 n, ?_, D.sum_masses⟩
  exact D.phase.summable_indexedMassReal D.M

/-- A supplied family of source facts binds the faithful downstream consumer. -/
def massData (D : ∀ u : QuantumNLS.PhysicalTensor.L2T L, SourceFacts L κ u) :
    QuantumNLS.MonotoneMassConsumers.MassData L κ :=
  { M := fun u => (D u).M
    finite := fun u => (D u).finite
    phase := fun u => (D u).selectedPhase }

/-- Analytic existence obligation; actual quantum-law binding is additionally required.
No proof or inhabitant is postulated. -/
def PhysicalSourceExistence : Prop :=
  ∀ (L : ℝ) [Fact (0 < L)] (κ : ℝ), 0 < κ →
    ∀ u : QuantumNLS.PhysicalTensor.L2T L, Nonempty (SourceFacts L κ u)

end QuantumNLS.PhysicalIndexedMasses

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.PhysicalIndexedMasses.SourceFacts
#print axioms QuantumNLS.PhysicalIndexedMasses.SourceFacts.boundary_cosine
#print axioms QuantumNLS.PhysicalIndexedMasses.SourceFacts.phase
#print axioms QuantumNLS.PhysicalIndexedMasses.SourceFacts.separator_zero
#print axioms QuantumNLS.PhysicalIndexedMasses.SourceFacts.separator_complex_zero
#print axioms QuantumNLS.PhysicalIndexedMasses.SourceFacts.separator_in_band
#print axioms QuantumNLS.PhysicalIndexedMasses.SourceFacts.phase_isBoundaryRealPart
#print axioms QuantumNLS.PhysicalIndexedMasses.SourceFacts.selectedPhase
#print axioms QuantumNLS.PhysicalIndexedMasses.SourceFacts.masses
#print axioms QuantumNLS.PhysicalIndexedMasses.SourceFacts.sum_masses
#print axioms QuantumNLS.PhysicalIndexedMasses.SourceFacts.not_strictMono_on_nonempty_gap
#print axioms QuantumNLS.PhysicalIndexedMasses.«DEF-014»
#print axioms QuantumNLS.PhysicalIndexedMasses.massData
#print axioms QuantumNLS.PhysicalIndexedMasses.PhysicalSourceExistence

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.PhysicalIndexedMasses." then
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
