import QuantumNLS.DEF014Round5

/-! R-2EAD2BB6, ROOT_indexed_masses.tex:16. Physical L2 theorem with its
printed positive L and coupling. R-2EAD2BB6 is proved here, never assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Set Filter Topology
namespace QuantumNLS.RootIndexedPhase
open PhysicalTensor (L2T)
variable {L κ : ℝ} [Fact (0 < L)]
abbrev theta (hκ : 0 < κ) (u : L2T L) (x : ℝ) :=
  (PhysicalContinuousBoundary.boundary hκ u x).re
abbrev separator (hκ : 0 < κ) (u : L2T L) :=
  (PhysicalSourceFinal.sourceFacts hκ u).phase.separator

theorem band_derivative (hκ : 0 < κ) (u : L2T L) {x : ℝ}
    (hx : |(L2SpatialTransfer.discriminant κ u (x : ℂ)).re| < 2) :
    HasDerivAt (theta hκ u)
      (L/2+κ*∫ t : ℝ, (x-t)⁻¹^2 ∂(PhysicalQuantumMeasure.measure hκ u)) x ∧
      0 < deriv (theta hκ u) x := by
  by_cases hu : u = 0
  · subst u
    have he : theta hκ (0 : L2T L) = fun y => L*y/2 := by
      funext y; simp [theta, PhysicalContinuousBoundary.boundary_zero]
    constructor
    · simp only [PhysicalQuantumMeasure.measure_zero, integral_zero_measure, mul_zero, add_zero]
      rw [he]
      simpa using ((hasDerivAt_id x).const_mul L).div_const 2
    · exact PhysicalContinuousBoundary.positive_band_derivative_all hκ 0 x hx
  · exact PhysicalContinuousBoundary.positive_band_derivative hκ hu hx

theorem separator_top (hκ : 0 < κ) (u : L2T L) :
    Tendsto (separator hκ u) atTop atTop := by
  apply (PhysicalSourceFinal.sourceFacts hκ u).phase.separator_strictMono.monotone.tendsto_atTop_atTop
  intro x
  obtain ⟨n, hn⟩ := exists_int_gt (theta hκ u x / Real.pi - 1/2)
  refine ⟨n, le_of_lt (((PhysicalSourceFinal.sourceFacts hκ u).phase.lt_separator_iff x n).mpr ?_)⟩
  change theta hκ u x < ((n : ℝ)+1/2)*Real.pi
  nlinarith [Real.pi_pos, (div_lt_iff₀ Real.pi_pos).mp (show theta hκ u x / Real.pi < (n : ℝ)+1/2 by linarith)]

theorem separator_bot (hκ : 0 < κ) (u : L2T L) :
    Tendsto (separator hκ u) atBot atBot := by
  apply tendsto_atBot_atBot_of_monotone
    (PhysicalSourceFinal.sourceFacts hκ u).phase.separator_strictMono.monotone
  intro x
  obtain ⟨n, hn⟩ := exists_int_lt (theta hκ u x / Real.pi - 1/2)
  refine ⟨n, le_of_lt (((PhysicalSourceFinal.sourceFacts hκ u).phase.separator_lt_iff x n).mpr ?_)⟩
  change ((n : ℝ)+1/2)*Real.pi < theta hκ u x
  nlinarith [Real.pi_pos, (lt_div_iff₀ Real.pi_pos).mp (show (n : ℝ)+1/2 < theta hκ u x / Real.pi by linarith)]

/-- The complete printed real boundary phase lemma, including vacuum. The
full upper limits and continuous boundary state the continuous extension. -/
theorem root_indexed_phase (hκ : 0 < κ) (u : L2T L) :
    Continuous (PhysicalContinuousBoundary.boundary hκ u) ∧
    (∀ x : ℝ, Tendsto (SpatialTransfer.boundaryPhase L κ (PhysicalQuantumMeasure.measure hκ u))
      (𝓝[PhysicalPhaseHolomorphic.upper] (x : ℂ))
      (𝓝 (PhysicalContinuousBoundary.boundary hκ u x))) ∧
    Continuous (theta hκ u) ∧ Monotone (theta hκ u) ∧ Function.Surjective (theta hκ u) ∧
    (∀ x : ℝ, |(L2SpatialTransfer.discriminant κ u (x : ℂ)).re| < 2 →
      HasDerivAt (theta hκ u)
        (L/2+κ*∫ t : ℝ, (x-t)⁻¹^2 ∂(PhysicalQuantumMeasure.measure hκ u)) x ∧
      0 < deriv (theta hκ u) x) ∧
    (∀ a b : ℝ, a < b →
      (∀ x ∈ Ioo a b, 2 < |(L2SpatialTransfer.discriminant κ u (x : ℂ)).re|) →
      ∃ n : ℤ, ∀ x ∈ Ioo a b, theta hκ u x = n*Real.pi) ∧
    (∀ n : ℤ, ∃! x : ℝ, theta hκ u x = MonotoneIndexedMasses.level n) ∧
    (∀ n : ℤ, L2SpatialTransfer.discriminant κ u (separator hκ u n : ℂ) = 0 ∧
      deriv (fun x : ℝ => (L2SpatialTransfer.discriminant κ u (x : ℂ)).re)
        (separator hκ u n) ≠ 0) ∧
    StrictMono (separator hκ u) ∧
    Tendsto (separator hκ u) atTop atTop ∧ Tendsto (separator hκ u) atBot atBot := by
  refine ⟨PhysicalContinuousBoundary.continuous_boundary hκ u,
    PhysicalContinuousBoundary.boundary_limit hκ u,
    Complex.continuous_re.comp (PhysicalContinuousBoundary.continuous_boundary hκ u),
    PhysicalContinuousBoundary.monotone_all hκ u, PhysicalContinuousBoundary.onto_all hκ u,
    (fun _ hx => band_derivative hκ u hx),
    (fun a b hab hg => PhysicalContinuousBoundary.gap_constancy hκ u hab hg),
    (PhysicalSourceFinal.sourceFacts hκ u).phase.exists_unique_separator,
    ?_, (PhysicalSourceFinal.sourceFacts hκ u).phase.separator_strictMono,
    separator_top hκ u, separator_bot hκ u⟩
  intro n
  exact ⟨(PhysicalSourceFinal.sourceFacts hκ u).separator_complex_zero n,
    (DEF014Crossings.separator_simple (⟨⟨κ,hκ⟩,u⟩ : DEF014Phase.Param L) n).2⟩
end QuantumNLS.RootIndexedPhase
#print axioms QuantumNLS.RootIndexedPhase.root_indexed_phase

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.RootIndexedPhase." ||
        n.toString.startsWith "_private.QuantumNLS.RootIndexedPhase." then
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
  Lean.logInfo m!"RootIndexedPhase audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
