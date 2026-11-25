import QuantumNLS.PhysicalL2Normalization

/-! Holomorphy of the actual Cauchy-defined phase throughout the open
upper half-plane, proved by differentiating its finite-measure integral.
No boundary regularity or trace-symbol identity is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open MeasureTheory Filter Topology Set
namespace QuantumNLS.PhysicalPhaseHolomorphic

def upper : Set ℂ := {z | 0 < z.im}

theorem isOpen_upper : IsOpen upper := isOpen_lt continuous_const Complex.continuous_im

/-- Differentiation under the Cauchy integral on the upper half-plane. -/
theorem hasDerivAt_cauchy (M : Measure ℝ) [IsFiniteMeasure M] {z₀ : ℂ} (hz₀ : 0 < z₀.im) :
    HasDerivAt (EmpiricalRapidity.cauchyTransform M)
      (∫ t : ℝ, -((z₀ - (t : ℂ))⁻¹ ^ 2) ∂M) z₀ := by
  let s : Set ℂ := {z | z₀.im / 2 < z.im}
  let F : ℂ → ℝ → ℂ := fun z t => (z - (t : ℂ))⁻¹
  let D : ℂ → ℝ → ℂ := fun z t => -((z - (t : ℂ))⁻¹ ^ 2)
  have hs : s ∈ 𝓝 z₀ := (isOpen_lt continuous_const Complex.continuous_im).mem_nhds (by
    dsimp [s]; linarith)
  have hz : ∀ z ∈ s, 0 < z.im := by intro z h; dsimp [s] at h; linarith
  have hbound : ∀ z ∈ s, ∀ t : ℝ, ‖D z t‖ ≤ (z₀.im / 2)⁻¹ ^ 2 := by
    intro z hzs t
    dsimp [D]
    rw [norm_neg, norm_pow]
    apply pow_le_pow_left₀ (norm_nonneg _) _ 2
    have h := EmpiricalRapidity.norm_cauchyIntegrand_le z (hz z hzs).ne' t
    rw [abs_of_pos (hz z hzs)] at h
    exact h.trans (inv_anti₀ (by linarith : 0 < z₀.im / 2) (by exact le_of_lt hzs))
  have hdiff : ∀ z ∈ s, ∀ t : ℝ, HasDerivAt (fun w => F w t) (D z t) z := by
    intro z hzs t
    have h := ((hasDerivAt_id z).sub_const (t : ℂ)).inv
      (EmpiricalRapidity.sub_ne_zero_of_im z (hz z hzs).ne' t)
    exact h.congr_deriv (by simp [D, div_eq_mul_inv, inv_pow])
  have hmeas : ∀ᶠ z in 𝓝 z₀, AEStronglyMeasurable (F z) M := by
    filter_upwards [hs] with z hzs
    exact (EmpiricalRapidity.continuous_cauchyIntegrand z (hz z hzs).ne').aestronglyMeasurable
  have hDmeas : AEStronglyMeasurable (D z₀) M :=
    ((EmpiricalRapidity.continuous_cauchyIntegrand z₀ hz₀.ne').pow 2).neg.aestronglyMeasurable
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hmeas
    (EmpiricalRapidity.integrable_cauchyIntegrand M z₀ hz₀.ne') hDmeas
    (Filter.Eventually.of_forall (fun t z hzs => hbound z hzs t))
    (integrable_const ((z₀.im / 2)⁻¹ ^ 2))
    (Filter.Eventually.of_forall (fun t z hzs => hdiff z hzs t))).2

/-- Holomorphy requires only that the positive measure be finite. -/
theorem differentiableOn_cauchy (M : Measure ℝ) [IsFiniteMeasure M] :
    DifferentiableOn ℂ (EmpiricalRapidity.cauchyTransform M) upper :=
  fun _ hz => (hasDerivAt_cauchy M hz).differentiableAt.differentiableWithinAt

/-- The Cauchy-defined phase is holomorphic on the whole upper half-plane. -/
theorem differentiableOn_phase (L κ : ℝ) (M : Measure ℝ) [IsFiniteMeasure M] :
    DifferentiableOn ℂ (SpatialTransfer.boundaryPhase L κ M) upper := by
  unfold SpatialTransfer.boundaryPhase
  have hlin : Differentiable ℂ (fun z : ℂ => (L : ℂ) * z / 2) := by fun_prop
  exact hlin.differentiableOn.sub ((differentiableOn_cauchy M).const_mul (κ : ℂ))

/-- The physical phase of the already constructed canonical quantum measure
has no additional holomorphy premise. -/
theorem canonical_phase_holomorphic {L κ : ℝ} [Fact (0 < L)] (hκ : 0 < κ)
    (u : PhysicalTensor.L2T L) :
    AnalyticOnNhd ℂ (SpatialTransfer.boundaryPhase L κ (PhysicalQuantumMeasure.measure hκ u)) upper :=
  (differentiableOn_phase L κ (PhysicalQuantumMeasure.measure hκ u)).analyticOnNhd isOpen_upper

end QuantumNLS.PhysicalPhaseHolomorphic

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.PhysicalPhaseHolomorphic.upper
#print axioms QuantumNLS.PhysicalPhaseHolomorphic.isOpen_upper
#print axioms QuantumNLS.PhysicalPhaseHolomorphic.hasDerivAt_cauchy
#print axioms QuantumNLS.PhysicalPhaseHolomorphic.differentiableOn_cauchy
#print axioms QuantumNLS.PhysicalPhaseHolomorphic.differentiableOn_phase
#print axioms QuantumNLS.PhysicalPhaseHolomorphic.canonical_phase_holomorphic

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.PhysicalPhaseHolomorphic." then
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
