import QuantumNLS.RootDensityIdentification

/-! The actual canonical Cauchy transform extends through every open band.
All distance and form inputs below are derived from the canonical density. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Filter Topology Set MeasureTheory
namespace QuantumNLS.PhysicalBandCauchy
variable {L κ : ℝ} [Fact (0 < L)]

/-- The canonical quantum measure vanishes on every measurable open-band set. -/
theorem measure_band_zero (hκ : 0 < κ) {u : PhysicalTensor.L2T L} (hu : u ≠ 0)
    {S : Set ℝ} (hS : MeasurableSet S)
    (hband : ∀ t ∈ S, |(L2SpatialTransfer.discriminant κ u (t : ℂ)).re| ≤ 2) :
    PhysicalQuantumMeasure.measure hκ u S = 0 := by
  rw [RootDensityIdentification.root_density hκ hu, withDensity_apply _ hS]
  apply setLIntegral_eq_zero hS
  intro t ht
  simp [RootDensityIdentification.dens, RootDensity.hfun, not_lt.mpr (hband t ht)]

/-- Every band point has a positive distance from the canonical measure almost everywhere. -/
theorem band_away (hκ : 0 < κ) {u : PhysicalTensor.L2T L} (hu : u ≠ 0)
    {x : ℝ} (hx : |(L2SpatialTransfer.discriminant κ u (x : ℂ)).re| < 2) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᵐ t ∂(PhysicalQuantumMeasure.measure hκ u), δ ≤ |x - t| := by
  have ho : IsOpen {y : ℝ | |(L2SpatialTransfer.discriminant κ u (y : ℂ)).re| < 2} :=
    isOpen_lt (Complex.continuous_re.comp ((L2DiscriminantRegularity.continuous_discriminant κ u).comp
      Complex.continuous_ofReal)).abs continuous_const
  obtain ⟨δ, hδ, hb⟩ := Metric.mem_nhds_iff.mp (ho.mem_nhds hx)
  refine ⟨δ, hδ, ?_⟩
  have hz : PhysicalQuantumMeasure.measure hκ u (Metric.ball x δ) = 0 :=
    measure_band_zero hκ hu Metric.isOpen_ball.measurableSet (fun t ht => (hb ht).le)
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with t ht
  simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm, not_lt] using ht

/-- A finite measure separated from a real point has a holomorphic Cauchy integral there. -/
theorem hasDerivAt_cauchy_of_away (M : Measure ℝ) [IsFiniteMeasure M]
    {x δ : ℝ} (hδ : 0 < δ) (ha : ∀ᵐ (t : ℝ) ∂M, δ ≤ |x - t|) :
    HasDerivAt (EmpiricalRapidity.cauchyTransform M)
      (∫ t : ℝ, -(((x : ℂ) - (t : ℂ))⁻¹ ^ 2) ∂M) (x : ℂ) := by
  let S : Set ℂ := Metric.ball (x : ℂ) (δ / 2)
  let F : ℂ → ℝ → ℂ := fun z t => (z - (t : ℂ))⁻¹
  let D : ℂ → ℝ → ℂ := fun z t => -((z - (t : ℂ))⁻¹ ^ 2)
  have hs : S ∈ 𝓝 (x : ℂ) := Metric.ball_mem_nhds _ (by positivity)
  have hb : ∀ᵐ (t : ℝ) ∂M, ∀ z ∈ S, δ / 2 ≤ ‖z - (t : ℂ)‖ := by
    filter_upwards [ha] with t ht z hz
    have hnorm : δ ≤ ‖(x : ℂ) - (t : ℂ)‖ := by
      simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using ht
    have hz' : ‖(x : ℂ) - z‖ < δ / 2 := by
      simpa [S, Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hz
    have ht := norm_add_le ((x : ℂ) - z) (z - (t : ℂ))
    rw [sub_add_sub_cancel] at ht
    linarith
  have hmeas (z : ℂ) : AEStronglyMeasurable (F z) M := by
    exact ((measurable_const.sub Complex.measurable_ofReal).inv).aestronglyMeasurable
  have hnorm : ∀ᵐ (t : ℝ) ∂M, ∀ z ∈ S, ‖F z t‖ ≤ (δ / 2)⁻¹ := by
    filter_upwards [hb] with t ht z hz
    exact (norm_inv _).trans_le (inv_anti₀ (by positivity) (ht z hz))
  have hxS : (x : ℂ) ∈ S := Metric.mem_ball_self (by positivity)
  have hi : Integrable (F (x : ℂ)) M :=
    (integrable_const ((δ / 2)⁻¹)).mono' (hmeas _) (hnorm.mono (fun t ht => ht _ hxS))
  have hmD : AEStronglyMeasurable (D (x : ℂ)) M := (hmeas _).pow 2 |>.neg
  have hbd : ∀ᵐ (t : ℝ) ∂M, ∀ z ∈ S, ‖D z t‖ ≤ (δ / 2)⁻¹ ^ 2 := by
    filter_upwards [hnorm] with t ht z hz
    simpa [D, F] using pow_le_pow_left₀ (norm_nonneg (F z t)) (ht z hz) 2
  have hd : ∀ᵐ (t : ℝ) ∂M, ∀ z ∈ S, HasDerivAt (fun w => F w t) (D z t) z := by
    filter_upwards [hb] with t ht z hz
    have hn : z - (t : ℂ) ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by positivity) (ht z hz))
    exact (((hasDerivAt_id z).sub_const (t : ℂ)).inv hn).congr_deriv
      (by simp [D, div_eq_mul_inv, inv_pow])
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs
    (Eventually.of_forall hmeas) hi hmD hbd (integrable_const _) hd).2

/-- Literal continuation of the canonical phase through an open band. -/
theorem band_phase_hasDerivAt (hκ : 0 < κ) {u : PhysicalTensor.L2T L} (hu : u ≠ 0)
    {x : ℝ} (hx : |(L2SpatialTransfer.discriminant κ u (x : ℂ)).re| < 2) :
    HasDerivAt (SpatialTransfer.boundaryPhase L κ (PhysicalQuantumMeasure.measure hκ u))
      ((L / 2 + κ * ∫ t : ℝ, (x - t)⁻¹ ^ 2 ∂(PhysicalQuantumMeasure.measure hκ u) : ℝ) : ℂ)
      (x : ℂ) := by
  obtain ⟨δ, hδ, ha⟩ := band_away hκ hu hx
  have hc := hasDerivAt_cauchy_of_away (PhysicalQuantumMeasure.measure hκ u) hδ ha
  have hd := (((hasDerivAt_id (x : ℂ)).const_mul (L : ℂ)).div_const 2).sub (hc.const_mul (κ : ℂ))
  have he : (∫ t : ℝ, -(((x : ℂ) - (t : ℂ))⁻¹ ^ 2) ∂(PhysicalQuantumMeasure.measure hκ u)) =
      -(↑(∫ t : ℝ, (x - t)⁻¹ ^ 2 ∂(PhysicalQuantumMeasure.measure hκ u)) : ℂ) := by
    simp_rw [← Complex.ofReal_sub, ← Complex.ofReal_inv, ← Complex.ofReal_pow]
    rw [integral_neg]
    congr 1
    exact integral_complex_ofReal
  convert hd using 1
  · funext z
    simp [SpatialTransfer.boundaryPhase, mul_comm]
  · rw [he]
    push_cast
    ring

/-- The source's strictly positive derivative formula on every actual open band. -/
theorem positive_band_derivative (hκ : 0 < κ) {u : PhysicalTensor.L2T L} (hu : u ≠ 0)
    {x : ℝ} (hx : |(L2SpatialTransfer.discriminant κ u (x : ℂ)).re| < 2) :
    deriv (fun y : ℝ => (SpatialTransfer.boundaryPhase L κ
      (PhysicalQuantumMeasure.measure hκ u) (y : ℂ)).re) x =
        L / 2 + κ * ∫ t : ℝ, (x - t)⁻¹ ^ 2 ∂(PhysicalQuantumMeasure.measure hκ u) ∧
    0 < deriv (fun y : ℝ => (SpatialTransfer.boundaryPhase L κ
      (PhysicalQuantumMeasure.measure hκ u) (y : ℂ)).re) x := by
  have hd := (band_phase_hasDerivAt hκ hu hx).real_of_complex
  simp only [Complex.ofReal_re] at hd
  refine ⟨hd.deriv, ?_⟩
  rw [hd.deriv]
  have hL : 0 < L := Fact.out
  have hi : 0 ≤ ∫ t : ℝ, (x - t)⁻¹ ^ 2 ∂(PhysicalQuantumMeasure.measure hκ u) :=
    integral_nonneg (fun _ => sq_nonneg _)
  positivity

/-- At a band point, the full canonical complex phase has its literal real-axis limit. -/
theorem band_boundary (hκ : 0 < κ) {u : PhysicalTensor.L2T L} (hu : u ≠ 0)
    {x : ℝ} (hx : |(L2SpatialTransfer.discriminant κ u (x : ℂ)).re| < 2) :
    Tendsto (SpatialTransfer.boundaryPhase L κ (PhysicalQuantumMeasure.measure hκ u))
      (𝓝[PhysicalPhaseHolomorphic.upper] (x : ℂ))
      (𝓝 (SpatialTransfer.boundaryPhase L κ (PhysicalQuantumMeasure.measure hκ u) (x : ℂ))) :=
  (band_phase_hasDerivAt hκ hu hx).continuousAt.tendsto.mono_left nhdsWithin_le_nhds

end QuantumNLS.PhysicalBandCauchy

#print axioms QuantumNLS.PhysicalBandCauchy.band_phase_hasDerivAt
#print axioms QuantumNLS.PhysicalBandCauchy.positive_band_derivative
#print axioms QuantumNLS.PhysicalBandCauchy.band_boundary
#print axioms QuantumNLS.PhysicalBandCauchy.measure_band_zero

#print axioms QuantumNLS.PhysicalBandCauchy.band_away

#print axioms QuantumNLS.PhysicalBandCauchy.hasDerivAt_cauchy_of_away

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.PhysicalBandCauchy." then
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
