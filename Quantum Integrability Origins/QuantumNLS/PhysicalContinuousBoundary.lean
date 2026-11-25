import QuantumNLS.BandWindowSurjectivity
import QuantumNLS.FiniteExceptionalMonotonicity
import QuantumNLS.ComplexCosineBoundary
import QuantumNLS.PhysicalUnconditionalTrace
import QuantumNLS.PhysicalBandCauchy

/-! The continuous, correctly lifted actual quantum boundary phase.
The construction consumes TS1 and the canonical measure; no SourceFacts input. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Set Filter Topology MeasureTheory
namespace QuantumNLS.PhysicalContinuousBoundary
variable {L κ : ℝ} [Fact (0 < L)]

theorem exists_boundary (hκ : 0 < κ) (u : PhysicalTensor.L2T L) :
    ∃ b : ℝ → ℂ, Continuous b ∧ ∀ x : ℝ,
      Tendsto (SpatialTransfer.boundaryPhase L κ (PhysicalQuantumMeasure.measure hκ u))
        (𝓝[PhysicalPhaseHolomorphic.upper] (x : ℂ)) (𝓝 (b x)) := by
  exact ComplexCosineBoundary.exists_boundary
    (L2DiscriminantRegularity.continuous_discriminant κ u)
    (PhysicalPhaseHolomorphic.canonical_phase_holomorphic hκ u).continuousOn
    (fun z hz => (PhysicalQuantumMeasure.im_phase_pos hκ u hz).le)
    (fun z hz => PhysicalUnconditionalTrace.upper_cosine hκ u hz)

def boundary (hκ : 0 < κ) (u : PhysicalTensor.L2T L) : ℝ → ℂ :=
  Classical.choose (exists_boundary hκ u)

theorem continuous_boundary (hκ : 0 < κ) (u : PhysicalTensor.L2T L) :
    Continuous (boundary hκ u) := (Classical.choose_spec (exists_boundary hκ u)).1

theorem boundary_limit (hκ : 0 < κ) (u : PhysicalTensor.L2T L) (x : ℝ) :
    Tendsto (SpatialTransfer.boundaryPhase L κ (PhysicalQuantumMeasure.measure hκ u))
      (𝓝[PhysicalPhaseHolomorphic.upper] (x : ℂ)) (𝓝 (boundary hκ u x)) :=
  (Classical.choose_spec (exists_boundary hκ u)).2 x

theorem boundary_cosine (hκ : 0 < κ) (u : PhysicalTensor.L2T L) (x : ℝ) :
    2 * Complex.cos (boundary hκ u x) = L2SpatialTransfer.discriminant κ u (x : ℂ) := by
  have : NeBot (𝓝[PhysicalPhaseHolomorphic.upper] (x : ℂ)) := ComplexCosineBoundary.upper_neBot x
  have hc := (Complex.continuous_cos.continuousAt.tendsto.comp (boundary_limit hκ u x)).const_mul (2 : ℂ)
  have hd := (L2DiscriminantRegularity.continuous_discriminant κ u).continuousAt.tendsto.mono_left
    (show 𝓝[PhysicalPhaseHolomorphic.upper] (x : ℂ) ≤ 𝓝 (x : ℂ) from nhdsWithin_le_nhds)
  apply tendsto_nhds_unique hc
  apply hd.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (PhysicalUnconditionalTrace.upper_cosine hκ u hz).symm

theorem boundary_im (hκ : 0 < κ) (u : PhysicalTensor.L2T L) (x : ℝ) :
    (boundary hκ u x).im = RootDensity.hfun |(L2SpatialTransfer.discriminant κ u (x : ℂ)).re| := by
  have : NeBot (𝓝[PhysicalPhaseHolomorphic.upper] (x : ℂ)) := ComplexCosineBoundary.upper_neBot x
  exact tendsto_nhds_unique
    (Complex.continuous_im.continuousAt.tendsto.comp (boundary_limit hκ u x))
    (PhysicalUnconditionalTrace.boundary_height hκ u x)

/-- On bands the globally selected lift equals the literal convergent Cauchy integral. -/
theorem band_eq (hκ : 0 < κ) {u : PhysicalTensor.L2T L} (hu : u ≠ 0)
    {x : ℝ} (hx : |(L2SpatialTransfer.discriminant κ u (x : ℂ)).re| < 2) :
    boundary hκ u x = SpatialTransfer.boundaryPhase L κ (PhysicalQuantumMeasure.measure hκ u) (x : ℂ) := by
  have : NeBot (𝓝[PhysicalPhaseHolomorphic.upper] (x : ℂ)) := ComplexCosineBoundary.upper_neBot x
  exact tendsto_nhds_unique (boundary_limit hκ u x) (PhysicalBandCauchy.band_boundary hκ hu hx)

/-- The derivative of the actual global boundary lift on open bands. -/
theorem positive_band_derivative (hκ : 0 < κ) {u : PhysicalTensor.L2T L} (hu : u ≠ 0)
    {x : ℝ} (hx : |(L2SpatialTransfer.discriminant κ u (x : ℂ)).re| < 2) :
    HasDerivAt (fun y => (boundary hκ u y).re)
      (L / 2 + κ * ∫ t : ℝ, (x - t)⁻¹ ^ 2 ∂(PhysicalQuantumMeasure.measure hκ u)) x ∧
    0 < deriv (fun y => (boundary hκ u y).re) x := by
  have ho : {y : ℝ | |(L2SpatialTransfer.discriminant κ u (y : ℂ)).re| < 2} ∈ 𝓝 x :=
    (isOpen_lt (Complex.continuous_re.comp ((L2DiscriminantRegularity.continuous_discriminant κ u).comp
      Complex.continuous_ofReal)).abs continuous_const).mem_nhds hx
  have he : (fun y => (boundary hκ u y).re) =ᶠ[𝓝 x]
      (fun y : ℝ => (SpatialTransfer.boundaryPhase L κ (PhysicalQuantumMeasure.measure hκ u) (y : ℂ)).re) := by
    filter_upwards [ho] with y hy
    exact congrArg Complex.re (band_eq hκ hu hy)
  have hd := (PhysicalBandCauchy.band_phase_hasDerivAt hκ hu hx).real_of_complex
  simp only [Complex.ofReal_re] at hd
  refine ⟨hd.congr_of_eventuallyEq he, ?_⟩
  rw [he.deriv_eq]
  exact (PhysicalBandCauchy.positive_band_derivative hκ hu hx).2

/-- The actual boundary is a single integer-pi value on every open gap interval. -/
theorem gap_constancy (hκ : 0 < κ) (u : PhysicalTensor.L2T L)
    {a b : ℝ} (hab : a < b)
    (hg : ∀ x ∈ Ioo a b, 2 < |(L2SpatialTransfer.discriminant κ u (x : ℂ)).re|) :
    ∃ k : ℤ, ∀ x ∈ Ioo a b, (boundary hκ u x).re = (k : ℝ) * Real.pi := by
  apply PhysicalTraceSymbolDependency.gap_constancy (continuous_boundary hκ u) _ hab hg
  intro x
  have hr : L2SpatialTransfer.discriminant κ u (x : ℂ) =
      ((L2SpatialTransfer.discriminant κ u (x : ℂ)).re : ℂ) := by
    apply Complex.ext <;> simp [L2DiscriminantRegularity.discriminant_real κ u x]
  exact (boundary_cosine hκ u x).trans hr

/-- Constant gap values have zero derivative; this is derived from the cosine identity. -/
theorem gap_hasDerivAt (hκ : 0 < κ) (u : PhysicalTensor.L2T L)
    {x : ℝ} (hx : 2 < |(L2SpatialTransfer.discriminant κ u (x : ℂ)).re|) :
    HasDerivAt (fun y => (boundary hκ u y).re) 0 x := by
  have ho : {y : ℝ | 2 < |(L2SpatialTransfer.discriminant κ u (y : ℂ)).re|} ∈ 𝓝 x :=
    (isOpen_lt continuous_const (Complex.continuous_re.comp
      ((L2DiscriminantRegularity.continuous_discriminant κ u).comp Complex.continuous_ofReal)).abs).mem_nhds hx
  obtain ⟨a, b, hxab, hab⟩ := mem_nhds_iff_exists_Ioo_subset.mp ho
  obtain ⟨k, hk⟩ := gap_constancy hκ u (hxab.1.trans hxab.2) (fun y hy => hab hy)
  apply (hasDerivAt_const x ((k : ℝ) * Real.pi)).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hxab.1 hxab.2] with y hy
  exact hk y hy

/-- The actual global real boundary phase is nondecreasing. -/
theorem monotone_boundary (hκ : 0 < κ) {u : PhysicalTensor.L2T L} (hu : u ≠ 0) :
    Monotone (fun y => (boundary hκ u y).re) := by
  classical
  intro a b hab
  let S := (PhysicalUpperTraceIdentity.finite_band_edges hκ u a b).toFinset
  have he : ∀ x ∈ Ioo a b, x ∉ S → |(L2SpatialTransfer.discriminant κ u (x : ℂ)).re| ≠ 2 := by
    intro x hx hs hh
    apply hs
    simpa only [S, Set.Finite.mem_toFinset, mem_ofPred_eq] using
      (show x ∈ Icc a b ∧ |(L2SpatialTransfer.discriminant κ u (x : ℂ)).re| = 2 from ⟨⟨hx.1.le, hx.2.le⟩, hh⟩)
  apply FiniteExceptionalMonotonicity.image_le (fun y => (boundary hκ u y).re)
    (Complex.continuous_re.comp (continuous_boundary hκ u)) S a b hab
  · intro x hx hs
    rcases lt_or_gt_of_ne (he x hx hs) with hb | hg
    · exact (positive_band_derivative hκ hu hb).1.differentiableAt
    · exact (gap_hasDerivAt hκ u hg).differentiableAt
  · intro x hx hs
    rcases lt_or_gt_of_ne (he x hx hs) with hb | hg
    · exact (positive_band_derivative hκ hu hb).2.le
    · rw [(gap_hasDerivAt hκ u hg).deriv]

/-- Uniform free-zero band windows force the actual lifted phase onto the real line. -/
theorem onto_boundary (hκ : 0 < κ) {u : PhysicalTensor.L2T L} (hu : u ≠ 0) :
    Function.Surjective (fun y => (boundary hκ u y).re) := by
  apply BandWindowSurjectivity.surjective (f := fun y => (boundary hκ u y).re)
    (d := fun t => (L2SpatialTransfer.discriminant κ u (t : ℂ)).re) (Fact.out : 0 < L)
    (Complex.continuous_re.comp (continuous_boundary hκ u)) (monotone_boundary hκ hu)
  · intro x hx
    have hh := positive_band_derivative hκ hu hx
    refine ⟨hh.1.differentiableAt, ?_⟩
    rw [hh.1.deriv]
    have hi : 0 ≤ ∫ t : ℝ, (x - t)⁻¹ ^ 2 ∂(PhysicalQuantumMeasure.measure hκ u) :=
      integral_nonneg (fun _ => sq_nonneg _)
    nlinarith
  · exact L1TraceGeometry.L2_trace_asymptotic hκ u

theorem boundary_zero (hκ : 0 < κ) (x : ℝ) :
    boundary hκ (0 : PhysicalTensor.L2T L) x = (L : ℂ) * (x : ℂ) / 2 := by
  have : NeBot (𝓝[PhysicalPhaseHolomorphic.upper] (x : ℂ)) := ComplexCosineBoundary.upper_neBot x
  apply tendsto_nhds_unique (boundary_limit hκ 0 x)
  have hc : Continuous (fun z : ℂ => (L : ℂ) * z / 2) := by fun_prop
  have he : SpatialTransfer.boundaryPhase L κ (PhysicalQuantumMeasure.measure hκ (0 : PhysicalTensor.L2T L)) =
      (fun z : ℂ => (L : ℂ) * z / 2) := by
    funext z
    simp [SpatialTransfer.boundaryPhase, EmpiricalRapidity.cauchyTransform]
  rw [he]
  exact hc.continuousAt.tendsto.mono_left
      (show 𝓝[PhysicalPhaseHolomorphic.upper] (x : ℂ) ≤ 𝓝 (x : ℂ) from nhdsWithin_le_nhds)

theorem monotone_all (hκ : 0 < κ) (u : PhysicalTensor.L2T L) :
    Monotone (fun y => (boundary hκ u y).re) := by
  by_cases hu : u = 0
  · subst u
    intro x y hxy
    simp only [boundary_zero, Complex.div_ofNat_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hxy (Fact.out : 0 < L).le) (by norm_num)
  · exact monotone_boundary hκ hu

theorem onto_all (hκ : 0 < κ) (u : PhysicalTensor.L2T L) :
    Function.Surjective (fun y => (boundary hκ u y).re) := by
  by_cases hu : u = 0
  · subst u
    intro y
    refine ⟨2 * y / L, ?_⟩
    simp only [boundary_zero, Complex.div_ofNat_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    field_simp [(Fact.out : 0 < L).ne']
  · exact onto_boundary hκ hu

theorem positive_band_derivative_all (hκ : 0 < κ) (u : PhysicalTensor.L2T L)
    (x : ℝ) (hx : |(L2SpatialTransfer.discriminant κ u (x : ℂ)).re| < 2) :
    0 < deriv (fun y => (boundary hκ u y).re) x := by
  by_cases hu : u = 0
  · subst u
    have he : (fun y : ℝ => (boundary hκ (0 : PhysicalTensor.L2T L) y).re) =
        (fun y => L * y / 2) := by funext y; simp [boundary_zero]
    rw [he]
    have hd : HasDerivAt (fun y : ℝ => L * y / 2) (L / 2) x := by
      simpa using ((hasDerivAt_id x).const_mul L).div_const 2
    rw [hd.deriv]
    exact div_pos Fact.out (by norm_num)
  · exact (positive_band_derivative hκ hu hx).2

end QuantumNLS.PhysicalContinuousBoundary

#print axioms QuantumNLS.PhysicalContinuousBoundary.exists_boundary
#print axioms QuantumNLS.PhysicalContinuousBoundary.boundary
#print axioms QuantumNLS.PhysicalContinuousBoundary.continuous_boundary
#print axioms QuantumNLS.PhysicalContinuousBoundary.boundary_limit
#print axioms QuantumNLS.PhysicalContinuousBoundary.boundary_cosine
#print axioms QuantumNLS.PhysicalContinuousBoundary.boundary_im
#print axioms QuantumNLS.PhysicalContinuousBoundary.band_eq
#print axioms QuantumNLS.PhysicalContinuousBoundary.positive_band_derivative
#print axioms QuantumNLS.PhysicalContinuousBoundary.gap_constancy
#print axioms QuantumNLS.PhysicalContinuousBoundary.gap_hasDerivAt
#print axioms QuantumNLS.PhysicalContinuousBoundary.monotone_boundary
#print axioms QuantumNLS.PhysicalContinuousBoundary.onto_boundary
#print axioms QuantumNLS.PhysicalContinuousBoundary.boundary_zero
#print axioms QuantumNLS.PhysicalContinuousBoundary.monotone_all
#print axioms QuantumNLS.PhysicalContinuousBoundary.onto_all
#print axioms QuantumNLS.PhysicalContinuousBoundary.positive_band_derivative_all

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.PhysicalContinuousBoundary." then
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
