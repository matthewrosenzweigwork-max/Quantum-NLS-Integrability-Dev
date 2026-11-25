import QuantumNLS.PhysicalUpperTraceIdentity

/-! Actual continuous imaginary boundary, including every band edge.
The elementary ellipse identity avoids choosing a branch of complex arcosh. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Filter Topology Set
namespace QuantumNLS.PhysicalPhaseHeightBoundary

/-- The two focal distances of cosine determine its phase height. -/
theorem focal_distances (z : ℂ) :
    ‖Complex.cos z + 1‖ = Real.cosh z.im + Real.cos z.re ∧
      ‖Complex.cos z - 1‖ = Real.cosh z.im - Real.cos z.re := by
  have hc : (Complex.cos z).re = Real.cos z.re * Real.cosh z.im := by
    rw [Complex.cos_eq]
    simp [Complex.mul_re, Complex.mul_im, Complex.cos_ofReal_re]
  have hn := PhysicalPhaseAtomlessness.norm_cos_sq z
  have hh := Real.cosh_sq z.im
  have hp := Real.one_le_cosh z.im
  have hcl := Real.neg_one_le_cos z.re
  have hcu := Real.cos_le_one z.re
  have h₁ : ‖Complex.cos z + 1‖ ^ 2 = ‖Complex.cos z‖ ^ 2 +
      2 * (Complex.cos z).re + 1 := by
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re,
      Complex.add_im, Complex.one_re, Complex.one_im, add_zero]
    ring
  have h₂ : ‖Complex.cos z - 1‖ ^ 2 = ‖Complex.cos z‖ ^ 2 -
      2 * (Complex.cos z).re + 1 := by
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re,
      Complex.sub_im, Complex.one_re, Complex.one_im, sub_zero]
    ring
  constructor <;> nlinarith [norm_nonneg (Complex.cos z + 1), norm_nonneg (Complex.cos z - 1)]

/-- Continuous height defined directly from an arbitrary complex trace. -/
def height (d : ℂ) : ℝ := Real.arcosh ((‖d + 2‖ + ‖d - 2‖) / 4)

theorem one_le_focal (d : ℂ) : 1 ≤ (‖d + 2‖ + ‖d - 2‖) / 4 := by
  have h := norm_sub_le (d + 2) (d - 2)
  have he : d + 2 - (d - 2) = (4 : ℂ) := by ring
  rw [he] at h
  norm_num at h
  linarith

theorem continuous_height : Continuous height :=
  Real.continuousOn_arcosh.comp_continuous (by fun_prop)
    (fun d => one_le_focal d)

/-- The actual positive height is uniquely fixed by the cosine trace. -/
theorem height_cos {z : ℂ} (hz : 0 ≤ z.im) : height (2 * Complex.cos z) = z.im := by
  obtain ⟨h₁, h₂⟩ := focal_distances z
  have he₁ : 2 * Complex.cos z + 2 = 2 * (Complex.cos z + 1) := by ring
  have he₂ : 2 * Complex.cos z - 2 = 2 * (Complex.cos z - 1) := by ring
  unfold height
  rw [he₁, he₂, norm_mul, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num, h₁, h₂]
  convert Real.arcosh_cosh hz using 1
  congr 1
  ring

/-- On the real axis, this is exactly the source's piecewise arcosh height. -/
theorem height_real (d : ℝ) : height (d : ℂ) = RootDensity.hfun |d| := by
  rw [height, RootDensity.hfun_eq_arcosh_max]
  congr 1
  simp only [← Complex.ofReal_ofNat, ← Complex.ofReal_add, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]
  rcases le_total 0 d with hd | hd
  · by_cases h : d ≤ 2
    · rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith), abs_of_nonneg hd,
        max_eq_right (by linarith)]
      ring
    · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg hd,
        max_eq_left (by linarith)]
      ring
  · by_cases h : -2 ≤ d
    · rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos hd,
        max_eq_right (by linarith)]
      ring
    · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos hd,
        max_eq_left (by linarith)]
      ring

variable {L κ : ℝ} [Fact (0 < L)]

/-- A literal continuous extension of the actual phase height to all of ℂ. -/
def canonicalHeight (κ : ℝ) (u : PhysicalTensor.L2T L) (z : ℂ) : ℝ :=
  height (L2SpatialTransfer.discriminant κ u z)

theorem continuous_canonicalHeight (κ : ℝ) (u : PhysicalTensor.L2T L) :
    Continuous (canonicalHeight κ u) :=
  continuous_height.comp (PhysicalUpperTraceIdentity.entire_discriminant κ u).continuous

theorem canonicalHeight_eq_im (hκ : 0 < κ) {u : PhysicalTensor.L2T L} (hu : u ≠ 0)
    (htrace : PhysicalTraceSymbolDependency.TraceSymbolIdentity L κ u)
    {z : ℂ} (hz : 0 < z.im) :
    canonicalHeight κ u z =
      (SpatialTransfer.boundaryPhase L κ (PhysicalQuantumMeasure.measure hκ u) z).im := by
  unfold canonicalHeight
  rw [← PhysicalUpperTraceIdentity.upper_cosine hκ hu htrace hz]
  exact height_cos (PhysicalQuantumMeasure.im_phase_pos hκ u hz).le

/-- Full approach from the upper half-plane, at every real point,
including closed gaps and band edges. Only TraceSymbolIdentity is conditional. -/
theorem boundary_height (hκ : 0 < κ) {u : PhysicalTensor.L2T L} (hu : u ≠ 0)
    (htrace : PhysicalTraceSymbolDependency.TraceSymbolIdentity L κ u) (x : ℝ) :
    Tendsto (fun z : ℂ =>
      (SpatialTransfer.boundaryPhase L κ (PhysicalQuantumMeasure.measure hκ u) z).im)
      (𝓝[PhysicalPhaseHolomorphic.upper] (x : ℂ))
      (𝓝 (RootDensity.hfun |(L2SpatialTransfer.discriminant κ u (x : ℂ)).re|)) := by
  have hreal : L2SpatialTransfer.discriminant κ u (x : ℂ) =
      ((L2SpatialTransfer.discriminant κ u (x : ℂ)).re : ℂ) := by
    apply Complex.ext <;> simp [L2DiscriminantRegularity.discriminant_real κ u x]
  have he : canonicalHeight κ u (x : ℂ) =
      RootDensity.hfun |(L2SpatialTransfer.discriminant κ u (x : ℂ)).re| := by
    unfold canonicalHeight
    calc
      _ = height (((L2SpatialTransfer.discriminant κ u (x : ℂ)).re : ℂ)) := congrArg height hreal
      _ = _ := height_real _
  rw [← he]
  apply ((continuous_canonicalHeight κ u).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact canonicalHeight_eq_im hκ hu htrace hz

/-- Locally uniform vertical boundary height on every real compact set.
This is the source's uniform Poisson-height limit before measure inversion. -/
theorem uniform_boundary_height (hκ : 0 < κ) {u : PhysicalTensor.L2T L} (hu : u ≠ 0)
    (htrace : PhysicalTraceSymbolDependency.TraceSymbolIdentity L κ u)
    {K : Set ℝ} (hK : IsCompact K) :
    TendstoUniformlyOn (fun η : ℝ => fun x : ℝ =>
      (SpatialTransfer.boundaryPhase L κ (PhysicalQuantumMeasure.measure hκ u)
        ((x : ℂ) + (η : ℂ) * Complex.I)).im)
      (fun x => RootDensity.hfun |(L2SpatialTransfer.discriminant κ u (x : ℂ)).re|)
      (𝓝[>] 0) K := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let F : ℝ → K → ℝ := fun η x => canonicalHeight κ u ((x.val : ℂ) + (η : ℂ) * Complex.I)
  have hc : Continuous (Function.uncurry F) := by
    apply (continuous_canonicalHeight κ u).comp
    fun_prop
  have ht := Continuous.tendstoUniformly F hc 0
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  intro v hv
  filter_upwards [(ht v hv).filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with η hη hpos
  intro x
  have he₁ : F η x =
      (SpatialTransfer.boundaryPhase L κ (PhysicalQuantumMeasure.measure hκ u)
        ((x.val : ℂ) + (η : ℂ) * Complex.I)).im :=
    canonicalHeight_eq_im hκ hu htrace (by simpa using hpos)
  have he₀ : F 0 x = RootDensity.hfun |(L2SpatialTransfer.discriminant κ u (x.val : ℂ)).re| := by
    change height (L2SpatialTransfer.discriminant κ u ((x.val : ℂ) + (0 : ℂ) * Complex.I)) = _
    simp only [zero_mul, add_zero]
    have hr : L2SpatialTransfer.discriminant κ u (x.val : ℂ) =
        ((L2SpatialTransfer.discriminant κ u (x.val : ℂ)).re : ℂ) := by
      apply Complex.ext <;> simp [L2DiscriminantRegularity.discriminant_real κ u x.val]
    exact (congrArg height hr).trans (height_real _)
  simpa only [Function.comp_apply, he₀, he₁] using hη x

end QuantumNLS.PhysicalPhaseHeightBoundary

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.PhysicalPhaseHeightBoundary.focal_distances
#print axioms QuantumNLS.PhysicalPhaseHeightBoundary.height
#print axioms QuantumNLS.PhysicalPhaseHeightBoundary.one_le_focal
#print axioms QuantumNLS.PhysicalPhaseHeightBoundary.continuous_height
#print axioms QuantumNLS.PhysicalPhaseHeightBoundary.height_cos
#print axioms QuantumNLS.PhysicalPhaseHeightBoundary.height_real
#print axioms QuantumNLS.PhysicalPhaseHeightBoundary.canonicalHeight
#print axioms QuantumNLS.PhysicalPhaseHeightBoundary.continuous_canonicalHeight
#print axioms QuantumNLS.PhysicalPhaseHeightBoundary.canonicalHeight_eq_im
#print axioms QuantumNLS.PhysicalPhaseHeightBoundary.boundary_height
#print axioms QuantumNLS.PhysicalPhaseHeightBoundary.uniform_boundary_height

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.PhysicalPhaseHeightBoundary." then
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
