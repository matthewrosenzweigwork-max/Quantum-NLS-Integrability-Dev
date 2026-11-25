import QuantumNLS.L1TransferHolomorphic
import QuantumNLS.PhysicalPhaseHolomorphic
import QuantumNLS.PhysicalPhaseAtomlessness
import QuantumNLS.PhysicalTraceSymbolDependency

/-! Analytic continuation for the actual L2 Volterra discriminant and the
canonical quantum measure. The high trace-symbol proposition remains the
sole premise and is not proved here. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open MeasureTheory Filter Topology Set
namespace QuantumNLS.PhysicalUpperTraceIdentity
open SpatialTransfer L2SpatialTransfer PhysicalPhaseHolomorphic
attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
local instance : TopologicalSpace.PseudoMetrizableSpace Mat2 :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin 2 → Fin 2 → ℂ))
local instance : ENormedAddMonoid Mat2 := NormedAddGroup.toENormedAddMonoid
variable {L κ : ℝ} [Fact (0 < L)]

/-- Entire parameter dependence for every actual L2 profile. -/
theorem entire_transfer (κ : ℝ) (u : PhysicalTensor.L2T L)
    {x : ℝ} (hx : x ∈ Icc 0 L) :
    Differentiable ℂ (fun z : ℂ => L2SpatialTransfer.spatialTransfer κ u z x) := by
  apply L1TransferHolomorphic.differentiable_transfer (Fact.out : 0 < L).le
    (fun z => intervalIntegrable_coef (intervalIntegrable_profile u) _ _ z)
  · intro t _
    let D : Mat2 := !![-Complex.I / 2, 0; 0, Complex.I / 2]
    have he : (fun z : ℂ => balCoef κ (profile u) z t) =
        (fun z => z • D + balCoef κ (profile u) 0 t) := by
      funext z
      ext i j
      fin_cases i <;> fin_cases j <;> simp [balCoef, coef, D] <;> ring
    change Differentiable ℂ (fun z => balCoef κ (profile u) z t)
    rw [he]
    exact (differentiable_id.smul_const D).add_const _
  · intro z₀
    let g : ℝ → ℝ := fun t => (‖z₀‖ + 2) / 2 + Real.sqrt κ * ‖profile u t‖
    refine ⟨g, intervalIntegrable_const.add ((intervalIntegrable_profile u).norm.const_mul _), ?_⟩
    intro z hz t _
    have hzR : ‖z‖ ≤ ‖z₀‖ + 2 := by
      have hh : ‖z - z₀‖ ≤ 2 := by simpa [dist_eq_norm] using hz
      linarith [norm_le_norm_add_norm_sub' z z₀, norm_sub_rev z z₀]
    exact (RootDiscriminantContinuity.norm_balCoef_le κ (profile u) z t).trans
      (by dsimp [g]; linarith)
  · exact hx

/-- The physical discriminant is entire, with no spectral premise. -/
theorem entire_discriminant (κ : ℝ) (u : PhysicalTensor.L2T L) :
    Differentiable ℂ (L2SpatialTransfer.discriminant κ u) := by
  let tr : Mat2 →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin 2) ℂ ℂ)
  exact tr.differentiable.comp (entire_transfer κ u
    (show L ∈ Icc 0 L from ⟨(Fact.out : 0 < L).le, le_rfl⟩))

/-- Actual physical band edges are locally finite. Entirety and the already
proved existence of open-band points exclude an identically-edge trace. -/
theorem finite_band_edges (hκ : 0 < κ) (u : PhysicalTensor.L2T L) (a b : ℝ) :
    {t : ℝ | t ∈ Icc a b ∧
      |(L2SpatialTransfer.discriminant κ u (t : ℂ)).re| = 2}.Finite := by
  apply RootDensity.finite_endpoints (entire_discriminant κ u)
    (fun t => Complex.ext rfl (by simp [L2DiscriminantRegularity.discriminant_real κ u t]))
  obtain ⟨p, _, hp⟩ := (PhysicalL2BandGeometry.unbounded_bands hκ u 0).1
  exact ⟨p, ne_of_lt hp⟩

/-- The high-half-plane identity extends to the full PhysicalPhaseHolomorphic.upper half-plane.
No boundary equation is assumed, and the canonical measure is unchanged. -/
theorem upper_cosine (hκ : 0 < κ) {u : PhysicalTensor.L2T L} (hu : u ≠ 0)
    (htrace : PhysicalTraceSymbolDependency.TraceSymbolIdentity L κ u)
    {z : ℂ} (hz : 0 < z.im) :
    2 * Complex.cos (SpatialTransfer.boundaryPhase L κ (PhysicalQuantumMeasure.measure hκ u) z) =
      L2SpatialTransfer.discriminant κ u z := by
  let y : ℝ := max (4 * (κ * ‖u‖ ^ 2)) (Real.log 16 / L) + 1
  let z₀ : ℂ := (y : ℂ) * Complex.I
  have hL : 0 < L := Fact.out
  have hy₁ : 4 * (κ * ‖u‖ ^ 2) < y := by dsimp [y]; linarith [le_max_left (4 * (κ * ‖u‖ ^ 2)) (Real.log 16 / L)]
  have hy₂ : Real.log 16 < L * y := by
    have h : Real.log 16 / L < y := by dsimp [y]; linarith [le_max_right (4 * (κ * ‖u‖ ^ 2)) (Real.log 16 / L)]
    exact (div_lt_iff₀ hL).mp h |>.trans_eq (mul_comm y L)
  have hy : 0 < y := lt_of_le_of_lt (by positivity) hy₁
  have hz₀ : z₀ ∈ PhysicalPhaseHolomorphic.upper := by simpa [PhysicalPhaseHolomorphic.upper, z₀] using hy
  have hf : AnalyticOnNhd ℂ (fun z =>
      2 * Complex.cos (SpatialTransfer.boundaryPhase L κ (PhysicalQuantumMeasure.measure hκ u) z)) PhysicalPhaseHolomorphic.upper :=
    ((differentiableOn_phase L κ (PhysicalQuantumMeasure.measure hκ u)).ccos.const_mul 2).analyticOnNhd isOpen_upper
  have hg : AnalyticOnNhd ℂ (L2SpatialTransfer.discriminant κ u) PhysicalPhaseHolomorphic.upper :=
    (entire_discriminant κ u).differentiableOn.analyticOnNhd isOpen_upper
  have hconn : IsPreconnected PhysicalPhaseHolomorphic.upper := by
    have : Convex ℝ PhysicalPhaseHolomorphic.upper := (convex_Ioi (0 : ℝ)).linear_preimage Complex.imLm
    exact this.isPreconnected
  have heq : (fun z =>
      2 * Complex.cos (SpatialTransfer.boundaryPhase L κ (PhysicalQuantumMeasure.measure hκ u) z))
      =ᶠ[𝓝 z₀] L2SpatialTransfer.discriminant κ u := by
    have h₁ : {w : ℂ | 4 * (κ * ‖u‖ ^ 2) < w.im} ∈ 𝓝 z₀ :=
      (isOpen_lt continuous_const Complex.continuous_im).mem_nhds (by simpa [z₀] using hy₁)
    have h₂ : {w : ℂ | Real.log 16 < L * w.im} ∈ 𝓝 z₀ :=
      (isOpen_lt continuous_const (continuous_const.mul Complex.continuous_im)).mem_nhds
        (by simpa [z₀] using hy₂)
    filter_upwards [h₁, h₂] with w hw₁ hw₂
    exact PhysicalTraceSymbolDependency.high_cosine hκ hu htrace ⟨hw₁.le, hw₂.le⟩
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hconn hz₀ heq hz

/-- Actual canonical atomlessness now needs only the named high identity. -/
theorem canonical_atomless (hκ : 0 < κ) {u : PhysicalTensor.L2T L} (hu : u ≠ 0)
    (htrace : PhysicalTraceSymbolDependency.TraceSymbolIdentity L κ u) :
    NullSingletonClass (PhysicalQuantumMeasure.measure hκ u) :=
  PhysicalPhaseAtomlessness.canonical_atomless_of_upper_cosine hκ u
    (fun _ hz => upper_cosine hκ hu htrace hz)

end QuantumNLS.PhysicalUpperTraceIdentity

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.PhysicalUpperTraceIdentity.entire_transfer
#print axioms QuantumNLS.PhysicalUpperTraceIdentity.entire_discriminant
#print axioms QuantumNLS.PhysicalUpperTraceIdentity.finite_band_edges
#print axioms QuantumNLS.PhysicalUpperTraceIdentity.upper_cosine
#print axioms QuantumNLS.PhysicalUpperTraceIdentity.canonical_atomless

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.PhysicalUpperTraceIdentity." then
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
