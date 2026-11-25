import QuantumNLS.DEF014DiscriminantAnalytic
import QuantumNLS.DEF014Crossings
import QuantumNLS.Ext025AAnalysis

/-! Pointwise physical Cauchy-phase analyticity in the field. The branch is
identified by the actual weak measure continuity, rather than postulated. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Set Filter Topology MeasureTheory
open scoped BoundedContinuousFunction
namespace QuantumNLS.DEF014PhaseAnalytic
open PhysicalTensor (L2T)
variable {L κ : ℝ} [Fact (0 < L)] (hκ : 0 < κ)

def selected (u : L2T L) (z : ℂ) : ℂ :=
  SpatialTransfer.boundaryPhase L κ (PhysicalQuantumMeasure.measure hκ u) z

/-- Weak continuity suffices for the actual Cauchy values away from the real axis. -/
theorem continuous_selected {z : ℂ} (hz : z.im ≠ 0) :
    Continuous (fun u : L2T L => selected hκ u z) := by
  have hm : Continuous (fun u : L2T L => FullMass.Mfin κ u) :=
    FullMassLimit.continuous_Mfin.comp
      ((continuous_const (y := (⟨κ,hκ.le⟩ : {k : ℝ // 0 ≤ k}))).prodMk continuous_id)
  let k : ℝ →ᵇ ℂ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun t : ℝ => (z - (t : ℂ))⁻¹)
    (EmpiricalRapidity.continuous_cauchyIntegrand z hz) |z.im|⁻¹
    (EmpiricalRapidity.norm_cauchyIntegrand_le z hz)
  have hi : Continuous (fun u : L2T L => ∫ t, k t ∂(FullMass.Mfin κ u : Measure ℝ)) := by
    rw [continuous_iff_continuousAt]
    intro u
    exact (FiniteMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp (hm.tendsto u) k
  have he (u : L2T L) : (FullMass.Mfin κ u : Measure ℝ) = PhysicalQuantumMeasure.measure hκ u :=
    (PhysicalL2Normalization.measure_eq_Mmeas hκ u).symm
  simp_rw [he] at hi
  exact continuous_const.sub (continuous_const.mul hi)

/-- A continuous selected solution of the cosine equation inherits an analytic
germ from its analytic right-hand side, provided the scalar sine is nonzero. -/
theorem analytic_selected_cosine {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g F : E → ℂ} {u : E} (hF : AnalyticAt ℝ F u)
    (hg : ContinuousAt g u) (he : ∀ᶠ v in 𝓝 u, 2 * Complex.cos (g v) = F v)
    (hs : Complex.sin (g u) ≠ 0) : AnalyticAt ℝ g u := by
  let f : ℂ → ℂ := fun w => 2 * Complex.cos w
  let d : ℂ := -2 * Complex.sin (g u)
  have hd : d ≠ 0 := mul_ne_zero (by norm_num) hs
  let I : ℂ ≃L[ℂ] ℂ := ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 d hd)
  have ha : AnalyticAt ℂ f (g u) := analyticAt_const.mul Complex.analyticAt_cos
  have hder : HasFDerivAt f I.toContinuousLinearMap (g u) := by
    have h := ((Complex.hasDerivAt_cos (g u)).const_mul (2 : ℂ)).hasFDerivAt
    convert h using 1
    apply ContinuousLinearMap.ext
    intro x
    change x * d = x • (2 * -Complex.sin (g u))
    dsimp [d]
    ring
  obtain ⟨inv,hinv,_,hleft,_⟩ := Ext025A.gp03_analytic_inverse I ha hder
  have hFu : F u = f (g u) := (Filter.Eventually.self_of_nhds he).symm
  have hcomp : AnalyticAt ℝ (fun v => inv (F v)) u := by
    rw [← hFu] at hinv
    exact hinv.restrictScalars.comp hF
  apply hcomp.congr
  filter_upwards [he, hg.tendsto.eventually hleft] with v hv hl
  rw [← hv]
  exact hl

/-- Pointwise real analyticity of the quantum-selected phase in the entire
open upper half-plane, including at zero and collapsed masses. -/
theorem analyticAt_selected_upper (u : L2T L) {z : ℂ} (hz : 0 < z.im) :
    AnalyticAt ℝ (fun v : L2T L => selected hκ v z) u := by
  have hF := DEF014DiscriminantAnalytic.analyticAt_discriminant κ z u
  have hs : Complex.sin (selected hκ u z) ≠ 0 := by
    intro hzero
    have hp := PhysicalQuantumMeasure.im_phase_pos hκ u hz
    obtain ⟨k,hk⟩ := Complex.sin_eq_zero_iff.mp hzero
    have hh := congrArg Complex.im hk
    simp at hh
    change 0 < (selected hκ u z).im at hp
    linarith
  exact analytic_selected_cosine hF (continuous_selected hκ hz.ne').continuousAt
    (Filter.Eventually.of_forall fun v => PhysicalUnconditionalTrace.upper_cosine hκ v hz) hs

/-- Actual Cauchy transform, at each fixed upper-half-plane point. This is
pointwise field analyticity; uniform contour analyticity is a further step. -/
theorem analyticAt_cauchy_upper (u : L2T L) {z : ℂ} (hz : 0 < z.im) :
    AnalyticAt ℝ (fun v : L2T L =>
      EmpiricalRapidity.cauchyTransform (PhysicalQuantumMeasure.measure hκ v) z) u := by
  have h := ((analyticAt_const (v := (L : ℂ) * z / 2)).sub
    (analyticAt_selected_upper hκ u hz)).div
    (analyticAt_const (v := (κ : ℂ))) (Complex.ofReal_ne_zero.mpr hκ.ne')
  convert h using 1
  funext v
  dsimp [selected, SpatialTransfer.boundaryPhase]
  field_simp [Complex.ofReal_ne_zero.mpr hκ.ne']
  ring

/-- Pointwise real analyticity of the actual selected boundary phase at a
fixed real band point. Common bands and selected-phase continuity identify
the same analytic cosine branch for every nearby physical input. -/
theorem analyticAt_boundary_band (u : L2T L) (x : ℝ)
    (hx : |(L2SpatialTransfer.discriminant κ u (x : ℂ)).re| < 2) :
    AnalyticAt ℝ (fun v : L2T L => DEF014Phase.phase (⟨κ,hκ⟩,v) x) u := by
  let j : L2T L → DEF014Phase.Param L := fun v => (⟨κ,hκ⟩,v)
  have hj : Continuous j := continuous_const.prodMk continuous_id
  let g : L2T L → ℂ := fun v => (DEF014Phase.phase (j v) x : ℂ)
  have hg : ContinuousAt g u := Complex.continuous_ofReal.continuousAt.comp
    ((DEF014Phase.continuous_phase_at_band (j u) hx).comp hj.continuousAt)
  obtain ⟨δ,hδ,hband⟩ := DEF014Phase.common_band (j u) hx
  have hb : ∀ᶠ v : L2T L in 𝓝 u,
      |(L2SpatialTransfer.discriminant κ v (x : ℂ)).re| < 2 := by
    filter_upwards [hj.continuousAt.tendsto.eventually hband] with v hv
    exact hv x (by simpa using hδ)
  have he : ∀ᶠ v : L2T L in 𝓝 u,
      2 * Complex.cos (g v) = L2SpatialTransfer.discriminant κ v (x : ℂ) := by
    filter_upwards [hb] with v hv
    have hr := DEF014Crossings.real_trace_eq_cos (j v) hv
    apply Complex.ext
    · simpa [g, j, Complex.mul_re, Complex.cos_ofReal_re] using hr.symm
    · simp [g, Complex.mul_im, L2DiscriminantRegularity.discriminant_real]
  have hs : Complex.sin (g u) ≠ 0 := by
    intro hz
    have he0 := Filter.Eventually.self_of_nhds he
    rcases Complex.sin_eq_zero_iff_cos_eq.mp hz with hcos | hcos
    all_goals
      rw [hcos] at he0
      have hr := congrArg Complex.re he0
      norm_num at hr
      rw [← hr] at hx
      norm_num at hx
  have ha := analytic_selected_cosine
    (DEF014DiscriminantAnalytic.analyticAt_discriminant κ (x : ℂ) u) hg he hs
  have hh : AnalyticAt ℝ (fun v => (g v).re) u :=
    (Complex.reCLM.analyticAt (g u)).comp (f := g) ha
  simpa only [g, Complex.ofReal_re] using hh

end QuantumNLS.DEF014PhaseAnalytic

-- ROUND 4 AUTHOR AUDIT
#print axioms QuantumNLS.DEF014PhaseAnalytic.analyticAt_boundary_band
#print axioms QuantumNLS.DEF014PhaseAnalytic.continuous_selected
#print axioms QuantumNLS.DEF014PhaseAnalytic.analytic_selected_cosine
#print axioms QuantumNLS.DEF014PhaseAnalytic.analyticAt_selected_upper
#print axioms QuantumNLS.DEF014PhaseAnalytic.analyticAt_cauchy_upper

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.DEF014PhaseAnalytic." then
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
  Lean.logInfo m!"DEF014PhaseAnalytic audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
