import QuantumNLS.DEF014Phase

/-! The actual half-integer crossings are nondegenerate real zeros. This
supplies the scalar nondegeneracy needed for an analytic implicit argument;
field analyticity is a separate obligation and is not assumed here. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Set Filter Topology MeasureTheory
namespace QuantumNLS.DEF014Crossings
open DEF014Phase
variable {L : ℝ} [Fact (0 < L)]

theorem real_trace_eq_cos (p : Param L) {x : ℝ}
    (hx : |(L2SpatialTransfer.discriminant p.1.1 p.2 (x : ℂ)).re| < 2) :
    (L2SpatialTransfer.discriminant p.1.1 p.2 (x : ℂ)).re = 2 * Real.cos (phase p x) := by
  have hi : (PhysicalContinuousBoundary.boundary p.1.2 p.2 x).im = 0 := by
    rw [PhysicalContinuousBoundary.boundary_im, RootDensity.hfun,
      ite_eq_right (not_lt.mpr hx.le)]
  rw [← PhysicalContinuousBoundary.boundary_cosine p.1.2 p.2 x,
    BandPhaseBridge.real_cosine, hi, Real.cosh_zero, mul_one]
  rfl

/-- The literal real discriminant has a nonzero derivative at every selected
separator, for arbitrary L2 input and positive coupling. -/
theorem separator_simple (p : Param L) (n : ℤ) :
    HasDerivAt (fun x : ℝ => (L2SpatialTransfer.discriminant p.1.1 p.2 (x : ℂ)).re)
      (-2 * Real.sin (MonotoneIndexedMasses.level n) *
        deriv (phase p) (separator p n)) (separator p n) ∧
      deriv (fun x : ℝ => (L2SpatialTransfer.discriminant p.1.1 p.2 (x : ℂ)).re)
        (separator p n) ≠ 0 := by
  let b := separator p n
  have hx : |(L2SpatialTransfer.discriminant p.1.1 p.2 (b : ℂ)).re| < 2 :=
    (facts p).separator_in_band n
  have hp : 0 < deriv (phase p) b :=
    PhysicalContinuousBoundary.positive_band_derivative_all p.1.2 p.2 b hx
  have hd : HasDerivAt (phase p) (deriv (phase p) b) b :=
    (differentiableAt_of_deriv_ne_zero hp.ne').hasDerivAt
  have hcos := ((Real.hasDerivAt_cos (phase p b)).comp b hd).const_mul 2
  have hb : phase p b = MonotoneIndexedMasses.level n := (facts p).phase.separator_spec n
  have he : (fun x : ℝ => (L2SpatialTransfer.discriminant p.1.1 p.2 (x : ℂ)).re) =ᶠ[𝓝 b]
      (fun x => 2 * Real.cos (phase p x)) := by
    have hc : Continuous (fun x : ℝ =>
        |(L2SpatialTransfer.discriminant p.1.1 p.2 (x : ℂ)).re|) :=
      (Complex.continuous_re.comp ((L2DiscriminantRegularity.continuous_discriminant
        p.1.1 p.2).comp Complex.continuous_ofReal)).abs
    filter_upwards [hc.continuousAt.eventually (gt_mem_nhds hx)] with x hxx
    exact real_trace_eq_cos p hxx
  have hder : HasDerivAt (fun x : ℝ => (L2SpatialTransfer.discriminant p.1.1 p.2 (x : ℂ)).re)
      (-2 * Real.sin (MonotoneIndexedMasses.level n) * deriv (phase p) b) b := by
    convert hcos.congr_of_eventuallyEq he using 1
    rw [hb]
    ring
  refine ⟨hder, ?_⟩
  rw [hder.deriv]
  have hs : Real.sin (MonotoneIndexedMasses.level n) ≠ 0 := by
    intro hs
    have hi := Real.sin_sq_add_cos_sq (MonotoneIndexedMasses.level n)
    rw [BandPhaseBridge.cos_level, hs] at hi
    norm_num at hi
  exact mul_ne_zero (mul_ne_zero (by norm_num) hs) hp.ne'

end QuantumNLS.DEF014Crossings

#print axioms QuantumNLS.DEF014Crossings.real_trace_eq_cos
#print axioms QuantumNLS.DEF014Crossings.separator_simple

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.DEF014Crossings." then
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
  Lean.logInfo m!"DEF014Crossings audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
