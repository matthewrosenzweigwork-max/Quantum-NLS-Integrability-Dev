import QuantumNLS.RootMassInvolutionR8

/-! R-620D5517: simultaneous fixed full-space Cauchy periods and their
full differentials. Identification with the local inverse/logarithm in
the leading quantum period is a separate, unproved clause. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter Topology MeasureTheory Complex
namespace QuantumNLS.RootScalarPeriodR8
open PhysicalTensor (L2T)
open RootMassInvolutionR8
variable {L κ : ℝ} [Fact (0 < L)]

abbrev cut (hκ : 0 < κ) (u : L2T L) (n : ℤ) : ℝ :=
  DEF014Phase.separator (⟨κ,hκ⟩,u) n

def center (hκ : 0 < κ) (u : L2T L) (n : ℤ) : ℝ :=
  (cut hκ u (n-1) + cut hκ u n)/2

def radius (hκ : 0 < κ) (u : L2T L) (n : ℤ) : ℝ :=
  (cut hκ u n - cut hκ u (n-1))/2

/-- The literal fixed Cauchy period; no local logarithmic inverse is
assumed or defined by its desired conclusion. -/
def cauchyPeriod (hκ : 0 < κ) (base : L2T L) (n : ℤ) (v : L2T L) : ℂ :=
  (2 * (Real.pi : ℂ) * I)⁻¹ *
    (∮ z in C((center hκ base n : ℂ), radius hκ base n),
      EmpiricalRapidity.cauchyTransform (PhysicalQuantumMeasure.measure hκ v) z)

theorem eventually_mass_eq_cauchyPeriod (hκ : 0 < κ) (u : L2T L) (n : ℤ) :
    ∀ᶠ v : L2T L in 𝓝 u, (mass hκ n v : ℂ) = cauchyPeriod hκ u n v := by
  have hj : Continuous (fun v : L2T L => ((⟨κ,hκ⟩,v) : DEF014Phase.Param L)) :=
    continuous_const.prodMk continuous_id
  exact hj.continuousAt.eventually (DEF014Contour.eventually_physical_mass_contour
    ((⟨κ,hκ⟩,u) : DEF014Phase.Param L) n)

/-- One full open neighborhood works for every selected label. At every
point of this neighborhood the identity identifies the full Hilbert
differential and its application to every Hilbert tangent vector. -/
theorem finite_fixed_cauchy_periods (hκ : 0 < κ) (u : L2T L) (F : Finset ℤ) :
    ∃ U : Set (L2T L), IsOpen U ∧ u ∈ U ∧
      ∀ n ∈ F, 0 < radius hκ u n ∧
        (∀ v ∈ U, (mass hκ n v : ℂ) = cauchyPeriod hκ u n v) ∧
        (∀ v ∈ U, AnalyticAt ℝ (cauchyPeriod hκ u n) v) ∧
        (∀ v ∈ U, fderiv ℝ (fun w => (mass hκ n w : ℂ)) v =
          fderiv ℝ (cauchyPeriod hκ u n) v) ∧
        (∀ v ∈ U, ∀ h : L2T L,
          fderiv ℝ (fun w => (mass hκ n w : ℂ)) v h =
            fderiv ℝ (cauchyPeriod hκ u n) v h) := by
  have he : ∀ᶠ v : L2T L in 𝓝 u,
      ∀ n ∈ F, (mass hκ n v : ℂ) = cauchyPeriod hκ u n v := by
    rw [Filter.eventually_all_finset]
    intro n hn
    exact eventually_mass_eq_cauchyPeriod hκ u n
  obtain ⟨U,hsub,hU,hu⟩ := mem_nhds_iff.mp he
  refine ⟨U,hU,hu,?_⟩
  intro n hn
  have hrad : 0 < radius hκ u n := by
    have h := (DEF014Phase.facts ((⟨κ,hκ⟩,u) : DEF014Phase.Param L)).phase.separator_strictMono
      (show n-1 < n by omega)
    change 0 < (cut hκ u n-cut hκ u (n-1))/2
    change cut hκ u (n-1) < cut hκ u n at h
    linarith
  have hd : ∀ v ∈ U, fderiv ℝ (fun w => (mass hκ n w : ℂ)) v =
      fderiv ℝ (cauchyPeriod hκ u n) v := by
    intro v hv
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [hU.mem_nhds hv] with w hw
    exact hsub hw n hn
  have ha : ∀ v ∈ U, AnalyticAt ℝ (cauchyPeriod hκ u n) v := by
    intro v hv
    have hm := (Complex.ofRealCLM.analyticAt (mass hκ n v)).comp
      (DEF014MassAnalytic.analyticAt_physical_coordinate hκ n v)
    apply hm.congr
    filter_upwards [hU.mem_nhds hv] with w hw
    exact hsub hw n hn
  exact ⟨hrad,fun v hv => hsub hv n hn,ha,hd,
    fun v hv h => DFunLike.congr_fun (hd v hv) h⟩
end QuantumNLS.RootScalarPeriodR8
#print axioms QuantumNLS.RootScalarPeriodR8.finite_fixed_cauchy_periods

#check @QuantumNLS.RootScalarPeriodR8.finite_fixed_cauchy_periods

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.RootScalarPeriodR8." ||
        n.toString.startsWith "_private.QuantumNLS.RootScalarPeriodR8." then
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
  Lean.logInfo m!"RootScalarPeriodR8 audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
