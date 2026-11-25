import QuantumNLS.ActualModelPeriodGermR52a
import QuantumNLS.ActualModelScalarR52a

/-! R-E679E41D: realize the full-open-neighborhood logarithmic-period
requirement of R51a, with the actual constrained quadratic branch. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Set Filter Topology Complex MeasureTheory
namespace QuantumNLS.ActualModelPeriodsR52a
open PhysicalTensor RootScalarPeriodR10 ScalarLogBranchR10 ActualModelPeriodGermR52a
open Def044ChartR51a
variable {L κ : ℝ} [Fact (0 < L)]

def Good (hκ : 0 < κ) (u : L2T L) (p : ℂ × ℂ) : Prop :=
  AnalyticAt ℂ (germ hκ u) p ∧
  (exp (germ hκ u p)^2-p.2*exp (germ hκ u p)+exponential L p.1 = 0) ∧
  exp (germ hκ u p)-exponential L p.1/exp (germ hκ u p) ≠ 0

def branchDomain (hκ : 0 < κ) (u : L2T L) : Set (ℂ × ℂ) := interior {p | Good hκ u p}

lemma germ_at_transfer (hκ : 0 < κ) (u : L2T L) (z : ℂ)
    (hz : RootCauchyJointR9.Regular κ (u,z)) :
    germ hκ u (z,symbol κ u z) = exponent hκ u z := by
  change localLog (exponential L z) (exponent hκ u z) (symbol κ u z) = _
  rw [transfer_identity hκ u z hz,localLog,root_at,div_self (exp_ne_zero _),log_one,add_zero]

/-- The actual background graph lies in one open, constrained analytic
branch domain. Membership follows from analyticity and the explicit root
formula; no graph identity is assumed as a domain condition. -/
lemma background_mem (hκ : 0 < κ) (u : L2T L) (z : ℂ)
    (hz : RootCauchyJointR9.Regular κ (u,z)) :
    (z,symbol κ u z) ∈ branchDomain hκ u := by
  let p : ℂ × ℂ := (z,symbol κ u z)
  have hg := analytic_germ hκ u z hz
  have hb : AnalyticAt ℂ (fun q : ℂ × ℂ => exponent hκ u q.1) p :=
    AnalyticAt.comp (𝕜 := ℂ) (g := RootScalarPeriodR10.exponent hκ u)
      (f := fun q : ℂ × ℂ => q.1) (x := p) (analytic_exponent hκ u z hz) analyticAt_fst
  have he : AnalyticAt ℂ (fun q : ℂ × ℂ => exponential L q.1) p := by
    exact (((analyticAt_const (v := I)).mul analyticAt_fst).mul
      (analyticAt_const (v := (L : ℂ)))).cexp
  have hD := difference_ne hκ u z hz
  have hs : p.2 = transfer (exponential L p.1) (exponent hκ u p.1) := transfer_identity hκ u z hz
  have hr := continuousAt_root he.continuousAt hb.continuousAt continuousAt_snd hD hs
  have hratio := hr.div hb.continuousAt.cexp (exp_ne_zero _)
  have hr0 : root (exponential L p.1) (exponent hκ u p.1) p.2 /
      exp (exponent hκ u p.1) ≠ 0 := by rw [hs,root_at,div_self (exp_ne_zero _)]; exact one_ne_zero
  have hbD := hb.continuousAt.cexp.sub (he.continuousAt.div hb.continuousAt.cexp (exp_ne_zero _))
  have hgD := hg.continuousAt.cexp.sub (he.continuousAt.div hg.continuousAt.cexp (exp_ne_zero _))
  have hgD0 : exp (germ hκ u p)-exponential L p.1/exp (germ hκ u p) ≠ 0 := by
    rw [show germ hκ u p = exponent hκ u z from germ_at_transfer hκ u z hz]
    exact hD
  apply mem_interior_iff_mem_nhds.mpr
  filter_upwards [hg.eventually_analyticAt,hbD.eventually_ne hD,
    hratio.eventually_ne hr0,hgD.eventually_ne hgD0] with q hqa hqd hqr hqg
  exact ⟨hqa,germ_quadratic hκ u q hqd hqr,hqg⟩

lemma regular_not_support (hκ : 0 < κ) (u : L2T L) (z : ℂ)
    (hz : RootCauchyJointR9.Regular κ (u,z)) :
    z ∉ Complex.ofReal '' (PhysicalQuantumMeasure.measure hκ u).support := by
  rintro ⟨x,hx,rfl⟩
  by_cases hu : u = 0
  · simp [hu] at hx
  · have hb : |(L2SpatialTransfer.discriminant κ u (x : ℂ)).re| < 2 :=
      hz.resolve_left (by simp)
    exact Prop026Bound.cuts_sub hκ hu hb hx

/-- All strengthened branch constraints in R51a are discharged, with one
full open Hilbert neighborhood for each finite label packet. -/
theorem full_open_periods (hκ : 0 < κ) : FullOpenPeriods (L := L) hκ := by
  intro base F
  obtain ⟨U0,hU0,hbase0,hper⟩ := ActualModelChartR52a.logarithmic_periods hκ base F
  have hev : ∀ᶠ v : L2T L in 𝓝 base, ∀ n ∈ F,
      ∀ z ∈ Metric.sphere (RootScalarPeriodR8.center hκ base n : ℂ) (RootScalarPeriodR8.radius hκ base n),
        (z,NormalizedTransfer.productSymbol L κ v z) ∈ branchDomain hκ base ∧
          RootCauchyJointR9.Regular κ (v,z) := by
    rw [Filter.eventually_all_finset]
    intro n hn
    apply (isCompact_sphere (RootScalarPeriodR8.center hκ base n : ℂ)
      (RootScalarPeriodR8.radius hκ base n)).eventually_forall_of_forall_eventually
    intro z hz
    have hreg := circle_regular hκ base n hz
    have hg := (RootCauchyJointR9.continuousAt_joint_regular hκ (base,z) hreg).const_mul (I*(κ : ℂ))
    have he : ContinuousAt (fun p : L2T L × ℂ => exponential L p.2) (base,z) := by
      unfold exponential
      fun_prop
    have ht := hg.cexp.add (he.div hg.cexp (exp_ne_zero _))
    have hc := continuous_snd.continuousAt.prodMk ht
    have hmem : (z,transfer (exponential L z) (exponent hκ base z)) ∈ branchDomain hκ base := by
      rw [← transfer_identity hκ base z hreg]
      exact background_mem hκ base z hreg
    have hv := hc.eventually (isOpen_interior.mem_nhds hmem)
    filter_upwards [hv,(RootCauchyJointR9.isOpen_regular κ).mem_nhds hreg] with p hp hpr
    refine ⟨?_,hpr⟩
    change (p.2,RootScalarPeriodR10.symbol κ p.1 p.2) ∈ branchDomain hκ base
    rw [RootScalarPeriodR10.transfer_identity hκ p.1 p.2 hpr]
    exact hp
  have hUev : ∀ᶠ v : L2T L in 𝓝 base, v ∈ U0 := hU0.mem_nhds hbase0
  obtain ⟨U,hsub,hU,hbase⟩ := mem_nhds_iff.mp (hUev.and hev)
  refine ⟨U,hU,hbase,?_⟩
  intro n hn
  obtain ⟨hrad,hlog,hvalue,hana,hder,_⟩ := hper n hn
  refine ⟨lambda hκ base,hrad,?_,fun v hv => hlog v (hsub hv).1,
    fun v hv => hvalue v (hsub hv).1,fun v hv => hana v (hsub hv).1,
    fun v hv => hder v (hsub hv).1⟩
  refine ⟨branchDomain hκ base,isOpen_interior,fun p hp => ((interior_subset : interior {q : ℂ × ℂ | Good hκ base q} ⊆ {q | Good hκ base q}) hp).1,?_,?_⟩
  · intro v hv z hz
    obtain ⟨hp,hr⟩ := (hsub hv).2 n hn z hz
    exact ⟨hp,regular_not_support hκ v z hr⟩
  · intro p hp
    have hgood : Good hκ base p :=
      (interior_subset : interior {q : ℂ × ℂ | Good hκ base q} ⊆ {q | Good hκ base q}) hp
    have hg := hgood.2
    simpa only [germ,exponential,show I*p.1*(L : ℂ) = I*(L : ℂ)*p.1 by ring] using hg

end QuantumNLS.ActualModelPeriodsR52a
#print axioms QuantumNLS.ActualModelPeriodsR52a.background_mem
#print axioms QuantumNLS.ActualModelPeriodsR52a.regular_not_support
#print axioms QuantumNLS.ActualModelPeriodsR52a.full_open_periods

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.ActualModelPeriodsR52a." ||
        n.toString.startsWith "_private.QuantumNLS.ActualModelPeriodsR52a." then
      pending := pending.push n
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn "HeldGP14Tonelli").length > 1 then
        throwError "Rejected dependency: {n}"
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"Round52 aggregate audit PASS: {own} own constants; {seen.size} transitive constants; standard only."
