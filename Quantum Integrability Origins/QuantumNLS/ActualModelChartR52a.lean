import QuantumNLS.Def044ChartR51a
import QuantumNLS.Reg015HFinal
import QuantumNLS.RootScalarUniquenessR28
import QuantumNLS.Round10ScalarReconstructionBatch

/-! R-E679E41D: actual global chart, all real nonnegative Sobolev
restrictions, measure/transfer determination, and full Hilbert logarithmic
periods. No pending hierarchy or window module is imported. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open MeasureTheory Filter Topology Set
namespace QuantumNLS.ActualModelChartR52a
open PhysicalTensor QuantumFourierSpecification Def044ChartR51a Reg015Setting
variable {L κ : ℝ} [Fact (0 < L)]

def baseHomeo (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ) : L2T L ≃ₜ Seq where
  toFun := C.Φ
  invFun := C.Ψ
  left_inv := C.left_inverse
  right_inv := C.right_inverse
  continuous_toFun := continuous_iff_continuousAt.mpr fun u => (C.analytic u).continuousAt
  continuous_invFun := continuous_iff_continuousAt.mpr fun z => (C.inverse_analytic z).continuousAt

def targetUniv (s : ℝ) (hs : 0 ≤ s) : Sobolev.h02 L s ≃ₜ Target (L := L) univ s hs where
  toFun z := ⟨z,mem_univ _⟩
  invFun z := z.val
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_id.subtype_mk _
  continuous_invFun := continuous_subtype_val

/-- The authorized REG015_final is APPLIED, not assumed. The restriction
uses exactly the same global map and genuine inverse. -/
theorem sobolev_restrictions (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ) :
    SobolevRestrictions hκ C := by
  intro s hs
  let e : L2T L ≃ₜ (univ : Set Seq) :=
    (baseHomeo hκ C).trans (Homeomorph.Set.univ Seq).symm
  obtain ⟨F,hF⟩ := (Reg015HFinal.REG015_final hκ s hs).2.2 univ e C.actions
  let G : Sobolev.H02 L s ≃ₜ Sobolev.h02 L s := F.trans (targetUniv s hs).symm
  have hc : ∀ u, toBase s hs (G u) = C.Φ u.val := by
    intro u
    apply lp.ext
    funext n
    rw [toBase_apply]
    exact hF u n
  refine ⟨G,hc,?_⟩
  intro z
  have h := congrArg C.Ψ (hc (G.symm z))
  rw [G.apply_symm_apply,C.left_inverse] at h
  exact h.symm

/-- All indexed actions determine the full physical measure and transfer,
with no positivity requirement on individual actions. -/
theorem action_determination (hκ : 0 < κ) : ActionDetermination (L := L) hκ := by
  intro u v he
  have hm := (RootScalarUniquenessR28.root_scalar_uniqueness hκ).1 u v he
  have hdisc : L2SpatialTransfer.discriminant κ u = L2SpatialTransfer.discriminant κ v := by
    have hU := (PhysicalUpperTraceIdentity.entire_discriminant κ u).differentiableOn.analyticOnNhd isOpen_univ
    have hV := (PhysicalUpperTraceIdentity.entire_discriminant κ v).differentiableOn.analyticOnNhd isOpen_univ
    apply hU.eq_of_eventuallyEq hV (z₀ := Complex.I)
    filter_upwards [PhysicalPhaseHolomorphic.isOpen_upper.mem_nhds
      (show Complex.I ∈ PhysicalPhaseHolomorphic.upper by simp [PhysicalPhaseHolomorphic.upper])]
      with z hz
    rw [← PhysicalUnconditionalTrace.upper_cosine hκ u hz,
      ← PhysicalUnconditionalTrace.upper_cosine hκ v hz,hm]
  refine ⟨?_,hm⟩
  funext z
  apply mul_left_cancel₀ (Complex.exp_ne_zero (-(Complex.I*z*L/2)))
  rw [RootTraceSymbolFinal.traceSymbol_all hκ.le u z,
    RootTraceSymbolFinal.traceSymbol_all hκ.le v z,hdisc]

/-- The literal accepted logarithmic period, with its contour frozen at the
base input and its exact coefficient, on full open Hilbert neighborhoods.
This includes collapsed gaps, vacuum and every real radial direction. -/
theorem logarithmic_periods (hκ : 0 < κ) (u : L2T L) (F : Finset ℤ) :
    ∃ U : Set (L2T L), IsOpen U ∧ u ∈ U ∧ ∀ n ∈ F,
      0 < RootScalarPeriodR8.radius hκ u n ∧
      (∀ v ∈ U, ∀ z ∈ Metric.sphere (RootScalarPeriodR8.center hκ u n : ℂ)
        (RootScalarPeriodR8.radius hκ u n),
        RootScalarPeriodR10.lambda hκ u z (NormalizedTransfer.productSymbol L κ v z) =
          Complex.I*κ*EmpiricalRapidity.cauchyTransform (PhysicalQuantumMeasure.measure hκ v) z) ∧
      (∀ v ∈ U, leadingPeriod hκ u n (RootScalarPeriodR10.lambda hκ u) v = action hκ v n) ∧
      (∀ v ∈ U, AnalyticAt ℝ (leadingPeriod hκ u n (RootScalarPeriodR10.lambda hκ u)) v) ∧
      (∀ v ∈ U, fderiv ℝ (leadingPeriod hκ u n (RootScalarPeriodR10.lambda hκ u)) v =
        fderiv ℝ (fun w => action hκ w n) v) ∧
      (∀ v ∈ U, ∀ h : L2T L,
        fderiv ℝ (leadingPeriod hκ u n (RootScalarPeriodR10.lambda hκ u)) v h =
          fderiv ℝ (fun w => action hκ w n) v h) := by
  have hp (n : ℤ) : leadingPeriod hκ u n (RootScalarPeriodR10.lambda hκ u) =
      RootScalarPeriodR10.leadingPeriod hκ u n := by
    funext v
    simp only [leadingPeriod,RootScalarPeriodR10.leadingPeriod,one_div,RootScalarPeriodR10.symbol]
  have hm (n : ℤ) : (fun w : L2T L => action hκ w n) = RootMassInvolutionR8.mass hκ n := rfl
  obtain ⟨U,hU,hu,hper⟩ := RootScalarPeriodR10.audit_scalar_period hκ u F
  refine ⟨U,hU,hu,fun n hn => ?_⟩
  simpa only [← hp n,← hm n,RootScalarPeriodR10.symbol,RootScalarPeriodR10.exponent,
    RootCauchyFullBracketR8.G,Def044ChartR51a.action,RootMassInvolutionR8.mass] using hper n hn

/-- Both normalizations use exactly the actual global chart. -/
theorem actions (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ) (v : L2T L) (n : ℤ) :
    action hκ v n = ‖C.Φ v n‖^2 ∧
    action hκ v n = ‖reflected (C.Φ v) (-n)‖^2/2 :=
  ⟨(C.actions v n).symm,(C.actions v n).symm.trans (reflected_action _ _).symm⟩

end QuantumNLS.ActualModelChartR52a
#print axioms QuantumNLS.ActualModelChartR52a.sobolev_restrictions
#print axioms QuantumNLS.ActualModelChartR52a.action_determination
#print axioms QuantumNLS.ActualModelChartR52a.logarithmic_periods
#print axioms QuantumNLS.ActualModelChartR52a.actions

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.ActualModelChartR52a." ||
        n.toString.startsWith "_private.QuantumNLS.ActualModelChartR52a." then
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
