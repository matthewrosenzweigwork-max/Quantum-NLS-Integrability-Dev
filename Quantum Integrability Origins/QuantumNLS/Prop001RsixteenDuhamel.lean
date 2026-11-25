import QuantumNLS.Prop001RsixteenHierarchy
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Local trace-norm calculus for the actual hierarchy iteration.
Only finite dual tests are exchanged with integrals here; the later infinite
rank/time exchange is not supplied or assumed. -/
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 700000
open Filter Topology MeasureTheory
open scoped InnerProductSpace BigOperators ENNReal
namespace QuantumNLS.Prop001RsixteenDuhamel
open TraceClass TraceIdeal TensorCarrier Ext025A12Trace Prop001
  Prop001RfifteenRemainder Prop001RthirteenSeries Prop001RsixteenHierarchy
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
local instance : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
local instance : NormedSpace ℝ (E →L[ℂ] E) := NormedSpace.restrictScalars ℝ ℂ (E →L[ℂ] E)

/-- The constructed trace-norm derivative is also the actual bounded-operator
Bochner derivative, with no derivative conclusion supplied as a premise. -/
theorem hasDerivAt_of_trace_derivative (F : ℝ → E →L[ℂ] E) (V : E →L[ℂ] E) (t : ℝ)
    (h : Tendsto (fun s => traceNorm (slope F t s-V)) (𝓝[≠] t) (𝓝 0)) :
    HasDerivAt F V t := by
  apply hasDerivAt_iff_tendsto_slope.mpr
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hh : Tendsto (fun s => ENNReal.ofReal ‖slope F t s-V‖) (𝓝[≠] t) (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => bot_le)
      (fun s => norm_le_traceNorm _)
  have hr := (ENNReal.tendsto_toReal (show (0 : ℝ≥0∞) ≠ ⊤ by simp)).comp hh
  simpa only [Function.comp_def,ENNReal.toReal_ofReal (norm_nonneg _),ENNReal.toReal_zero] using hr

/-- Trace norm of the actual operator-valued Bochner integral. The proof
uses the repository's finite dual tests, without a trace-norm Banach-space
replacement or any infinite rank/time exchange. -/
theorem traceNorm_integral_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (F : Ω → E →L[ℂ] E) (b : Ω → ℝ) (hF : Integrable F μ) (hb : Integrable b μ)
    (h0 : ∀ᵐ x ∂μ,0 ≤ b x)
    (hbound : ∀ᵐ x ∂μ,traceNorm (F x) ≤ ENNReal.ofReal (b x)) :
    traceNorm (∫ x,F x ∂μ) ≤ ENNReal.ofReal (∫ x,b x ∂μ) := by
  classical
  let c := refBasis E
  apply traceNorm_le_of_forall c
  intro X hX s
  let L : (E →L[ℂ] E) →L[ℂ] ℂ :=
    ∑ j ∈ s,(innerSL ℂ (X (c j))).comp (ContinuousLinearMap.apply ℂ E (c j))
  have hLval (T : E →L[ℂ] E) : L T = ∑ j ∈ s,⟪X (c j),T (c j)⟫_ℂ := by
    simp [L]
  have hL : Integrable (fun x => L (F x)) μ := L.integrable_comp hF
  have hLI := L.integral_comp_comm hF
  rw [← hLval,← hLI,← integral_re hL]
  apply integral_mono_ae ((RCLike.reCLM : ℂ →L[ℝ] ℝ).integrable_comp hL) hb
  filter_upwards [h0,hbound] with x hx0 hx
  rw [hLval]
  exact (Complex.re_le_norm _).trans
    ((norm_sum_inner_le_traceNorm c (F x) X hX
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hx) s).trans
        (ENNReal.toReal_le_of_le_ofReal hx0 hx))

/-- The finite trace-norm fundamental theorem estimate. Its hypotheses
are ordinary local calculus and pointwise norm data on a generic curve;
it is not a hypothesis or a substitute for the PROP-001 iteration. -/
theorem traceNorm_FTC_bound (F V : ℝ → E →L[ℂ] E) (b : ℝ → ℝ) {a d : ℝ} (had : a ≤ d)
    (hderiv : ∀ t ∈ Set.uIcc a d,HasDerivAt F (V t) t)
    (hV : IntervalIntegrable V volume a d) (hb : IntervalIntegrable b volume a d)
    (h0 : ∀ t ∈ Set.Ioc a d,0 ≤ b t)
    (hbound : ∀ t ∈ Set.Ioc a d,traceNorm (V t) ≤ ENNReal.ofReal (b t)) :
    traceNorm (F d-F a) ≤ ENNReal.ofReal (∫ t in a..d,b t) := by
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hV,
    intervalIntegral.integral_of_le had,intervalIntegral.integral_of_le had]
  apply traceNorm_integral_le (volume.restrict (Set.Ioc a d)) V b hV.1 hb.1
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact h0 t ht
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hbound t ht

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual finite marginals have the actual hierarchy right-hand side
as their bounded-operator derivative, ready for the ordinary FTC. -/
theorem finite_marginal_hasDerivAt (D : ClassicalData H) (k m : ℕ)
    (ψ : SymSector ℂ H ((k+1)+m)) (hψ : ‖ψ‖=1) (t : ℝ) :
    HasDerivAt (fun r => marginal D.A ((k+1)+m) (k+1) (by omega) r ψ)
      ((-Complex.I) • (collisionSeries D.A
        (fun j => extendedMarginal D.A ((k+1)+m) j t ψ)
        (extendedMarginal_isTraceClass D.A D.selfAdjoint ((k+1)+m) t ψ hψ) k+
        finiteCorrection D k m ψ hψ t)) t :=
  hasDerivAt_of_trace_derivative _ _ t (PROP001_finite_hierarchy D k m ψ hψ t).1

end QuantumNLS.Prop001RsixteenDuhamel

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop001RsixteenDuhamel" then
      pending := pending.push n
      roots := roots + 1
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
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"Prop001RsixteenDuhamel audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."



#print axioms QuantumNLS.Prop001RsixteenDuhamel.hasDerivAt_of_trace_derivative
#print axioms QuantumNLS.Prop001RsixteenDuhamel.traceNorm_integral_le
#print axioms QuantumNLS.Prop001RsixteenDuhamel.traceNorm_FTC_bound
#print axioms QuantumNLS.Prop001RsixteenDuhamel.finite_marginal_hasDerivAt
