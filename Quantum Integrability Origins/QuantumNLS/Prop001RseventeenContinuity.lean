import QuantumNLS.Prop001RseventeenDuhamel

/-! Trace continuity and scalar measurability of the actual hierarchy errors. -/
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
open Filter Topology MeasureTheory
open scoped InnerProductSpace BigOperators ENNReal
namespace QuantumNLS.Prop001RseventeenContinuity
open TraceClass TraceIdeal TensorCarrier PhysicalTensor Prop001 Prop001RthirteenSeries
  Prop001RfifteenDerivative Prop001RthirteenDerivative Prop001RseventeenDuhamel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Subtraction preserves convergence in the constructed trace norm. -/
theorem trace_tendsto_sub {ι : Type*} {l : Filter ι}
    (F G : ι → E →L[ℂ] E) (A B : E →L[ℂ] E)
    (hF : Tendsto (fun i => traceNorm (F i-A)) l (𝓝 0))
    (hG : Tendsto (fun i => traceNorm (G i-B)) l (𝓝 0)) :
    Tendsto (fun i => traceNorm ((F i-G i)-(A-B))) l (𝓝 0) := by
  have hh : Tendsto (fun i => traceNorm (F i-A)+traceNorm (G i-B)) l (𝓝 0) := by
    simpa only [add_zero] using hF.add hG
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hh (fun _ => bot_le)
  intro i
  have he : (F i-G i)-(A-B) = (F i-A)+-(G i-B) := by abel
  dsimp only
  rw [he]
  simpa only [TraceNormTopology.traceNorm_neg] using traceNorm_add_le (F i-A) (-(G i-B))

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Actual finite marginals are continuous for the trace metric. -/
theorem extendedMarginal_trace_continuous (D : ClassicalData H) (N j : ℕ)
    (ψ : SymSector ℂ H N) (t : ℝ) :
    Tendsto (fun s => traceNorm
      (extendedMarginal D.A N j s ψ-extendedMarginal D.A N j t ψ)) (𝓝 t) (𝓝 0) := by
  by_cases hj : j ≤ N
  · have hc : ContinuousAt (fun s => quantumVector D.A N ψ s) t :=
      (quantumVector_derivative D.A N ψ t).continuousAt
    have hd1 : Tendsto (fun s => ‖quantumVector D.A N ψ s-quantumVector D.A N ψ t‖)
        (𝓝 t) (𝓝 0) := by
      simpa only [sub_self,norm_zero] using
        (hc.tendsto.sub (tendsto_const_nhds (x := quantumVector D.A N ψ t))).norm
    have hd2 := hc.tendsto.norm.add
      (tendsto_const_nhds (f := 𝓝 t) (x := ‖quantumVector D.A N ψ t‖))
    have hd : Tendsto (fun s => ‖quantumVector D.A N ψ s-quantumVector D.A N ψ t‖*
        (‖quantumVector D.A N ψ s‖+‖quantumVector D.A N ψ t‖)) (𝓝 t) (𝓝 0) := by
      simpa only [zero_mul] using hd1.mul hd2
    have he : Tendsto (fun s => ENNReal.ofReal
        (‖quantumVector D.A N ψ s-quantumVector D.A N ψ t‖*
          (‖quantumVector D.A N ψ s‖+‖quantumVector D.A N ψ t‖))) (𝓝 t) (𝓝 (0 : ℝ≥0∞)) := by
      simpa only [Function.comp_def,ENNReal.ofReal_zero] using
        ENNReal.continuous_ofReal.continuousAt.tendsto.comp hd
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds he (fun _ => bot_le)
    intro s
    simp only [extendedMarginal_of_le D.A N j hj,marginal]
    exact MarginalPureState.traceNorm_reducedDensityN_sub_le N j hj
      (quantumVector D.A N ψ s) (quantumVector D.A N ψ t)
  · simp only [extendedMarginal,dite_eq_right hj,sub_self,Fidelity.traceNorm_zero]
    exact tendsto_const_nhds

/-- The actual product hierarchy is continuous for the same trace metric. -/
theorem coherent_trace_continuous (D : ClassicalData H) (u : Sphere H) (j : ℕ) (t : ℝ) :
    Tendsto (fun s => traceNorm (coherentProjector j (trajectory D u s)-
      coherentProjector j (trajectory D u t))) (𝓝 t) (𝓝 0) := by
  have hc := (trajectory_tensor_derivative D u j t).continuousAt.tendsto
  exact rankOne_trace_tendsto _ _ _ _ hc hc

/-- Literal scalar error used in the source Duhamel argument. -/
def error (D : ClassicalData H) (N : ℕ) (ψ : SymSector ℂ H N) (u : Sphere H)
    (j : ℕ) (t : ℝ) : ℝ :=
  (traceNorm (extendedMarginal D.A N j t ψ-coherentProjector j (trajectory D u t))).toReal

theorem error_nonneg (D : ClassicalData H) (N : ℕ) (ψ : SymSector ℂ H N)
    (u : Sphere H) (j : ℕ) (t : ℝ) : 0 ≤ error D N ψ u j t := ENNReal.toReal_nonneg

theorem error_le_two (D : ClassicalData H) (N : ℕ) (ψ : SymSector ℂ H N)
    (hψ : ‖ψ‖=1) (u : Sphere H) (j : ℕ) (t : ℝ) : error D N ψ u j t ≤ 2 := by
  have hh := extendedMarginal_error_le_two D.A D.selfAdjoint N j t ψ hψ
    (trajectory D u t) ((trajectory_spec D u).2.2.1 t).1
  have hr := ENNReal.toReal_mono (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hh
  simpa only [error,ENNReal.toReal_ofNat] using hr


theorem error_continuous (D : ClassicalData H) (N : ℕ) (ψ : SymSector ℂ H N)
    (hψ : ‖ψ‖=1) (u : Sphere H) (j : ℕ) : Continuous (error D N ψ u j) := by
  let F : ℝ → TraceNormTopology.Op (HilbertTensorPower ℂ H j) :=
    fun t => ⟨extendedMarginal D.A N j t ψ-coherentProjector j (trajectory D u t)⟩
  have hc : Continuous F := continuous_iff_continuousAt.mpr (fun t =>
    tendsto_iff_edist_tendsto_0.mpr (trace_tendsto_sub _ _ _ _
      (extendedMarginal_trace_continuous D N j ψ t) (coherent_trace_continuous D u j t)))
  have ht := TraceNormTopology.continuous_traceNorm.comp hc
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (ENNReal.continuousAt_toReal (ne_top_of_le_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    (extendedMarginal_error_le_two D.A D.selfAdjoint N j t ψ hψ
      (trajectory D u t) ((trajectory_spec D u).2.2.1 t).1))).comp (f := fun s : ℝ => traceNorm ((F s).val)) ht.continuousAt

/-- Hence the actual scalar errors are measurable and interval integrable. -/
theorem error_integrable (D : ClassicalData H) (N : ℕ) (ψ : SymSector ℂ H N)
    (hψ : ‖ψ‖=1) (u : Sphere H) (j : ℕ) (a b : ℝ) :
    IntervalIntegrable (error D N ψ u j) volume a b :=
  (error_continuous D N ψ hψ u j).intervalIntegrable a b

end QuantumNLS.Prop001RseventeenContinuity

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop001RseventeenContinuity" then
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
  Lean.logInfo m!"Prop001RseventeenContinuity audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."





#print axioms QuantumNLS.Prop001RseventeenContinuity.trace_tendsto_sub
#print axioms QuantumNLS.Prop001RseventeenContinuity.extendedMarginal_trace_continuous
#print axioms QuantumNLS.Prop001RseventeenContinuity.coherent_trace_continuous
#print axioms QuantumNLS.Prop001RseventeenContinuity.error
#print axioms QuantumNLS.Prop001RseventeenContinuity.error_nonneg
#print axioms QuantumNLS.Prop001RseventeenContinuity.error_le_two
#print axioms QuantumNLS.Prop001RseventeenContinuity.error_continuous
#print axioms QuantumNLS.Prop001RseventeenContinuity.error_integrable
