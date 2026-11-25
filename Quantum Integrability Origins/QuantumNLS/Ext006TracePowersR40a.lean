import QuantumNLS.Ext006PairDensityR40a

/-! Continuity of actual trace powers under trace-norm approximation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open scoped InnerProductSpace ENNReal
open Filter Topology
namespace QuantumNLS.Ext006TracePowersR40a
open TraceClass TraceIdeal TraceCompact TraceNormTopology
variable {H α : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {l : Filter α}

lemma operator_tendsto_of_trace {A : α → H →L[ℂ] H} {T : H →L[ℂ] H}
    (h : Tendsto (fun i => traceNorm (A i - T)) l (𝓝 0)) : Tendsto A l (𝓝 T) := by
  rw [← tendsto_sub_nhds_zero_iff]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [sub_zero]
  have hn : Tendsto (fun i => ENNReal.ofReal ‖A i - T‖) l (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => bot_le)
      (fun i => norm_le_traceNorm _)
  simpa only [Function.comp_def, ENNReal.toReal_ofReal (norm_nonneg _), ENNReal.toReal_zero] using
    (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp hn

lemma product_trace_tendsto {A B : α → H →L[ℂ] H} {T U : H →L[ℂ] H}
    (hA : Tendsto (fun i => traceNorm (A i - T)) l (𝓝 0))
    (hB : Tendsto (fun i => traceNorm (B i - U)) l (𝓝 0)) :
    Tendsto (fun i => traceNorm (A i * B i - T * U)) l (𝓝 0) := by
  have hAn := (operator_tendsto_of_trace hA).norm
  have hc : Tendsto (fun i => ENNReal.ofReal ‖A i‖ * traceNorm (B i-U) +
      traceNorm (A i-T) * ENNReal.ofReal ‖U‖) l (𝓝 0) := by
    have h1 := ENNReal.Tendsto.mul ((ENNReal.continuous_ofReal.tendsto _).comp hAn)
      (Or.inr ENNReal.zero_ne_top) hB (Or.inr ENNReal.ofReal_ne_top)
    have h2 := ENNReal.Tendsto.mul hA (Or.inr ENNReal.ofReal_ne_top)
      (tendsto_const_nhds (x := ENNReal.ofReal ‖U‖)) (Or.inr ENNReal.zero_ne_top)
    simpa using h1.add h2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc (fun _ => bot_le) (fun i => ?_)
  calc
    _ = traceNorm (A i * (B i-U) + (A i-T) * U) := by congr 1; noncomm_ring
    _ ≤ _ := traceNorm_add_le _ _
    _ ≤ _ := add_le_add (traceNorm_mul_left_le _ _) (traceNorm_mul_right_le _ _)

/-- Every fixed strictly positive power converges in the actual trace norm. -/
theorem power_trace_tendsto {A : α → H →L[ℂ] H} {T : H →L[ℂ] H}
    (hA : Tendsto (fun i => traceNorm (A i - T)) l (𝓝 0)) (n : ℕ) :
    Tendsto (fun i => traceNorm ((A i)^(n+1) - T^(n+1))) l (𝓝 0) := by
  induction n with
  | zero => simpa using hA
  | succ n ih => simpa only [pow_succ] using product_trace_tendsto ih hA

lemma traceNorm_tendsto_of_difference {A : α → H →L[ℂ] H} {T : H →L[ℂ] H}
    (hA : Tendsto (fun i => traceNorm (A i-T)) l (𝓝 0)) :
    Tendsto (fun i => traceNorm (A i)) l (𝓝 (traceNorm T)) := by
  have ht : Tendsto (fun i => (⟨A i⟩ : Op H)) l (𝓝 (⟨T⟩ : Op H)) := by
    rw [EMetric.tendsto_nhds]
    intro ε hε
    have he := (tendsto_order.1 hA).2 ε hε
    exact he
  exact continuous_traceNorm.continuousAt.tendsto.comp ht

/-- Real trace norms of fixed powers converge whenever the limiting power is trace class. -/
theorem power_trace_real_tendsto {A : α → H →L[ℂ] H} {T : H →L[ℂ] H}
    (hA : Tendsto (fun i => traceNorm (A i-T)) l (𝓝 0))
    (hT : IsTraceClass T) (n : ℕ) :
    Tendsto (fun i => (traceNorm ((A i)^(n+1))).toReal) l
      (𝓝 ((traceNorm (T^(n+1))).toReal)) :=
  (ENNReal.continuousAt_toReal (Ext006FredholmTracePower.traceNorm_power_finite T hT n)).tendsto.comp
    (traceNorm_tendsto_of_difference (power_trace_tendsto hA n))

/-- The finite reduced densities converge in every actual trace power. -/
theorem adjoint_density_trace_power_limit {ι : Type*} (b : HilbertBasis ι ℂ H)
    (K : H →L[ℂ] H) (hHS : hsSq b K ≠ ⊤) (n : ℕ) :
    Tendsto (fun S : Finset ι => (traceNorm
      ((TensorCarrier.reducedDensity (Ext006PairDensityR40a.finiteAdjointPair b K S))^(n+1))).toReal)
      atTop (𝓝 ((traceNorm ((K.adjoint ∘L K)^(n+1))).toReal)) :=
  power_trace_real_tendsto (Ext006PairDensityR40a.density_traceNorm_tendsto b K hHS)
    (Ext006Blocks.beta_adjoint_beta_traceClass b K hHS).1 n

end QuantumNLS.Ext006TracePowersR40a
#print axioms QuantumNLS.Ext006TracePowersR40a.power_trace_tendsto
#print axioms QuantumNLS.Ext006TracePowersR40a.adjoint_density_trace_power_limit

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006TracePowersR40a." then
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
  Lean.logInfo m!"Round40a aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
