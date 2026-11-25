import QuantumNLS.Ext025STrace

/-! GP-09: completeness of the actual frozen trace norm. The operator limit is
constructed using completeness in operator norm; finite contraction tests then
prove convergence in trace norm. No ideal-completeness premise is supplied. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Filter Topology InnerProductSpace
open scoped InnerProductSpace ENNReal
namespace QuantumNLS.Ext025B6TraceCompletion
open TraceClass TraceIdeal
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Closed finite trace-norm balls in the operator norm topology. -/
theorem traceNorm_limit_bound {J : Type*} {l : Filter J} [l.NeBot]
    (b : HilbertBasis ι ℂ E) (A : J → E →L[ℂ] E) (T : E →L[ℂ] E)
    (hlim : Tendsto A l (𝓝 T)) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ᶠ j in l, traceNorm (A j) ≤ ENNReal.ofReal C) :
    traceNorm T ≤ ENNReal.ofReal C := by
  apply traceNorm_le_of_forall b
  intro X hX F
  have ht : Tendsto (fun j => (∑ i ∈ F, ⟪X (b i),A j (b i)⟫_ℂ).re) l
      (𝓝 (∑ i ∈ F, ⟪X (b i),T (b i)⟫_ℂ).re) := by
    apply Complex.continuous_re.continuousAt.tendsto.comp
    exact tendsto_finsetSum F fun i _ => tendsto_const_nhds.inner
      (((ContinuousLinearMap.apply ℂ E (b i)).continuous).tendsto T |>.comp hlim)
  apply le_of_tendsto ht
  filter_upwards [hbound] with j hj
  have hf : traceNorm (A j) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hj
  have hh := (RCLike.re_le_norm (∑ i ∈ F, ⟪X (b i),A j (b i)⟫_ℂ)).trans
    (norm_sum_inner_le_traceNorm b (A j) X hX hf F)
  exact hh.trans (by simpa only [ENNReal.toReal_ofReal hC] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hj)

/-- Trace-norm Cauchy sequences have an operator norm limit. -/
theorem operator_cauchy (A : ℕ → E →L[ℂ] E)
    (hA : ∀ ε : ℝ, 0 < ε → ∃ K, ∀ m ≥ K, ∀ n ≥ K,
      traceNorm (A m-A n) ≤ ENNReal.ofReal ε) : CauchySeq A := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨K,hK⟩ := hA (ε/2) (by positivity)
  refine ⟨K,fun m hm n hn => ?_⟩
  rw [dist_eq_norm]
  have h := (norm_le_traceNorm (A m-A n)).trans (hK m hm n hn)
  have hh : ‖A m-A n‖ ≤ ε/2 :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ ε/2)).mp h
  linarith

/-- Completeness for the actual trace ideal: every trace-norm Cauchy sequence
of trace-class operators converges in trace norm to a trace-class operator. -/
theorem trace_complete (b : HilbertBasis ι ℂ E) (A : ℕ → E →L[ℂ] E)
    (hfin : ∀ n, IsTraceClass (A n))
    (hA : ∀ ε : ℝ, 0 < ε → ∃ K, ∀ m ≥ K, ∀ n ≥ K,
      traceNorm (A m-A n) ≤ ENNReal.ofReal ε) :
    ∃ T : E →L[ℂ] E, IsTraceClass T ∧ Tendsto A atTop (𝓝 T) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, traceNorm (A n-T) ≤ ENNReal.ofReal ε := by
  obtain ⟨T,hT⟩ := cauchySeq_tendsto_of_complete (operator_cauchy A hA)
  have hc (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ n in atTop, traceNorm (A n-T) ≤ ENNReal.ofReal ε := by
    obtain ⟨K,hK⟩ := hA ε hε
    apply eventually_atTop.mpr
    refine ⟨K,fun n hn => ?_⟩
    apply traceNorm_limit_bound b (fun m => A n-A m) (A n-T)
      (tendsto_const_nhds.sub hT) ε hε.le
    exact eventually_atTop.mpr ⟨K,fun m hm => hK n hn m hm⟩
  have hfT : IsTraceClass T := by
    obtain ⟨n,hn⟩ := (hc 1 zero_lt_one).exists
    have he : T = A n + (-1 : ℂ) • (A n-T) := by simp
    rw [he]
    apply (hfin n).add
    unfold IsTraceClass
    rw [traceNorm_smul]
    have hb : traceNorm (A n-T) < ⊤ := hn.trans_lt ENNReal.ofReal_lt_top
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hb
  exact ⟨T,hfT,hT,hc⟩

end QuantumNLS.Ext025B6TraceCompletion

#print axioms QuantumNLS.Ext025B6TraceCompletion.traceNorm_limit_bound
#print axioms QuantumNLS.Ext025B6TraceCompletion.operator_cauchy
#print axioms QuantumNLS.Ext025B6TraceCompletion.trace_complete

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext025B6TraceCompletion." then
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
  Lean.logInfo m!"Ext025B6TraceCompletion audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."
