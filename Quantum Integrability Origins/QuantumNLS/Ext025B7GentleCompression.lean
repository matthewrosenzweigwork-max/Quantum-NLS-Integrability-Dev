import QuantumNLS.Ext025STrace

/-! GP-09, R-6EA807B1: assemble the actual positive four-block estimate.
The operators and traces are the frozen trace ideal's concrete ones. Neither
the cross-block estimate nor trace-norm completeness is an input premise. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open scoped InnerProductSpace ENNReal ComplexOrder
namespace QuantumNLS.Ext025B7GentleCompression
open TraceClass TraceIdeal TraceCompact Ext025STrace
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Positivity of an actual diagonal block. -/
theorem block_positive (ρ P : E →L[ℂ] E) (hρ : ρ.IsPositive) :
    (P*ρ*P.adjoint).IsPositive := by
  simpa only [ContinuousLinearMap.mul_def,ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.comp_assoc] using hρ.adjoint_conj P.adjoint

omit [CompleteSpace E] in
/-- Algebraic identity used before applying the ideal estimates. -/
theorem four_blocks (ρ P : E →L[ℂ] E) :
    ρ-P*ρ*P = (1-P)*ρ*(1-P)+P*ρ*(1-P)+(1-P)*ρ*P := by noncomm_ring

/-- Convert the three positive block bounds to the displayed real formula. -/
theorem scalar_conversion (t δ : ℝ≥0∞) (hδ : δ ≠ ⊤) :
    δ+ENNReal.ofReal (Real.sqrt t.toReal*Real.sqrt δ.toReal)+
      ENNReal.ofReal (Real.sqrt δ.toReal*Real.sqrt t.toReal) =
    ENNReal.ofReal (δ.toReal+2*Real.sqrt (t.toReal*δ.toReal)) := by
  have hp : 0 ≤ Real.sqrt t.toReal*Real.sqrt δ.toReal := by positivity
  have hq : 0 ≤ Real.sqrt δ.toReal*Real.sqrt t.toReal := by positivity
  calc
    δ+ENNReal.ofReal (Real.sqrt t.toReal*Real.sqrt δ.toReal)+
        ENNReal.ofReal (Real.sqrt δ.toReal*Real.sqrt t.toReal) =
      ENNReal.ofReal δ.toReal+ENNReal.ofReal (Real.sqrt t.toReal*Real.sqrt δ.toReal)+
        ENNReal.ofReal (Real.sqrt δ.toReal*Real.sqrt t.toReal) := by
      rw [ENNReal.ofReal_toReal hδ]
    _ = ENNReal.ofReal (δ.toReal+Real.sqrt t.toReal*Real.sqrt δ.toReal+
        Real.sqrt δ.toReal*Real.sqrt t.toReal) := by
      rw [ENNReal.ofReal_add (add_nonneg ENNReal.toReal_nonneg hp) hq,
        ENNReal.ofReal_add ENNReal.toReal_nonneg hp]
    _ = _ := by
      congr 1
      rw [Real.sqrt_mul ENNReal.toReal_nonneg]
      ring

/-- The requested delta + 2 sqrt(t delta) estimate, with t and delta
literally the two positive diagonal traces. Finiteness is the natural
trace-ideal hypothesis; no limiting conclusion is assumed. -/
theorem four_block_bound (b : HilbertBasis ι ℂ E) (ρ P : E →L[ℂ] E)
    (hρ : ρ.IsPositive) (hP : P.adjoint = P)
    (ht : posTrace (P*ρ*P) ≠ ⊤) (hδ : posTrace ((1-P)*ρ*(1-P)) ≠ ⊤) :
    traceNorm (ρ-P*ρ*P) ≤ ENNReal.ofReal
      ((posTrace ((1-P)*ρ*(1-P))).toReal +
        2*Real.sqrt ((posTrace (P*ρ*P)).toReal*(posTrace ((1-P)*ρ*(1-P))).toReal)) := by
  have hQ : (1-P).adjoint = 1-P := by simp only [map_sub,ContinuousLinearMap.adjoint_one,hP]
  have hPQ := gp09_cross_block b ρ P (1-P) hρ (by simpa only [hP] using ht)
    (by simpa only [hQ] using hδ)
  have hQP := gp09_cross_block b ρ (1-P) P hρ (by simpa only [hQ] using hδ)
    (by simpa only [hP] using ht)
  simp only [hP,hQ] at hPQ hQP
  have hQQ : traceNorm ((1-P)*ρ*(1-P)) = posTrace ((1-P)*ρ*(1-P)) := by
    apply traceNorm_of_isPositive
    simpa only [hQ] using block_positive ρ (1-P) hρ
  rw [four_blocks ρ P]
  calc
    traceNorm ((1-P)*ρ*(1-P)+P*ρ*(1-P)+(1-P)*ρ*P) ≤
        traceNorm ((1-P)*ρ*(1-P))+traceNorm (P*ρ*(1-P))+traceNorm ((1-P)*ρ*P) :=
      (traceNorm_add_le _ _).trans (add_le_add (traceNorm_add_le _ _) (le_refl _))
    _ ≤ posTrace ((1-P)*ρ*(1-P))+
        ENNReal.ofReal (Real.sqrt (posTrace (P*ρ*P)).toReal *
          Real.sqrt (posTrace ((1-P)*ρ*(1-P))).toReal)+
        ENNReal.ofReal (Real.sqrt (posTrace ((1-P)*ρ*(1-P))).toReal *
          Real.sqrt (posTrace (P*ρ*P)).toReal) := by
      rw [hQQ]
      exact add_le_add (add_le_add (le_refl _) hPQ) hQP
    _ = _ := scalar_conversion _ _ hδ

/-- A positive trace-class input supplies finite diagonal traces for every
bounded block. Thus finiteness need not be separately supplied downstream. -/
theorem block_finite (ρ P : E →L[ℂ] E) (hρ : ρ.IsPositive) (htrace : IsTraceClass ρ) :
    posTrace (P*ρ*P.adjoint) ≠ ⊤ := by
  rw [← traceNorm_of_isPositive (block_positive ρ P hρ)]
  exact ne_of_lt ((traceNorm_mul_mul_le P ρ P.adjoint).trans_lt
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top htrace) ENNReal.ofReal_lt_top))

/-- The four-block bound for the source's orthogonal projection and any
positive trace-class operator. The numerical traces are not free parameters. -/
theorem positive_trace_four_block (b : HilbertBasis ι ℂ E) (ρ P : E →L[ℂ] E)
    (hρ : ρ.IsPositive) (htrace : IsTraceClass ρ) (hP : IsStarProjection P) :
    traceNorm (ρ-P*ρ*P) ≤ ENNReal.ofReal
      ((posTrace ((1-P)*ρ*(1-P))).toReal +
        2*Real.sqrt ((posTrace (P*ρ*P)).toReal*(posTrace ((1-P)*ρ*(1-P))).toReal)) := by
  have hp : P.adjoint = P := hP.isSelfAdjoint
  have hq : (1-P).adjoint = 1-P := by simp only [map_sub,ContinuousLinearMap.adjoint_one,hp]
  apply four_block_bound b ρ P hρ hp
  · simpa only [hp] using block_finite ρ P hρ htrace
  · simpa only [hq] using block_finite ρ (1-P) hρ htrace

/-- The exact total-trace gentle estimate used by R-6EA807B1. It follows
from the two-term square-root factorization, without general trace cyclicity. -/
theorem positive_trace_gentle (b : HilbertBasis ι ℂ E) (ρ P : E →L[ℂ] E)
    (hρ : ρ.IsPositive) (htrace : IsTraceClass ρ) (hP : IsStarProjection P) :
    traceNorm (ρ-P*ρ*P) ≤ ENNReal.ofReal
      (2*Real.sqrt ((posTrace ρ).toReal*(posTrace ((1-P)*ρ*(1-P))).toReal)) := by
  have hp : P.adjoint = P := hP.isSelfAdjoint
  have hq : (1-P).adjoint = 1-P := by simp only [map_sub,ContinuousLinearMap.adjoint_one,hp]
  have ht : posTrace ρ ≠ ⊤ := by
    rw [← traceNorm_of_isPositive hρ]
    exact ne_of_lt htrace
  have hδ : posTrace ((1-P)*ρ*(1-P)) ≠ ⊤ := by
    simpa only [hq] using block_finite ρ (1-P) hρ htrace
  have hright := gp09_cross_block b ρ 1 (1-P) hρ (by simpa only [ContinuousLinearMap.adjoint_one,one_mul,mul_one] using ht)
    (by simpa only [hq] using hδ)
  have hleft := gp09_cross_block b ρ (1-P) 1 hρ (by simpa only [hq] using hδ)
    (by simpa only [ContinuousLinearMap.adjoint_one,one_mul,mul_one] using ht)
  simp only [ContinuousLinearMap.adjoint_one,one_mul,mul_one,hq] at hright hleft
  have hnorm : ENNReal.ofReal ‖P‖ ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (IsStarProjection.norm_le P hP)
  have hcontract : traceNorm (P*(ρ*(1-P))) ≤ traceNorm (ρ*(1-P)) := by
    calc
      _ ≤ ENNReal.ofReal ‖P‖*traceNorm (ρ*(1-P)) := traceNorm_mul_left_le _ _
      _ ≤ 1*traceNorm (ρ*(1-P)) := mul_le_mul_of_nonneg_right hnorm (bot_le)
      _ = _ := one_mul _
  have he : ρ-P*ρ*P = (1-P)*ρ+P*(ρ*(1-P)) := by noncomm_ring
  rw [he]
  calc
    traceNorm ((1-P)*ρ+P*(ρ*(1-P))) ≤
        traceNorm ((1-P)*ρ)+traceNorm (P*(ρ*(1-P))) := traceNorm_add_le _ _
    _ ≤ ENNReal.ofReal (Real.sqrt (posTrace ((1-P)*ρ*(1-P))).toReal *
          Real.sqrt (posTrace ρ).toReal)+
        ENNReal.ofReal (Real.sqrt (posTrace ρ).toReal *
          Real.sqrt (posTrace ((1-P)*ρ*(1-P))).toReal) :=
      add_le_add hleft (hcontract.trans hright)
    _ = _ := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        Real.sqrt_mul ENNReal.toReal_nonneg]
      congr 1
      ring

end QuantumNLS.Ext025B7GentleCompression

#print axioms QuantumNLS.Ext025B7GentleCompression.block_positive
#print axioms QuantumNLS.Ext025B7GentleCompression.four_blocks
#print axioms QuantumNLS.Ext025B7GentleCompression.scalar_conversion
#print axioms QuantumNLS.Ext025B7GentleCompression.four_block_bound
#print axioms QuantumNLS.Ext025B7GentleCompression.block_finite
#print axioms QuantumNLS.Ext025B7GentleCompression.positive_trace_four_block

#print axioms QuantumNLS.Ext025B7GentleCompression.positive_trace_gentle

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext025B7GentleCompression." then
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
  Lean.logInfo m!"Ext025B7GentleCompression audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."
