import QuantumNLS.EnergyTraceLimit
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-! Positive-contraction trace estimates for continuous exhaustion. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped InnerProductSpace ENNReal ComplexOrder BigOperators
open Filter Topology
namespace QuantumNLS.ContractionTraceR13
open TraceClass TraceIdeal TraceCompact Ext025STrace Ext025B7GentleCompression EnergyTracePassage
variable {E ι T : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem contraction_gentle (b : HilbertBasis ι ℂ E) (ρ P : E →L[ℂ] E)
    (hρ : ρ.IsPositive) (htrace : IsTraceClass ρ) (hp : P.adjoint = P) (hn : ‖P‖ ≤ 1) :
    traceNorm (ρ-P*ρ*P) ≤ ENNReal.ofReal
      (2*Real.sqrt ((posTrace ρ).toReal*(posTrace ((1-P)*ρ*(1-P))).toReal)) := by
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
    exact ENNReal.ofReal_le_ofReal hn
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

/-- The trace split becomes an inequality for a positive contraction. -/
theorem vector_defect (P : E →L[ℂ] E) (hp : 0 ≤ P) (hn : ‖P‖ ≤ 1) (x : E) :
    ‖P x‖^2 + ‖x-P x‖^2 ≤ ‖x‖^2 := by
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hp.isSelfAdjoint
  have hh := CStarAlgebra.mul_self_le_of_nonneg_of_norm_le_one hp hn
  have hi := (ContinuousLinearMap.nonneg_iff_isPositive.mp (sub_nonneg.mpr hh)).re_inner_nonneg_left x
  change 0 ≤ (inner ℂ ((P-P*P) x) x).re at hi
  have hi' : inner ℂ (P (P x)) x = inner ℂ (P x) (P x) := hs (P x) x
  simp only [sub_apply,mul_apply_eq_comp,inner_sub_left,Complex.sub_re,hi'] at hi
  have hself := inner_self_eq_norm_sq (𝕜 := ℂ) (P x)
  change (inner ℂ (P x) (P x)).re = ‖P x‖^2 at hself
  rw [hself] at hi
  have he := norm_sub_sq (𝕜 := ℂ) x (P x)
  rw [inner_re_symm] at he
  change ‖x-P x‖^2 = ‖x‖^2-2*(inner ℂ (P x) x).re+‖P x‖^2 at he
  linarith

theorem trace_defect (b : HilbertBasis ι ℂ E) (P B : E →L[ℂ] E)
    (hp : 0 ≤ P) (hn : ‖P‖ ≤ 1) (hB : B.IsPositive) :
    posTrace (P*B*P)+posTrace ((1-P)*B*(1-P)) ≤ posTrace B := by
  have hs : P.adjoint = P := hp.isSelfAdjoint
  have hq : (1-P).adjoint = 1-P := by simp only [map_sub,ContinuousLinearMap.adjoint_one,hs]
  have h1 := block_trace_hs b B P hB
  have h2 := block_trace_hs b B (1-P) hB
  have hid := block_trace_hs b B 1 hB
  simp only [hs,hq] at h1 h2
  simp only [ContinuousLinearMap.adjoint_one,one_mul,mul_one] at hid
  rw [h1,h2,hid,hsSq,hsSq,hsSq,← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro i
  simp only [mul_apply_eq_comp,sub_apply,one_apply_eq_self]
  rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (vector_defect P hp hn _)

theorem tail_le_defect (b : HilbertBasis ι ℂ E) (P B : E →L[ℂ] E)
    (hp : 0 ≤ P) (hn : ‖P‖ ≤ 1) (hB : B.IsPositive) (htB : IsTraceClass B) :
    tail P B ≤ total B-total (P*B*P) := by
  have hs : P.adjoint = P := hp.isSelfAdjoint
  have hq : (1-P).adjoint = 1-P := by simp only [map_sub,ContinuousLinearMap.adjoint_one,hs]
  have hf := block_finite B P hB htB
  have hg := block_finite B (1-P) hB htB
  simp only [hs,hq] at hf hg
  have ht : posTrace B ≠ ⊤ := by rw [← traceNorm_of_isPositive hB]; exact htB.ne
  have hh := (ENNReal.toReal_mono ht (trace_defect b P B hp hn hB))
  rw [ENNReal.toReal_add hf hg] at hh
  dsimp [tail,total]
  linarith

end QuantumNLS.ContractionTraceR13
