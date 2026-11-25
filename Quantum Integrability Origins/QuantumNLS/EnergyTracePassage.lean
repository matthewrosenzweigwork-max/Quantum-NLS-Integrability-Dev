import QuantumNLS.Ext025B11TraceBasis
import QuantumNLS.Fidelity

/-! R-6EA807B1: total/complementary trace passage for actual positive
trace-class operators and a normalized strongly additive PVM. No spectral
representation of an arbitrary self-adjoint operator is presumed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Filter Topology MeasureTheory
open scoped InnerProductSpace BigOperators ENNReal
namespace QuantumNLS.EnergyTracePassage
open TraceClass TraceIdeal Ext025STrace Ext025B7GentleCompression
open BetheChargeResolution Ext025B6PVM Ext025B7SpectralCompression
open Ext025B11TracePairing Ext025B11TraceBasis
variable {E ι T : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def total (B : E →L[ℂ] E) : ℝ := (posTrace B).toReal
def tail (P B : E →L[ℂ] E) : ℝ := total ((1-P)*B*(1-P))

theorem finite_sub (S B : E →L[ℂ] E) (hS : IsTraceClass S) (hB : IsTraceClass B) :
    traceNorm (S-B) ≠ ⊤ := by
  have hn : traceNorm (-B) = traceNorm B := by
    rw [show -B = (-1 : ℂ) • B from (neg_one_smul ℂ B).symm,traceNorm_smul]
    simp
  rw [sub_eq_add_neg]
  exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hS.ne,by rw [hn]; exact hB.ne⟩)
    (traceNorm_add_le S (-B))

/-- Quantitative continuity of the total positive trace, including all
finiteness requirements needed to use real traces. -/
theorem total_difference (b : HilbertBasis ι ℂ E) (S B : E →L[ℂ] E)
    (hS : S.IsPositive) (hB : B.IsPositive) (htS : IsTraceClass S) (htB : IsTraceClass B) :
    |total S-total B| ≤ (traceNorm (S-B)).toReal := by
  have hh := norm_trace_le b (S-B) (finite_sub S B htS htB)
  rw [trace_sub b S B htS.ne htB.ne,trace_positive b S hS,trace_positive b B hB,
    ← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] at hh
  exact hh

/-- Total trace splits exactly into the two orthogonal diagonal blocks.
The proof applies Pythagoras to the square-root Hilbert--Schmidt factors. -/
theorem trace_split (b : HilbertBasis ι ℂ E) (P : ProjectionMeasure E)
    (s : Set ℝ) (hs : MeasurableSet s) (B : E →L[ℂ] E) (hB : B.IsPositive) :
    posTrace (P.toFun s*B*P.toFun s)+
      posTrace ((1-P.toFun s)*B*(1-P.toFun s)) = posTrace B := by
  have hp := P.selfAdjoint s hs
  have hq : (1-P.toFun s).adjoint = 1-P.toFun s := by
    simp only [map_sub,ContinuousLinearMap.adjoint_one,hp]
  have h1 := block_trace_hs b B (P.toFun s) hB
  have h2 := block_trace_hs b B (1-P.toFun s) hB
  simp only [hp,hq] at h1 h2
  rw [h1,h2]
  have hid := block_trace_hs b B 1 hB
  simp only [ContinuousLinearMap.adjoint_one,one_mul,mul_one] at hid
  rw [hid,hsSq,hsSq,hsSq,← ENNReal.tsum_add]
  apply tsum_congr
  intro i
  simp only [mul_apply_eq_comp,sub_apply,one_apply_eq_self]
  rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
  congr 1
  have hh := projection_error_sq P s hs (CFC.sqrt B (b i))
  linarith

theorem projection (P : ProjectionMeasure E) (s : Set ℝ) (hs : MeasurableSet s) :
    IsStarProjection (P.toFun s) :=
  ⟨idempotent P s hs,P.selfAdjoint s hs⟩

/-- Real-valued complementary trace is total minus compressed trace. -/
theorem tail_eq (b : HilbertBasis ι ℂ E) (P : ProjectionMeasure E)
    (s : Set ℝ) (hs : MeasurableSet s) (B : E →L[ℂ] E)
    (hB : B.IsPositive) (htB : IsTraceClass B) :
    tail (P.toFun s) B = total B-total (P.toFun s*B*P.toFun s) := by
  have hp := P.selfAdjoint s hs
  have hq : (1-P.toFun s).adjoint = 1-P.toFun s := by
    simp only [map_sub,ContinuousLinearMap.adjoint_one,hp]
  have hf := block_finite B (P.toFun s) hB htB
  have hg := block_finite B (1-P.toFun s) hB htB
  simp only [hp,hq] at hf hg
  have hh := congrArg ENNReal.toReal (trace_split b P s hs B hB)
  rw [ENNReal.toReal_add hf hg] at hh
  dsimp [tail,total]
  linarith

/-- The source's uniform complementary-trace passage is quantitative. -/
theorem tail_difference (b : HilbertBasis ι ℂ E) (P : ProjectionMeasure E)
    (s : Set ℝ) (hs : MeasurableSet s) (S B : E →L[ℂ] E)
    (hS : S.IsPositive) (hB : B.IsPositive) (htS : IsTraceClass S) (htB : IsTraceClass B) :
    |tail (P.toFun s) S-tail (P.toFun s) B| ≤
      |total S-total B|+(traceNorm (P.toFun s*(S-B)*P.toFun s)).toReal := by
  have hp := P.selfAdjoint s hs
  have hf (D : E →L[ℂ] E) (hD : D.IsPositive) (htD : IsTraceClass D) :
      IsTraceClass (P.toFun s*D*P.toFun s) := by
    rw [IsTraceClass,traceNorm_of_isPositive (by simpa only [hp] using block_positive D (P.toFun s) hD)]
    exact lt_top_iff_ne_top.mpr (by simpa only [hp] using block_finite D (P.toFun s) hD htD)
  have hh := total_difference b _ _
    (by simpa only [hp] using block_positive S (P.toFun s) hS)
    (by simpa only [hp] using block_positive B (P.toFun s) hB) (hf S hS htS) (hf B hB htB)
  rw [← sub_mul,← mul_sub] at hh
  rw [tail_eq b P s hs S hS htS,tail_eq b P s hs B hB htB]
  have he : total S-total (P.toFun s*S*P.toFun s)-
      (total B-total (P.toFun s*B*P.toFun s)) =
      (total S-total B)-(total (P.toFun s*S*P.toFun s)-total (P.toFun s*B*P.toFun s)) := by ring
  rw [he]
  exact (abs_sub _ _).trans (add_le_add le_rfl hh)

/-- A literal uniform-in-parameter version of the complementary passage. -/
theorem uniform_complementary (b : HilbertBasis ι ℂ E) (P : ProjectionMeasure E)
    (s : Set ℝ) (hs : MeasurableSet s) (B : ℕ → T → E →L[ℂ] E) (D : T → E →L[ℂ] E)
    (hB : ∀ n t, (B n t).IsPositive ∧ IsTraceClass (B n t))
    (hD : ∀ t, (D t).IsPositive ∧ IsTraceClass (D t))
    (ht : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ t, |total (B n t)-total (D t)| ≤ ε)
    (hc : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ t,
      traceNorm (P.toFun s*(B n t-D t)*P.toFun s) ≤ ENNReal.ofReal ε) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ t,
      |tail (P.toFun s) (B n t)-tail (P.toFun s) (D t)| ≤ ε := by
  intro ε hε
  filter_upwards [ht (ε/2) (by linarith),hc (ε/2) (by linarith)] with n hn hm
  intro t
  have hh := tail_difference b P s hs (B n t) (D t) (hB n t).1 (hD t).1 (hB n t).2 (hD t).2
  have hr := ENNReal.toReal_le_of_le_ofReal (by linarith : 0 ≤ ε/2) (hm t)
  linarith [hn t]
end QuantumNLS.EnergyTracePassage

#print axioms QuantumNLS.EnergyTracePassage.trace_split
#print axioms QuantumNLS.EnergyTracePassage.total_difference
#print axioms QuantumNLS.EnergyTracePassage.tail_difference
#print axioms QuantumNLS.EnergyTracePassage.uniform_complementary
set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.EnergyTracePassage" then
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
  Lean.logInfo m!"EnergyTracePassage audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."
