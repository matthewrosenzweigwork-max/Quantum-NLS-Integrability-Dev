/-
QuantumNLS.TraceCompact — positive trace-class operators are compact (owner: opus_tensor).

Standalone analytic interface.  Frozen imports, read-only: Fidelity FD3 (sha256 84f2a973…394ca),
which brings TraceClass TC6.

Proof: finite-rank frame approximation.  The partial frame sums
`A_s = Σ_{i∈s} |√A bᵢ⟩⟨√A bᵢ|` are finite sums of rank-one operators, hence compact.
By FD3 (`traceNorm_sub_frameSum`, `tendsto_traceNorm_sub_frameSum`) we have
`‖A − A_s‖₁ = Tr A − Σ_{i∈s} λᵢ → 0`.  By TC6 (`norm_le_traceNorm`) `‖A − A_s‖ ≤ ‖A − A_s‖₁`.
So `A_s → A` in operator norm, and the compact operators are closed
(mathlib `isCompactOperator_of_tendsto`).  General finite trace reduces to trace one by scaling.

Scope: this does NOT start the compact spectral theorem (eigenbasis) chain; S2 policy of
R-828C5F7E is unchanged.
-/
import QuantumNLS.Fidelity
import Mathlib.Analysis.Normed.Operator.Compact.Basic

open scoped InnerProductSpace ENNReal ComplexOrder
open QuantumNLS.TraceClass QuantumNLS.Fidelity Filter Topology

noncomputable section

namespace QuantumNLS.TraceCompact

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Rank-one operators are compact (their range lies in a line, which is locally compact). -/
theorem isCompactOperator_rankOne (x y : E) :
    IsCompactOperator (InnerProductSpace.rankOne ℂ x y) := by
  rw [InnerProductSpace.rankOne_def']
  exact (isCompactOperator_of_locallyCompactSpace_rng
    (ContinuousLinearMap.toSpanSingleton ℂ x)).comp_clm (innerSL ℂ y)

/-- The partial frame sums are compact (finite rank). -/
theorem isCompactOperator_frameSum {ι : Type*} (b : HilbertBasis ι ℂ E) (A : E →L[ℂ] E)
    (s : Finset ι) : IsCompactOperator (frameSum b A s) := by
  classical
  unfold frameSum
  induction s using Finset.induction_on with
  | empty => simpa using (isCompactOperator_zero : IsCompactOperator (0 : E → E))
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact (isCompactOperator_rankOne _ _).add ih

/-- `A_s → A` in operator norm when `A ≥ 0` and `Tr A = 1`. -/
theorem tendsto_frameSum_of_trace_one {A : E →L[ℂ] E} (hA : A.IsPositive)
    (hTr : posTrace A = 1) :
    Tendsto (fun s => frameSum (refBasis E) A s) atTop (𝓝 A) := by
  set b := refBasis E
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h := tendsto_traceNorm_sub_frameSum b hA hTr
  have h2 : Tendsto (fun s => (traceNorm (A - frameSum b A s)).toReal) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
    rw [ENNReal.toReal_zero] at this
    exact this
  refine squeeze_zero (fun s => norm_nonneg _) (fun s => ?_) h2
  rw [norm_sub_rev]
  have hfin : traceNorm (A - frameSum b A s) ≠ ⊤ := by
    rw [traceNorm_sub_frameSum b hA hTr s]; exact ENNReal.ofReal_ne_top
  exact (ENNReal.ofReal_le_iff_le_toReal hfin).mp (norm_le_traceNorm _)

/-- A positive operator of trace one is compact. -/
theorem isCompactOperator_of_trace_one {A : E →L[ℂ] E} (hA : A.IsPositive)
    (hTr : posTrace A = 1) : IsCompactOperator A :=
  isCompactOperator_of_tendsto (tendsto_frameSum_of_trace_one hA hTr)
    (Eventually.of_forall fun s => isCompactOperator_frameSum (refBasis E) A s)

/-- **Positive trace-class operators are compact.**  (`Tr A < ∞`, `A ≥ 0` ⇒ `A` compact.) -/
theorem isCompactOperator_of_isPositive_of_posTrace_ne_top {A : E →L[ℂ] E} (hA : A.IsPositive)
    (hfin : posTrace A ≠ ⊤) : IsCompactOperator A := by
  by_cases h0 : posTrace A = 0
  · have hA0 : A = 0 := by
      rw [← traceNorm_eq_zero_iff, traceNorm_of_isPositive hA, h0]
    rw [hA0]
    exact isCompactOperator_zero
  · set t : ℝ := (posTrace A).toReal with ht
    have htpos : 0 < t := ENNReal.toReal_pos h0 hfin
    set B : E →L[ℂ] E := ((t⁻¹ : ℝ) : ℂ) • A with hB
    have hBpos : B.IsPositive :=
      hA.smul_of_nonneg (Complex.zero_le_real.mpr (inv_nonneg.mpr htpos.le))
    have hBtr : posTrace B = 1 := by
      rw [← traceNorm_of_isPositive hBpos, hB, traceNorm_smul, traceNorm_of_isPositive hA,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr htpos),
        ← ENNReal.ofReal_toReal hfin, ← ht, ← ENNReal.ofReal_mul (inv_pos.mpr htpos).le,
        inv_mul_cancel₀ htpos.ne', ENNReal.ofReal_one]
    have hBc := isCompactOperator_of_trace_one hBpos hBtr
    have hAB : A = ((t : ℝ) : ℂ) • B := by
      rw [hB, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ htpos.ne', Complex.ofReal_one,
        one_smul]
    rw [hAB]
    exact hBc.smul _

/-- Trace-class formulation: a positive trace-class operator is compact. -/
theorem IsTraceClass.isCompactOperator_of_isPositive {A : E →L[ℂ] E} (hA : A.IsPositive)
    (hAtc : IsTraceClass A) : IsCompactOperator A := by
  refine isCompactOperator_of_isPositive_of_posTrace_ne_top hA ?_
  rw [← traceNorm_of_isPositive hA]
  exact hAtc.ne

/-! ## Left ideal bound (bounded-weight interface) -/

/-- **Left ideal property:** `‖X T‖₁ ≤ ‖X‖ ‖T‖₁` for bounded `X`.  Proof via the TC6 duality:
`Σᵢ ⟪Y bᵢ, X T bᵢ⟫ = ‖X‖ Σᵢ ⟪Y' bᵢ, T bᵢ⟫` with the contraction `Y' = ‖X‖⁻¹ X† Y`. -/
theorem traceNorm_mul_left_le (X T : E →L[ℂ] E) :
    traceNorm (X * T) ≤ ENNReal.ofReal ‖X‖ * traceNorm T := by
  by_cases hX : ‖X‖ = 0
  · have hX0 : X = 0 := norm_eq_zero.mp hX
    rw [hX0, zero_mul, (traceNorm_eq_zero_iff 0).mpr rfl]
    exact zero_le
  have hXpos : 0 < ‖X‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hX)
  by_cases hT : traceNorm T = ⊤
  · rw [hT, ENNReal.mul_top (by simpa using hXpos)]
    exact le_top
  have hc : ENNReal.ofReal ‖X‖ * traceNorm T = ENNReal.ofReal (‖X‖ * (traceNorm T).toReal) := by
    rw [ENNReal.ofReal_mul hXpos.le, ENNReal.ofReal_toReal hT]
  rw [hc]
  refine traceNorm_le_of_forall (refBasis E) _ fun Y hY s => ?_
  set b := refBasis E
  set Y' : E →L[ℂ] E := ((‖X‖⁻¹ : ℝ) : ℂ) • (ContinuousLinearMap.adjoint X * Y) with hY'
  have hY'n : ‖Y'‖ ≤ 1 := by
    rw [hY', norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm]
    calc ‖X‖⁻¹ * ‖ContinuousLinearMap.adjoint X * Y‖
        ≤ ‖X‖⁻¹ * (‖ContinuousLinearMap.adjoint X‖ * ‖Y‖) :=
          mul_le_mul_of_nonneg_left (norm_mul_le _ _) (inv_nonneg.mpr hXpos.le)
      _ ≤ ‖X‖⁻¹ * (‖X‖ * 1) := by
          rw [LinearIsometryEquiv.norm_map]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hY hXpos.le)
            (inv_nonneg.mpr hXpos.le)
      _ = 1 := by field_simp
  have he : ∑ i ∈ s, ⟪Y (b i), (X * T) (b i)⟫_ℂ =
      ((‖X‖ : ℝ) : ℂ) * ∑ i ∈ s, ⟪Y' (b i), T (b i)⟫_ℂ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hY', ContinuousLinearMap.smul_apply, inner_smul_left, Complex.conj_ofReal,
      ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.adjoint_inner_left, ← mul_assoc, ← Complex.ofReal_mul,
      mul_inv_cancel₀ hX, Complex.ofReal_one, one_mul]
  rw [he]
  refine (RCLike.re_le_norm _).trans ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_norm]
  exact mul_le_mul_of_nonneg_left (norm_sum_inner_le_traceNorm b T Y' hY'n hT s) hXpos.le

end QuantumNLS.TraceCompact

#print axioms QuantumNLS.TraceCompact.isCompactOperator_rankOne
#print axioms QuantumNLS.TraceCompact.tendsto_frameSum_of_trace_one
#print axioms QuantumNLS.TraceCompact.isCompactOperator_of_isPositive_of_posTrace_ne_top
#print axioms QuantumNLS.TraceCompact.IsTraceClass.isCompactOperator_of_isPositive
#print axioms QuantumNLS.TraceCompact.traceNorm_mul_left_le
