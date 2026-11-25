import QuantumNLS.Ext025A12PartialTrace
import QuantumNLS.Ext025A12Trace
import QuantumNLS.Ext025B6TraceCompletion
import QuantumNLS.Ext025B6HilbertSchmidtCompletion

/-! EXT-025 layer A (part 2), haiku_inventory. Contract GP-09 =
FIN-EXT025-GP-09 (trace ideals, positive compressions and partial traces),
stated at the literal text of FINAL_EXTERNAL_THEOREM_INSTANCES.json:
  hypotheses: operators act on separable Hilbert spaces; trace-class and
  Hilbert-Schmidt factors have the indicated finite ideal norms; cyclic
  rearrangements include one trace-class factor and bounded other factors; partial
  traces are over a Hilbert tensor factor;
  conclusion: the trace ideals are complete two-sided ideals; the product of two
  Hilbert-Schmidt operators is trace class with the product-norm bound; the trace
  is basis independent and cyclic with bounded factors; partial trace is positive,
  trace preserving on positive inputs and contractive in trace norm.
Separability is kept as a hypothesis although the proofs do not use it. Two
Hilbert-Schmidt multiplication bounds are proved here; everything else is a
frozen theorem (trace ideal submodule, Ext025B6 completions, Ext025A12 trace
basis independence and cyclicity, partial trace). -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Filter Topology
open scoped InnerProductSpace ENNReal ComplexOrder
open QuantumNLS.TraceClass QuantumNLS.TraceIdeal QuantumNLS.TensorCarrier

namespace QuantumNLS.Ext025HGP09

/-- Hilbert-Schmidt left multiplication bound, proved from the definition of hsSq. -/
theorem hs_left {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {ι : Type*} (b : HilbertBasis ι ℂ E) (W T : E →L[ℂ] E) :
    hsSq b (W * T) ≤ ENNReal.ofReal (‖W‖ ^ 2) * hsSq b T := by
  unfold hsSq
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun i => ?_
  rw [← ENNReal.ofReal_mul (sq_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  have h1 : ‖W (T (b i))‖ ≤ ‖W‖ * ‖T (b i)‖ := W.le_opNorm _
  have h2 : ‖W (T (b i))‖ ^ 2 ≤ (‖W‖ * ‖T (b i)‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  rw [mul_pow] at h2
  exact h2

/-- Hilbert-Schmidt right multiplication bound, by adjointing. -/
theorem hs_right {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {ι : Type*} (b : HilbertBasis ι ℂ E) (T V : E →L[ℂ] E) :
    hsSq b (T * V) ≤ ENNReal.ofReal (‖V‖ ^ 2) * hsSq b T := by
  have he : (T * V).adjoint = V.adjoint * T.adjoint := by
    rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.mul_def]
  have h1 : hsSq b (T * V) = hsSq b (V.adjoint * T.adjoint) := by
    rw [hsSq_eq_hsSq_adjoint b b (T * V), he]
  have h2 := hs_left b V.adjoint T.adjoint
  have h3 : hsSq b T.adjoint = hsSq b T := (hsSq_eq_hsSq_adjoint b b T).symm
  have h4 : ‖V.adjoint‖ = ‖V‖ := LinearIsometryEquiv.norm_map ContinuousLinearMap.adjoint V
  calc hsSq b (T * V) = hsSq b (V.adjoint * T.adjoint) := h1
    _ ≤ ENNReal.ofReal (‖V.adjoint‖ ^ 2) * hsSq b T.adjoint := h2
    _ = ENNReal.ofReal (‖V‖ ^ 2) * hsSq b T := by rw [h4, h3]

/-- Exact contract GP-09. -/
theorem contract_GP09 {E X Y : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    [TopologicalSpace.SeparableSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    [TopologicalSpace.SeparableSpace Y] :
    -- trace ideal: a subspace, two-sided, complete in trace norm
    (∀ S T : E →L[ℂ] E, IsTraceClass S → IsTraceClass T → IsTraceClass (S + T)) ∧
    (∀ (c : ℂ) (T : E →L[ℂ] E), IsTraceClass T → IsTraceClass (c • T)) ∧
    (∀ W T V : E →L[ℂ] E, IsTraceClass T → IsTraceClass (W * T * V)) ∧
    (∀ {ι : Type*} (b : HilbertBasis ι ℂ E) (A : ℕ → E →L[ℂ] E), (∀ n, IsTraceClass (A n)) →
      (∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ m ≥ K, ∀ n ≥ K, traceNorm (A m - A n) ≤ ENNReal.ofReal ε) →
      ∃ T : E →L[ℂ] E, IsTraceClass T ∧ Tendsto A atTop (𝓝 T) ∧
        ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, traceNorm (A n - T) ≤ ENNReal.ofReal ε) ∧
    -- Hilbert-Schmidt ideal: two-sided, complete
    (∀ {ι : Type*} (b : HilbertBasis ι ℂ E) (W T V : E →L[ℂ] E),
      hsSq b (W * T * V) ≤ ENNReal.ofReal (‖V‖ ^ 2) * (ENNReal.ofReal (‖W‖ ^ 2) * hsSq b T)) ∧
    (∀ {ι : Type*} (b : HilbertBasis ι ℂ E) (A : ℕ → E →L[ℂ] E), (∀ n, hsSq b (A n) ≠ ⊤) →
      (∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ m ≥ K, ∀ n ≥ K, hsSq b (A m - A n) ≤ ENNReal.ofReal (ε ^ 2)) →
      ∃ T : E →L[ℂ] E, hsSq b T ≠ ⊤ ∧ Tendsto A atTop (𝓝 T) ∧
        ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, hsSq b (A n - T) ≤ ENNReal.ofReal (ε ^ 2)) ∧
    -- product of two Hilbert-Schmidt operators: trace class, product-norm bound
    (∀ {ι : Type*} (b : HilbertBasis ι ℂ E) (A B : E →L[ℂ] E), hsSq b A ≠ ⊤ → hsSq b B ≠ ⊤ →
      IsTraceClass (A * B) ∧ traceNorm (A * B) ≤ ENNReal.ofReal
        (Real.sqrt (hsSq b A).toReal * Real.sqrt (hsSq b B).toReal)) ∧
    -- trace: basis independent, and cyclic with a bounded factor
    (∀ {ι κ : Type*} (b : HilbertBasis ι ℂ E) (c : HilbertBasis κ ℂ E) (T : E →L[ℂ] E),
      IsTraceClass T → QuantumNLS.Ext025B11TracePairing.trace b T = QuantumNLS.Ext025B11TracePairing.trace c T) ∧
    (∀ {ι : Type*} (b : HilbertBasis ι ℂ E) (K T : E →L[ℂ] E), IsTraceClass T →
      QuantumNLS.Ext025B11TracePairing.trace b (K * T) = QuantumNLS.Ext025B11TracePairing.trace b (T * K)) ∧
    -- partial trace over a Hilbert tensor factor
    (∀ (T : HilbertTensor ℂ X Y →L[ℂ] HilbertTensor ℂ X Y) (ht : IsTraceClass T), T.IsPositive →
      (QuantumNLS.Ext025A12PartialTrace.partialTrace T ht).IsPositive ∧
        posTrace (QuantumNLS.Ext025A12PartialTrace.partialTrace T ht) = posTrace T) ∧
    (∀ (T : HilbertTensor ℂ X Y →L[ℂ] HilbertTensor ℂ X Y) (ht : IsTraceClass T),
      traceNorm (QuantumNLS.Ext025A12PartialTrace.partialTrace T ht) ≤ traceNorm T) := by
  refine ⟨fun S T hS hT => (QuantumNLS.Ext025A12Trace.traceIdeal E).add_mem hS hT,
    fun c T hT => (QuantumNLS.Ext025A12Trace.traceIdeal E).smul_mem c hT,
    fun W T V hT => ?_,
    fun b A hfin hA => QuantumNLS.Ext025B6TraceCompletion.trace_complete b A hfin hA,
    fun b W T V => (hs_right b (W * T) V).trans
      (mul_le_mul_of_nonneg_left (hs_left b W T) (by exact zero_le)),
    fun b A hfin hA => QuantumNLS.Ext025B6HilbertSchmidtCompletion.hs_complete b A hfin hA,
    fun b A B hA hB => ⟨QuantumNLS.Ext025STrace.hs_product_traceClass b A B hA hB,
      QuantumNLS.Ext025STrace.hs_product_bound b A B hA hB⟩,
    fun b c T ht => QuantumNLS.Ext025A12Trace.trace_basis_independent b c T ht,
    fun b K T ht => QuantumNLS.Ext025A12Normal.trace_cycle b K T ht,
    fun T ht hT => ⟨QuantumNLS.Ext025A12PartialTrace.partialTrace_positive T ht hT,
      QuantumNLS.Ext025A12PartialTrace.partialTrace_posTrace T ht hT⟩,
    fun T ht => QuantumNLS.Ext025A12PartialTrace.traceNorm_partialTrace_le T ht⟩
  -- two-sided trace-class ideal property (left and right bounded factors)
  exact (QuantumNLS.TraceIdeal.traceNorm_mul_mul_le W T V).trans_lt
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hT) ENNReal.ofReal_lt_top)

end QuantumNLS.Ext025HGP09

#print axioms QuantumNLS.Ext025HGP09.contract_GP09
