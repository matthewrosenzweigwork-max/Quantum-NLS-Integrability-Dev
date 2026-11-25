import QuantumNLS.Ext025HGP09
/-! integrator-authored trusted spec for EXT-025 contract_GP09 (contract ACCEPT): headline statement(s) copied verbatim from Ext025HGP09 (QuantumNLS.Ext025HGP09). -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Filter Topology
open scoped InnerProductSpace ENNReal ComplexOrder
open QuantumNLS.TraceClass QuantumNLS.TraceIdeal QuantumNLS.TensorCarrier
namespace QuantumNLS.X25GP09Spec
open QuantumNLS.Ext025HGP09


set_option maxHeartbeats 8000000 in
theorem contract_GP09_spec {E X Y : Type*}
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
  exact QuantumNLS.Ext025HGP09.contract_GP09 

end QuantumNLS.X25GP09Spec
#print axioms QuantumNLS.X25GP09Spec.contract_GP09_spec
