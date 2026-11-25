import QuantumNLS.LossSobolev
/-! integrator-authored trusted spec for R-8C922B25 lem:loss, Sobolev forms (review record r16 FULL ACCEPT): headline statement(s) copied verbatim from LossSobolev (QuantumNLS.LossSobolev). -/
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option linter.unusedSectionVars false
open scoped NNReal ContDiff
open Filter Topology Set Metric
noncomputable section
namespace QuantumNLS.R8C92SpecB
open QuantumNLS.LossSobolev
open QuantumNLS.Sobolev QuantumNLS.Loss
variable (L : ℝ) [Fact (0 < L)]

set_option maxHeartbeats 8000000 in
theorem loss_h_to_H_spec (L : ℝ) [Fact (0 < L)] {k : ℕ} (hk : 1 ≤ k) {q S : ℝ≥0} (hq : 0 < q)
    (hS : ((k : ℝ) + 1) * q < S) (hqS : q ≤ S)
    (f : (seqScale L).Y 0 → (fieldScale L).Y 0) (hf : AnalyticOnNhd ℝ f univ)
    (g : (seqScale L).Y S → (fieldScale L).Y S) (hg : Continuous g)
    (hres : ∀ x, (fieldScale L).emb S 0 (nn_zero_le S) (g x) = f ((seqScale L).emb S 0 (nn_zero_le S) x)) :
    ContDiff ℝ ((k : ℕ) : ℕ∞ω) (fun x => (fieldScale L).emb S q hqS (g x)) ∧
      (∀ j ≤ k, ∀ x v, (fieldScale L).emb q 0 (nn_zero_le q)
          (iteratedFDeriv ℝ j (fun x => (fieldScale L).emb S q hqS (g x)) x v) =
        iteratedFDeriv ℝ j (fun x => f ((seqScale L).emb S 0 (nn_zero_le S) x)) x v) ∧
      ∀ K : Set ((seqScale L).Y S), IsCompact K → ∃ V : Set ((seqScale L).Y S), IsOpen V ∧ K ⊆ V ∧ ∃ B : ℝ,
        ∀ x ∈ V, ∀ j ≤ k, ‖iteratedFDeriv ℝ j (fun x => (fieldScale L).emb S q hqS (g x)) x‖ ≤ B := by
  exact QuantumNLS.LossSobolev.loss_h_to_H L hk hq hS hqS f hf g hg hres

set_option maxHeartbeats 8000000 in
theorem loss_H_to_h_spec (L : ℝ) [Fact (0 < L)] {k : ℕ} (hk : 1 ≤ k) {q S : ℝ≥0} (hq : 0 < q)
    (hS : ((k : ℝ) + 1) * q < S) (hqS : q ≤ S)
    (f : (fieldScale L).Y 0 → (seqScale L).Y 0) (hf : AnalyticOnNhd ℝ f univ)
    (g : (fieldScale L).Y S → (seqScale L).Y S) (hg : Continuous g)
    (hres : ∀ x, (seqScale L).emb S 0 (nn_zero_le S) (g x) = f ((fieldScale L).emb S 0 (nn_zero_le S) x)) :
    ContDiff ℝ ((k : ℕ) : ℕ∞ω) (fun x => (seqScale L).emb S q hqS (g x)) ∧
      (∀ j ≤ k, ∀ x v, (seqScale L).emb q 0 (nn_zero_le q)
          (iteratedFDeriv ℝ j (fun x => (seqScale L).emb S q hqS (g x)) x v) =
        iteratedFDeriv ℝ j (fun x => f ((fieldScale L).emb S 0 (nn_zero_le S) x)) x v) ∧
      ∀ K : Set ((fieldScale L).Y S), IsCompact K → ∃ V : Set ((fieldScale L).Y S), IsOpen V ∧ K ⊆ V ∧ ∃ B : ℝ,
        ∀ x ∈ V, ∀ j ≤ k, ‖iteratedFDeriv ℝ j (fun x => (seqScale L).emb S q hqS (g x)) x‖ ≤ B := by
  exact QuantumNLS.LossSobolev.loss_H_to_h L hk hq hS hqS f hf g hg hres

end QuantumNLS.R8C92SpecB
#print axioms QuantumNLS.R8C92SpecB.loss_h_to_H_spec
#print axioms QuantumNLS.R8C92SpecB.loss_H_to_h_spec
