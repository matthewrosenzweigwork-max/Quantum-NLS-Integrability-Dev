import Mathlib
import QuantumNLS.BulkResponseForm

/-!
# R-8F7E0394 (`CC:F03:deterministic`), stage (I), support: weak sequential compactness in `L²(0,1)`

Source (F03.tex): "The bound (CC:F03:finite-bound) makes the minimizers weakly precompact."
`exists_weak_subseq`: a bounded sequence in the (separable) Hilbert space `L²(0,1)` has a subsequence converging weakly, i.e. `⟨x_{φ n}, ψ⟩ → ⟨x₀, ψ⟩` for all `ψ`
(sequential Banach-Alaoglu in the dual, identified with the space by the Riesz map).
-/

set_option autoImplicit false

open MeasureTheory Filter Topology Set
open scoped ENNReal

noncomputable section

namespace QuantumNLS.WeakSubseq

open QuantumNLS.BulkResponseForm (L2Unit)

theorem exists_weak_subseq (x : ℕ → L2Unit) {M : ℝ} (hM : ∀ n, ‖x n‖ ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ x0 : L2Unit, ∀ ψ : L2Unit,
      Tendsto (fun n => inner ℝ (x (φ n)) ψ) atTop (𝓝 (inner ℝ x0 ψ)) := by
  haveI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  haveI : TopologicalSpace.SeparableSpace L2Unit := by
    have h : TopologicalSpace.SeparableSpace (Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) := inferInstance
    exact h
  let T := InnerProductSpace.toDual ℝ L2Unit
  let a : ℕ → WeakDual ℝ L2Unit := fun n => StrongDual.toWeakDual (T (x n))
  have ha : ∀ n, a n ∈ (WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ L2Unit) M) := by
    intro n
    simp only [mem_preimage, Metric.mem_closedBall, dist_zero_right]
    show ‖T (x n)‖ ≤ M
    rw [LinearIsometryEquiv.norm_map]
    exact hM n
  obtain ⟨a0, -, φ, hφ, hlim⟩ := WeakDual.isSeqCompact_closedBall ℝ L2Unit 0 M ha
  refine ⟨φ, hφ, T.symm (WeakDual.toStrongDual a0), fun ψ => ?_⟩
  have h := (tendsto_iff_forall_eval_tendsto_topDualPairing.1 hlim) ψ
  have e : inner ℝ (T.symm (WeakDual.toStrongDual a0)) ψ = (WeakDual.toStrongDual a0) ψ :=
    InnerProductSpace.toDual_symm_apply
  rw [e]
  exact h

end QuantumNLS.WeakSubseq

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.WeakSubseq.exists_weak_subseq
