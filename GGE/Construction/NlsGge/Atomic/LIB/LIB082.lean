import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.WeakDual

set_option autoImplicit false
noncomputable section

namespace NlsGge.Atomic.LIB

open Filter Topology

/-- Every norm-bounded sequence in a separable real Hilbert space has a weakly
convergent subsequence, with weak convergence expressed by all real inner-product
pairings. -/
theorem bounded_hilbert_weak_subsequence
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    (u : ℕ → E) (hb : ∃ C : ℝ, ∀ n, ‖u n‖ ≤ C) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ ∃ v : E, ∀ w : E,
      Tendsto (fun n => inner ℝ w (u (s n))) atTop (𝓝 (inner ℝ w v)) := by
  obtain ⟨C, hC⟩ := hb
  have hC_nonneg : 0 ≤ C := le_trans (norm_nonneg (u 0)) (hC 0)
  let f : ℕ → StrongDual ℝ E := fun n => InnerProductSpace.toDual ℝ E (u n)
  let x : ℕ → WeakDual ℝ E := fun n => (f n).toWeakDual
  have hx : ∀ n, x n ∈ WeakDual.toStrongDual ⁻¹'
      Metric.closedBall (0 : StrongDual ℝ E) C := by
    intro n
    change dist (WeakDual.toStrongDual ((f n).toWeakDual)) 0 ≤ C
    rw [StrongDual.toStrongDual_toWeakDual, dist_zero_right]
    calc
      ‖f n‖ = ‖u n‖ := by
        dsimp [f]
        exact (InnerProductSpace.toDual ℝ E).norm_map (u n)
      _ ≤ C := hC n
  have hcompact := WeakDual.isSeqCompact_closedBall (𝕜 := ℝ) (E := E)
      (0 : StrongDual ℝ E) C
  obtain ⟨g, _hg, s, hs, hlim⟩ := hcompact hx
  let v : E := (InnerProductSpace.toDual ℝ E).symm (g.toStrongDual)
  refine ⟨s, hs, v, ?_⟩
  intro w
  have heval := ((WeakDual.eval_continuous (𝕜 := ℝ) w).tendsto g).comp hlim
  have hpair : g w = inner ℝ w v := by
    rw [← WeakDual.toStrongDual_apply]
    rw [real_inner_comm]
    dsimp [v]
    exact (InnerProductSpace.toDual_symm_apply (x := w) (y := g.toStrongDual)).symm
  have heval' : Tendsto (fun n => x (s n) w) atTop (𝓝 (g w)) := by
    change Tendsto (fun n => x (s n) w) atTop (𝓝 (g w)) at heval
    exact heval
  simpa [x, f, InnerProductSpace.toDual_apply_apply, real_inner_comm, hpair] using heval'

end NlsGge.Atomic.LIB
