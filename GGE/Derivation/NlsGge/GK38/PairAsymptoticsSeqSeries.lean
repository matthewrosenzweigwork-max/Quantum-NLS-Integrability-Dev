import NlsGge.GK38.PairAsymptoticsSeqFourier

/-!
# F5: a series bound on finite spectral windows

The series is estimated in a finite-dimensional Euclidean space. No square summability
of the full spectral sequence is assumed here.
-/

set_option autoImplicit false

open Filter Topology MeasureTheory

namespace NlsGge.GK38

noncomputable section

theorem seqSeries38_sum_sq_le (a : ℕ → ℤ → ℂ) (b : ℤ → ℂ) (w : ℕ → ℝ)
    (Q W : ℝ) (hQ : 0 ≤ Q) (hw : ∀ k, 0 ≤ w k) (hws : HasSum w W)
    (hb : ∀ n, HasSum (fun k => a k n) (b n))
    (ha : ∀ k, ∀ T : Finset ℤ, ∑ n ∈ T, ‖a k n‖ ^ 2 ≤ w k ^ 2 * Q)
    (T : Finset ℤ) : ∑ n ∈ T, ‖b n‖ ^ 2 ≤ W ^ 2 * Q := by
  classical
  let e := (PiLp.continuousLinearEquiv 2 ℂ (fun _ : T => ℂ)).symm
  have hv : HasSum (fun k => e (fun n : T => a k n)) (e (fun n : T => b n)) :=
    (Pi.hasSum.mpr (fun n : T => hb n)).map e e.continuous
  have hnorm : ∀ k, ‖e (fun n : T => a k n)‖ ≤ w k * Real.sqrt Q := by
    intro k
    have hs : ‖e (fun n : T => a k n)‖ ^ 2 ≤ w k ^ 2 * Q := by
      rw [EuclideanSpace.norm_sq_eq]
      simpa only [e, PiLp.continuousLinearEquiv_symm_apply, PiLp.toLp_apply,
        Finset.sum_coe_sort T (fun n : ℤ => ‖a k n‖ ^ 2)] using ha k T
    apply le_of_sq_le_sq ?_ (mul_nonneg (hw k) (Real.sqrt_nonneg Q))
    rw [mul_pow, Real.sq_sqrt hQ]
    exact hs
  have hbound := hv.norm_le_of_bounded (hws.mul_right (Real.sqrt Q)) hnorm
  have hs := pow_le_pow_left₀ (norm_nonneg _) hbound 2
  rw [EuclideanSpace.norm_sq_eq, mul_pow, Real.sq_sqrt hQ] at hs
  simpa only [e, PiLp.continuousLinearEquiv_symm_apply, PiLp.toLp_apply,
    Finset.sum_coe_sort T (fun n : ℤ => ‖b n‖ ^ 2)] using hs

end

end NlsGge.GK38
