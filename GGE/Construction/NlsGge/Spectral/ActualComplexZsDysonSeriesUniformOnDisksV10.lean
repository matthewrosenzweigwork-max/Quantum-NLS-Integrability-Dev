import NlsGge.Spectral.ActualComplexZsDysonTermFactorialEntryBoundV9
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import Mathlib.Tactic

set_option autoImplicit false

namespace NlsGge.SpectralFoundations

theorem hasSumUniformlyOn_actualComplexZsDysonSeries_entry
    (u : ℝ → ℂ) (R C : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hU : ∀ s ∈ Set.Icc (0 : ℝ) 2, ‖u s‖ ≤ C)
    (i j : Fin 2) :
    HasSumUniformlyOn
      (fun n : ℕ => fun p : ℂ × ℝ =>
        actualComplexZsDysonTerm u p.1 n p.2 i j)
      (fun p => ∑' n : ℕ, actualComplexZsDysonTerm u p.1 n p.2 i j)
      {p : ℂ × ℝ | ‖p.1‖ ≤ R ∧ p.2 ∈ Set.Icc (0 : ℝ) 2} := by
  let K : ℝ := 2 * (R + C)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hmajorant : Summable (fun n : ℕ => (2 * K) ^ n / (n.factorial : ℝ)) := by
    simpa [K] using
      (NormedSpace.expSeries_div_hasSum_exp (2 * (2 * (R + C)))).summable
  apply HasSumUniformlyOn.of_norm_le_summable hmajorant
  intro n p hp
  rcases hp with ⟨hz, ht⟩
  have hterm := actualComplexZsDysonTerm_entry_factorial_bound
    u p.1 R C hz hR hU hC n p.2 ht i j
  have htPow : p.2 ^ n ≤ (2 : ℝ) ^ n :=
    pow_le_pow_left₀ ht.1 ht.2 n
  have hcoef : 0 ≤ (K ^ n / (n.factorial : ℝ)) := by positivity
  calc
    ‖actualComplexZsDysonTerm u p.1 n p.2 i j‖ ≤
        ((2 * (R + C)) ^ n / (n.factorial : ℝ)) * p.2 ^ n := hterm
    _ ≤ (K ^ n / (n.factorial : ℝ)) * (2 : ℝ) ^ n := by
        dsimp [K] at hcoef ⊢
        exact mul_le_mul_of_nonneg_left htPow (by positivity)
    _ = K ^ n * (2 : ℝ) ^ n / (n.factorial : ℝ) := by ring
    _ = (K * 2) ^ n / (n.factorial : ℝ) := by rw [← mul_pow]
    _ = (2 * K) ^ n / (n.factorial : ℝ) := by rw [mul_comm K 2]

end NlsGge.SpectralFoundations
