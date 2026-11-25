import NlsGge.GK38.PeriodicAsymptoticsMatrixSine
import NlsGge.GK38.GradFundamentalSpectralSeq

/-! # S3: sampled sine square sums at the actual characteristic and critical roots

Constants are chosen before the potential and before the sampled full sequence.
Finite windows precede summability, including in the scalar K1 specialization. -/
set_option autoImplicit false
open scoped Matrix.Norms.Elementwise
namespace NlsGge.GK38
noncomputable section

/-- F5 and the direct matrix estimate bound any uniformly shifted characteristic-root sequence. -/
theorem perChar_roots_sine_l2_38 (R c : ℝ) (hc : 0 ≤ c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : PotPair, ‖φ‖ ≤ R → ∀ υ : ℤ → ℂ,
      (∀ n : ℤ, ‖υ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ c) →
      (∀ n : ℤ, perChar φ (υ n) = 0) →
      Summable (fun n : ℤ => ‖Complex.sin (υ n)‖ ^ 2) ∧
        (∑' n : ℤ, ‖Complex.sin (υ n)‖ ^ 2) ≤ C := by
  obtain ⟨B, hB⟩ := fundPair_seq_l2 R c
  let A : ℝ := Real.exp c * (Real.exp c + 1)
  refine ⟨A ^ 2 * max B 0, by positivity, fun φ hφ υ hshift hroot => ?_⟩
  obtain ⟨hs, ht⟩ := hB φ hφ υ hshift ⟨1, zero_le_one, le_rfl⟩
  have hpoint (n : ℤ) : ‖Complex.sin (υ n)‖ ^ 2 ≤
      A ^ 2 * ‖fundPair φ (υ n) ⟨1, zero_le_one, le_rfl⟩ -
        freeFund (υ n) ⟨1, zero_le_one, le_rfl⟩‖ ^ 2 := by
    have him : |(υ n).im| ≤ c := by
      have he : (υ n - (n : ℂ) * (Real.pi : ℂ)).im = (υ n).im := by simp
      rw [← he]
      exact (Complex.abs_im_le_norm _).trans (hshift n)
    have h := perChar_zero_sine_le38 φ (υ n) c hc him (hroot n)
    simpa only [A, mul_pow] using pow_le_pow_left₀ (norm_nonneg _) h 2
  have hfin (T : Finset ℤ) : ∑ n ∈ T, ‖Complex.sin (υ n)‖ ^ 2 ≤ A ^ 2 * max B 0 := by
    calc _ ≤ ∑ n ∈ T, A ^ 2 * ‖fundPair φ (υ n) ⟨1, zero_le_one, le_rfl⟩ -
          freeFund (υ n) ⟨1, zero_le_one, le_rfl⟩‖ ^ 2 := Finset.sum_le_sum (fun n _ => hpoint n)
      _ = A ^ 2 * (∑ n ∈ T, ‖fundPair φ (υ n) ⟨1, zero_le_one, le_rfl⟩ -
          freeFund (υ n) ⟨1, zero_le_one, le_rfl⟩‖ ^ 2) := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        ((hs.sum_le_tsum T (fun n _ => sq_nonneg _)).trans (ht.trans (le_max_left _ _)))
        (sq_nonneg _)
  have hsine := summable_of_sum_le (fun n : ℤ => sq_nonneg ‖Complex.sin (υ n)‖) hfin
  exact ⟨hsine, hsine.tsum_le_of_sum_le hfin⟩

/-- The accepted scalar K1 sequence estimate gives the sine square sum at critical roots. -/
theorem critical_roots_sine_l2_38 (R c : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : PotPair, ‖φ‖ ≤ R → ∀ υ : ℤ → ℂ,
      (∀ n : ℤ, ‖υ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ c) →
      (∀ n : ℤ, deriv (discrim φ) (υ n) = 0) →
      Summable (fun n : ℤ => ‖Complex.sin (υ n)‖ ^ 2) ∧
        (∑' n : ℤ, ‖Complex.sin (υ n)‖ ^ 2) ≤ C := by
  obtain ⟨B, hB, h⟩ := discrimDeriv_l2 R c
  refine ⟨B / 4, by positivity, fun φ hφ υ hshift hroot => ?_⟩
  have hfin (T : Finset ℤ) : ∑ n ∈ T, ‖Complex.sin (υ n)‖ ^ 2 ≤ B / 4 := by
    have hh := (h φ hφ υ hshift).1 T
    have he (n : ℤ) : ‖deriv (discrim φ) (υ n) + 2 * Complex.sin (υ n)‖ ^ 2 =
        4 * ‖Complex.sin (υ n)‖ ^ 2 := by
      rw [hroot n, zero_add, norm_mul, Complex.norm_two]
      ring
    simp only [he, ← Finset.mul_sum] at hh
    linarith
  have hs := summable_of_sum_le (fun n : ℤ => sq_nonneg ‖Complex.sin (υ n)‖) hfin
  exact ⟨hs, hs.tsum_le_of_sum_le hfin⟩

end
end NlsGge.GK38
