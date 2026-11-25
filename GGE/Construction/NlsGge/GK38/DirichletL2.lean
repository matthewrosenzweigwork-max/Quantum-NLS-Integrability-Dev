import NlsGge.GK38.DirichletLabels
import NlsGge.GK38.PeriodicAsymptoticsLocal
import NlsGge.GK38.PeriodicAsymptoticsL2

/-! # D1: full complex locally uniform square summability

Book Proposition 5.3, using the accepted elementary inverse-sine estimate.
No continuity of a sorted label and no uniformly small tail is asserted. -/
set_option autoImplicit false
open Filter Topology Set Metric
namespace NlsGge.GK38
noncomputable section

theorem muSeq_local_bounds38 (φ₀ : PotPair) :
  ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ ∃ N : ℕ, 0 < N ∧
    ∀ φ : PotPair, φ ∈ U → ∀ n : ℤ,
      ‖muSeq φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ 2 * (N : ℝ) * Real.pi + Real.pi / 4 ∧
      ((N : ℤ) < |n| → ‖muSeq φ n - (n : ℂ) * (Real.pi : ℂ)‖ < Real.pi / 4) := by
  obtain ⟨U, hU, N, hN⟩ := dirichlet_counting_lemma38 φ₀
  refine ⟨U, hU, N, (hN φ₀ (mem_of_mem_nhds hU)).1, fun φ hφ n => ?_⟩
  rw [muSeq_eq_candidate38 φ (hN φ hφ)]
  simpa only [countingCenter38] using criticalCandidate_shift_bound38 (hN φ hφ) n

/-- Summability and a nonnegative bound hold on one common neighbourhood before the potential. -/
theorem muSeq_local_l2_38 (φ₀ : PotPair) :
  ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ ∃ C : ℝ, 0 ≤ C ∧
    ∀ φ : PotPair, φ ∈ U →
      Summable (fun n : ℤ => ‖muSeq φ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) ∧
      (∑' n : ℤ, ‖muSeq φ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) ≤ C := by
  obtain ⟨U, hU, N, _hN, hloc⟩ := muSeq_local_bounds38 φ₀
  let b : ℝ := 2 * (N : ℝ) * Real.pi + Real.pi / 4
  have hb : 0 ≤ b := by dsimp [b]; positivity
  let R : ℝ := ‖φ₀‖ + 1
  obtain ⟨B, hB, h⟩ := dirichletChar_seq_l2_38 R b
  let C : ℝ := ((Finset.Icc (-(N : ℤ)) (N : ℤ)).card : ℝ) * b ^ 2 +
    (Real.pi / 2 + 1) ^ 2 * B
  refine ⟨U ∩ ball φ₀ 1, inter_mem hU (ball_mem_nhds φ₀ zero_lt_one),
    C, by dsimp [C]; positivity, fun φ hφ => ?_⟩
  have hR : ‖φ‖ ≤ R := by
    have hdist : ‖φ - φ₀‖ < 1 := mem_ball_iff_norm.mp hφ.2
    have hn : ‖φ‖ ≤ ‖φ - φ₀‖ + ‖φ₀‖ := by
      simpa only [sub_add_cancel] using norm_add_le (φ - φ₀) φ₀
    dsimp [R]
    linarith
  have hshift (n : ℤ) := (hloc φ hφ.1 n).1
  obtain ⟨hs, ht⟩ := h φ hR (muSeq φ) hshift
  have hsine : Summable (fun n : ℤ => ‖Complex.sin (muSeq φ n)‖ ^ 2) := by
    simpa only [muSeq_root38, zero_sub, norm_neg] using hs
  have htsine : (∑' n : ℤ, ‖Complex.sin (muSeq φ n)‖ ^ 2) ≤ B := by
    simpa only [muSeq_root38, zero_sub, norm_neg] using ht
  exact localized_sine_l2_38 (muSeq φ) N b B hb hB hshift
    (fun n hn => ((hloc φ hφ.1 n).2 hn).le) hsine htsine

/-- Exact D1 contract: local bounded complete square sums, including the Summable prerequisite. -/
theorem muSeq_l2 (φ₀ : PotPair) :
    IsLocUnifL2Seq (fun (φ : PotPair) (n : ℤ) => muSeq φ n - (n : ℂ) * (Real.pi : ℂ)) φ₀ := by
  obtain ⟨U, hU, C, _hC, h⟩ := muSeq_local_l2_38 φ₀
  exact ⟨U, hU, C, h⟩

/-- Pointwise square summability is proved before product and real-tsum consumers. -/
theorem muSeq_summable38 (φ : PotPair) :
    Summable (fun n : ℤ => ‖muSeq φ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) := by
  obtain ⟨U, hU, C, _hC, h⟩ := muSeq_local_l2_38 φ
  exact (h φ (mem_of_mem_nhds hU)).1

end
end NlsGge.GK38
