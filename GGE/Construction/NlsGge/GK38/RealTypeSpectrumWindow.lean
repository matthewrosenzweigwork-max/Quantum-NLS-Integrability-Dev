import NlsGge.GK38.PeriodicLabelling

/-! # S5: genuinely certified prescribed counting windows

GK book I.7 real deformation route. A requested lower bound is realized
using F5 and periodic_counting_at38, rather than cutoff upward validity.
-/
set_option autoImplicit false
open Filter Topology Set Metric
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem periodic_large_counting_cutoff38 (φ₀ : PotPair) (L : ℕ) :
    ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ ∃ N : ℕ, L ≤ N ∧
      ∀ φ ∈ U, RootCountingAt38 (perChar φ) 2 N := by
  obtain ⟨U, hU, R, herr⟩ := perChar_asymp φ₀ 1 (by norm_num)
  obtain ⟨K, hK⟩ := exists_nat_gt (R / Real.pi)
  let N := max (K + 1) L
  have hN : 0 < N := lt_of_lt_of_le (Nat.succ_pos K) (le_max_left _ _)
  have hRN : R ≤ countingRadius38 N := by
    have h := (div_lt_iff₀ Real.pi_pos).mp hK
    have hKN : (K : ℝ) < (N : ℝ) := by exact_mod_cast lt_of_lt_of_le (Nat.lt_succ_self K) (le_max_left _ _)
    unfold countingRadius38
    nlinarith [Real.pi_pos]
  refine ⟨U, hU, N, le_max_right _ _, fun φ hφ => ?_⟩
  have hcmp : ∀ z : ℂ, countingRadius38 N ≤ ‖z‖ →
      (∀ n : ℤ, Real.pi / 4 ≤ ‖z - countingCenter38 n‖) →
      ‖perChar φ z - perChar 0 z‖ < ‖perChar 0 z‖ := by
    intro z hz hsep
    apply counting_strict_comparison38
    · simpa only [one_mul] using herr φ hφ z (hRN.trans hz) hsep
    · exact hsep
  have hsphere := counting_radius_mem_sphere38 N
  have hnorm : countingRadius38 N ≤ ‖(countingRadius38 N : ℂ)‖ := by
    simp [Complex.norm_real, abs_of_pos (countingRadius_pos38 N)]
  have hsep := counting_central_sphere_separated38 N hsphere
  obtain ⟨hs, hc, he⟩ := periodic_counting_at38 φ N hcmp
  refine ⟨hN, analyticOnNhd_perChar_z φ,
    ⟨_, counting_ne_zero_of_comparison38 (hcmp _ hnorm hsep)⟩,
    counting_zeroMult_support_finite38 φ, hs, ?_, he⟩
  omega

theorem periodic_real_fixed_window38 (u₀ : PhysicalL2) (k : ℤ) :
    ∃ U : Set PhysicalL2, U ∈ 𝓝 u₀ ∧ ∃ N : ℕ, 0 < N ∧
      -(2 * (N : ℤ)) ≤ k ∧ k ≤ 2 * (N : ℤ) + 1 ∧
      ∀ u ∈ U, RootCountingAt38 (perChar (realSlice u)) 2 N := by
  obtain ⟨V, hV, N, hN, h⟩ := periodic_large_counting_cutoff38 (realSlice u₀) (k.natAbs + 1)
  refine ⟨realSlice ⁻¹' V, continuous_realSlice.continuousAt.preimage_mem_nhds hV,
    N, (h _ (mem_of_mem_nhds hV)).1, ?_, ?_, fun u hu => h _ hu⟩
  · have hk : -k ≤ (k.natAbs : ℤ) := by simpa using (Int.le_natAbs (a := -k))
    omega
  · have hk : k ≤ (k.natAbs : ℤ) := Int.le_natAbs
    omega

end
end NlsGge.GK38
