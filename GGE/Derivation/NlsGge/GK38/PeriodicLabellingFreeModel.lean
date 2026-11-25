import NlsGge.GK38.PeriodicLabellingCanonical
import NlsGge.GK38.PeriodicLabellingFreeWitness

/-! # S2: independent free enumeration and certified free cutoffs -/
set_option autoImplicit false
open Filter Topology Set Metric
namespace NlsGge.GK38
noncomputable section

theorem countingCenter_injective38 : Function.Injective countingCenter38 := by
  intro n m h
  unfold countingCenter38 at h
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have he := mul_right_cancel₀ hp h
  exact_mod_cast he

theorem counting_free_coverage38 (N : ℕ) {z : ℂ} (hz : Complex.sin z = 0) :
    z ∈ ball (0 : ℂ) (countingRadius38 N) ∨
      ∃ n : ℤ, (N : ℤ) < |n| ∧ z ∈ ball (countingCenter38 n) (Real.pi / 4) := by
  obtain ⟨n, rfl⟩ := Complex.sin_eq_zero_iff.mp hz
  by_cases hn : |n| ≤ (N : ℤ)
  · left
    rw [mem_ball, dist_zero_right]
    have hc := countingCenter_low_norm38 hn
    change ‖countingCenter38 n‖ < countingRadius38 N
    unfold countingRadius38
    linarith [Real.pi_pos]
  · exact Or.inr ⟨n, lt_of_not_ge hn, by simp [countingCenter38, Real.pi_pos]⟩

theorem free_periodic_counting38 {N : ℕ} (hN : 0 < N) : RootCountingAt38 (perChar 0) 2 N := by
  refine ⟨hN, analyticOnNhd_perChar_z 0, ?_, counting_zeroMult_support_finite38 0,
    fun n _ => counting_free_small_card38 n, ?_, ?_⟩
  · refine ⟨((Real.pi / 2 : ℝ) : ℂ), ?_⟩
    exact mt (counting_free_zero_iff38 _).mp free_sine_half_ne38
  · rw [counting_free_central_card38]
    omega
  · intro z hz
    exact counting_free_coverage38 N ((counting_free_zero_iff38 z).mp hz)

theorem free_critical_counting38 {N : ℕ} (hN : 0 < N) : RootCountingAt38 (deriv (discrim 0)) 1 N := by
  refine ⟨hN, analyticOnNhd_discrimDeriv38 0, ?_, critical_zeroMult_support_finite38 0,
    fun n _ => critical_free_small_card38 n, ?_, ?_⟩
  · refine ⟨((Real.pi / 2 : ℝ) : ℂ), ?_⟩
    exact mt (critical_free_zero_iff38 _).mp free_sine_half_ne38
  · simpa only [one_mul] using critical_free_central_card38 N
  · intro z hz
    exact counting_free_coverage38 N ((critical_free_zero_iff38 z).mp hz)

def freePeriodicSeq38 (k : ℤ) : ℂ := countingCenter38 (k / 2)

theorem freePeriodicSeq_enumeration38 : RootEnumeration38 (perChar 0) freePeriodicSeq38 := by
  classical
  apply rootEnumeration_of_blocks38 (free_periodic_counting38 (N := 1) (by norm_num))
  · intro k
    apply (counting_free_zero_iff38 _).mpr
    exact Complex.sin_eq_zero_iff.mpr ⟨k / 2, rfl⟩
  · intro z hz
    obtain ⟨n, rfl⟩ := Complex.sin_eq_zero_iff.mp ((counting_free_zero_iff38 z).mp hz)
    refine ⟨{2 * n, 2 * n + 1}, countingCenter38 n, Real.pi / 4,
      by simp only [countingCenter38, mem_ball, dist_self]; positivity, ?_, ?_⟩
    · intro k hk
      have hq : k / 2 = n := countingCenter_injective38 hk
      have hlo : 0 ≤ k % 2 := Int.emod_nonneg k (by norm_num)
      have hhi : k % 2 < 2 := Int.emod_lt_of_pos k (by norm_num)
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    · have hne : 2 * n ≠ 2 * n + 1 := by omega
      obtain ⟨hd₀, hd₁, _, _⟩ := periodic_index_pair38 n
      rw [counting_free_small_multiset38]
      simp [hne, freePeriodicSeq38, hd₀, hd₁, countingCenter38, Multiset.replicate_succ]

theorem freeCriticalSeq_enumeration38 : RootEnumeration38 (deriv (discrim 0)) countingCenter38 := by
  classical
  apply rootEnumeration_of_blocks38 (free_critical_counting38 (N := 1) (by norm_num))
  · intro k
    apply (critical_free_zero_iff38 _).mpr
    exact Complex.sin_eq_zero_iff.mpr ⟨k, rfl⟩
  · intro z hz
    obtain ⟨n, rfl⟩ := Complex.sin_eq_zero_iff.mp ((critical_free_zero_iff38 z).mp hz)
    refine ⟨{n}, countingCenter38 n, Real.pi / 4, by simp only [countingCenter38, mem_ball, dist_self]; positivity, ?_, ?_⟩
    · intro k hk
      exact Finset.mem_singleton.mpr (countingCenter_injective38 hk)
    · simp only [Finset.singleton_val, Multiset.map_singleton, critical_free_small_multiset38]

end
end NlsGge.GK38
