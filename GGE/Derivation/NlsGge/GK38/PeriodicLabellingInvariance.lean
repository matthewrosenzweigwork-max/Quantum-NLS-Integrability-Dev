import NlsGge.GK38.PeriodicLabellingWindowSort

/-! # S2: every certified cutoff gives the same global candidates -/
set_option autoImplicit false
open Filter Topology Set Metric
namespace NlsGge.GK38
noncomputable section

theorem periodicCandidate_invariant_of_le38 {f : ℂ → ℂ} {N M : ℕ}
    (hN : RootCountingAt38 f 2 N) (hM : RootCountingAt38 f 2 M) (hNM : N ≤ M) :
    periodicCandidate38 f N = periodicCandidate38 f M := by
  funext k
  by_cases hk : periodicCentralIndex38 M k
  · apply integerWindow_unique38 _ _
      (fun i j hij => periodicCandidate_mono38 hN hij)
      (fun i j hij => periodicCandidate_mono38 hM hij)
      (-(2 * (M : ℤ))) (2 * (M : ℤ) + 1) _ hk
    rw [periodicCandidate_larger_multiset38 hN hNM, periodicCandidate_central_multiset38 hM]
  · have hkN : ¬ periodicCentralIndex38 N k := by
      unfold periodicCentralIndex38 at *
      omega
    unfold periodicCentralIndex38 at hk hkN
    simp only [periodicCandidate38, ite_eq_right hk, ite_eq_right hkN]

theorem criticalCandidate_invariant_of_le38 {f : ℂ → ℂ} {N M : ℕ}
    (hN : RootCountingAt38 f 1 N) (hM : RootCountingAt38 f 1 M) (hNM : N ≤ M) :
    criticalCandidate38 f N = criticalCandidate38 f M := by
  funext k
  by_cases hk : criticalCentralIndex38 M k
  · apply integerWindow_unique38 _ _
      (fun i j hij => criticalCandidate_mono38 hN hij)
      (fun i j hij => criticalCandidate_mono38 hM hij)
      (-(M : ℤ)) (M : ℤ) _ hk
    rw [criticalCandidate_larger_multiset38 hN hNM, criticalCandidate_central_multiset38 hM]
  · have hkN : ¬ criticalCentralIndex38 N k := by
      unfold criticalCentralIndex38 at *
      omega
    unfold criticalCentralIndex38 at hk hkN
    simp only [criticalCandidate38, ite_eq_right hk, ite_eq_right hkN]

theorem periodicCandidate_cutoff_invariant38 {f : ℂ → ℂ} {N M : ℕ}
    (hN : RootCountingAt38 f 2 N) (hM : RootCountingAt38 f 2 M) :
    periodicCandidate38 f N = periodicCandidate38 f M := by
  have hmax : RootCountingAt38 f 2 (max N M) := by
    rcases le_total N M with h | h
    · simpa only [max_eq_right h] using hM
    · simpa only [max_eq_left h] using hN
  calc
    _ = periodicCandidate38 f (max N M) := periodicCandidate_invariant_of_le38 hN hmax (le_max_left _ _)
    _ = _ := (periodicCandidate_invariant_of_le38 hM hmax (le_max_right _ _)).symm

theorem criticalCandidate_cutoff_invariant38 {f : ℂ → ℂ} {N M : ℕ}
    (hN : RootCountingAt38 f 1 N) (hM : RootCountingAt38 f 1 M) :
    criticalCandidate38 f N = criticalCandidate38 f M := by
  have hmax : RootCountingAt38 f 1 (max N M) := by
    rcases le_total N M with h | h
    · simpa only [max_eq_right h] using hM
    · simpa only [max_eq_left h] using hN
  calc
    _ = criticalCandidate38 f (max N M) := criticalCandidate_invariant_of_le38 hN hmax (le_max_left _ _)
    _ = _ := (criticalCandidate_invariant_of_le38 hM hmax (le_max_right _ _)).symm

end
end NlsGge.GK38
