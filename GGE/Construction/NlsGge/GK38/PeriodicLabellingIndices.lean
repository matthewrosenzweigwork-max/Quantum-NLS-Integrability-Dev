import NlsGge.GK38.PeriodicLabellingDefs

/-! # S2: every certified candidate index is in range -/
set_option autoImplicit false
open Filter Topology Set Metric
namespace NlsGge.GK38
noncomputable section

theorem sortComplexRoots_length38 (s : Multiset ℂ) :
    (sortComplexRoots38 s).length = s.card := by
  simp [sortComplexRoots38]

theorem periodicCandidate_central_index38 {f : ℂ → ℂ} {N : ℕ}
    (h : RootCountingAt38 f 2 N) {k : ℤ}
    (hk : -(2 * (N : ℤ)) ≤ k ∧ k ≤ 2 * (N : ℤ) + 1) :
    (k + 2 * (N : ℤ)).toNat < (centralRoots f N).length := by
  rcases h with ⟨_, _, _, _, _, hc, _⟩
  rw [centralRoots, sortComplexRoots_length38, hc]
  omega

theorem periodicCandidate_far_index38 {f : ℂ → ℂ} {N : ℕ}
    (h : RootCountingAt38 f 2 N) {k : ℤ}
    (hk : ¬ (-(2 * (N : ℤ)) ≤ k ∧ k ≤ 2 * (N : ℤ) + 1)) :
    (k % 2).toNat < (smallRoots f (k / 2)).length := by
  rcases h with ⟨_, _, _, _, hs, _, _⟩
  have hfar : (N : ℤ) < |k / 2| := by
    by_contra h
    have hab := abs_le.mp (not_lt.mp h)
    omega
  rw [smallRoots, sortComplexRoots_length38, hs _ hfar]
  have hlo : 0 ≤ k % 2 := Int.emod_nonneg k (by norm_num)
  have hhi : k % 2 < 2 := Int.emod_lt_of_pos k (by norm_num)
  omega

theorem criticalCandidate_central_index38 {f : ℂ → ℂ} {N : ℕ}
    (h : RootCountingAt38 f 1 N) {n : ℤ}
    (hn : -(N : ℤ) ≤ n ∧ n ≤ (N : ℤ)) :
    (n + (N : ℤ)).toNat < (centralRoots f N).length := by
  rcases h with ⟨_, _, _, _, _, hc, _⟩
  rw [centralRoots, sortComplexRoots_length38, hc]
  omega

theorem criticalCandidate_far_index38 {f : ℂ → ℂ} {N : ℕ}
    (h : RootCountingAt38 f 1 N) {n : ℤ}
    (hn : ¬ (-(N : ℤ) ≤ n ∧ n ≤ (N : ℤ))) :
    0 < (smallRoots f n).length := by
  rcases h with ⟨_, _, _, _, hs, _, _⟩
  have hfar : (N : ℤ) < |n| := by
    by_contra h
    have hab := abs_le.mp (not_lt.mp h)
    omega
  rw [smallRoots, sortComplexRoots_length38, hs _ hfar]
  norm_num

/-- Euclidean division pairs negative indices with the intended negative lattice disc. -/
theorem periodic_index_pair38 (n : ℤ) :
    (2 * n) / 2 = n ∧ (2 * n + 1) / 2 = n ∧
      (2 * n) % 2 = 0 ∧ (2 * n + 1) % 2 = 1 := by omega

theorem periodic_negative_index_probe38 :
    (-2 : ℤ) / 2 = -1 ∧ (-1 : ℤ) / 2 = -1 ∧
      (-2 : ℤ) % 2 = 0 ∧ (-1 : ℤ) % 2 = 1 := by norm_num

end
end NlsGge.GK38
