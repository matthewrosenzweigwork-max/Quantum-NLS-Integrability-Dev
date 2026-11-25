import NlsGge.GK38.PeriodicLabellingFreeModel

/-! # S2: all free labels, including negative and central indices -/
set_option autoImplicit false
open Filter Topology Set Metric
namespace NlsGge.GK38
noncomputable section

theorem countingCenter_lex_mono38 {i j : ℤ} (hij : i ≤ j) :
    complexLexLE38 (countingCenter38 i) (countingCenter38 j) := by
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact complexLexLE_refl38 _
  · apply complexLexLE_of_re_lt38
    rw [countingCenter_re38, countingCenter_re38]
    apply mul_lt_mul_of_pos_right _ Real.pi_pos
    exact_mod_cast hlt

theorem freePeriodicSeq_mono38 {i j : ℤ} (hij : i ≤ j) :
    complexLexLE38 (freePeriodicSeq38 i) (freePeriodicSeq38 j) :=
  countingCenter_lex_mono38 (by omega)

theorem countingCenter_mem_central_iff38 (N : ℕ) (n : ℤ) :
    countingCenter38 n ∈ ball (0 : ℂ) (countingRadius38 N) ↔ |n| ≤ (N : ℤ) := by
  constructor
  · intro hz
    by_contra hn
    have hc := countingCenter_far_norm38 (lt_of_not_ge hn)
    have hz' : ‖countingCenter38 n‖ < countingRadius38 N := by
      simpa only [mem_ball, dist_zero_right] using hz
    unfold countingRadius38 at hz'
    linarith [Real.pi_pos]
  · intro hn
    have hc := countingCenter_low_norm38 hn
    rw [mem_ball, dist_zero_right]
    unfold countingRadius38
    linarith [Real.pi_pos]

theorem freePeriodicSeq_window_multiset38 (N : ℕ) :
    (Finset.Icc (-(2 * (N : ℤ))) (2 * (N : ℤ) + 1)).val.map freePeriodicSeq38 =
      Lib.zeroMultiset (perChar 0) (ball (0 : ℂ) (countingRadius38 N)) := by
  apply rootEnumeration_window_multiset38 (free_periodic_counting38 (N := 1) (by norm_num))
    freePeriodicSeq_enumeration38
  intro k
  rw [freePeriodicSeq38, countingCenter_mem_central_iff38]
  simp only [Finset.mem_Icc]
  constructor
  · intro hq
    have hb := abs_le.mp hq
    omega
  · intro hk
    apply abs_le.mpr
    omega

theorem freeCriticalSeq_window_multiset38 (N : ℕ) :
    (Finset.Icc (-(N : ℤ)) (N : ℤ)).val.map countingCenter38 =
      Lib.zeroMultiset (deriv (discrim 0)) (ball (0 : ℂ) (countingRadius38 N)) := by
  apply rootEnumeration_window_multiset38 (free_critical_counting38 (N := 1) (by norm_num))
    freeCriticalSeq_enumeration38
  intro k
  rw [countingCenter_mem_central_iff38, Finset.mem_Icc]
  exact abs_le

theorem lamSeq_zero38 (k : ℤ) : lamSeq 0 k = countingCenter38 (k / 2) := by
  let N : ℕ := k.natAbs + 1
  have hN : 0 < N := Nat.succ_pos _
  have hk : -(2 * (N : ℤ)) ≤ k ∧ k ≤ 2 * (N : ℤ) + 1 := by
    have hab : |k| = (k.natAbs : ℤ) := (Int.natCast_natAbs k).symm
    have hb := abs_le.mp (show |k| ≤ (N : ℤ) by unfold N; omega)
    omega
  rw [lamSeq_eq_candidate38 0 (free_periodic_counting38 hN)]
  apply integerWindow_unique38 _ freePeriodicSeq38
    (fun i j hij => periodicCandidate_mono38 (free_periodic_counting38 hN) hij)
    (fun i j hij => freePeriodicSeq_mono38 hij)
    (-(2 * (N : ℤ))) (2 * (N : ℤ) + 1) _ hk
  rw [periodicCandidate_central_multiset38 (free_periodic_counting38 hN), freePeriodicSeq_window_multiset38]

theorem lamMinus_zero38 (n : ℤ) : lamMinus 0 n = countingCenter38 n := by
  rw [lamMinus, lamSeq_zero38, (periodic_index_pair38 n).1]

theorem lamPlus_zero38 (n : ℤ) : lamPlus 0 n = countingCenter38 n := by
  rw [lamPlus, lamSeq_zero38, (periodic_index_pair38 n).2.1]

theorem lamDot_zero38 (n : ℤ) : lamDot 0 n = countingCenter38 n := by
  let N : ℕ := n.natAbs + 1
  have hN : 0 < N := Nat.succ_pos _
  have hn : -(N : ℤ) ≤ n ∧ n ≤ (N : ℤ) := by
    have hab : |n| = (n.natAbs : ℤ) := (Int.natCast_natAbs n).symm
    exact abs_le.mp (show |n| ≤ (N : ℤ) by unfold N; omega)
  rw [lamDot_eq_candidate38 0 (free_critical_counting38 hN)]
  apply integerWindow_unique38 _ countingCenter38
    (fun i j hij => criticalCandidate_mono38 (free_critical_counting38 hN) hij)
    (fun i j hij => countingCenter_lex_mono38 hij) (-(N : ℤ)) (N : ℤ) _ hn
  rw [criticalCandidate_central_multiset38 (free_critical_counting38 hN), freeCriticalSeq_window_multiset38]

end
end NlsGge.GK38
