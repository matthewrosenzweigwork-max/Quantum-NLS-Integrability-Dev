import NlsGge.GK38.PeriodicLabellingRegions

/-! # S2: global real/imaginary Lex order of certified candidates -/
set_option autoImplicit false
open Filter Topology Set Metric
namespace NlsGge.GK38
noncomputable section

theorem complexLexLE_refl38 (z : ℂ) : complexLexLE38 z z := le_refl _

theorem complexLexLE_of_re_lt38 {z w : ℂ} (h : z.re < w.re) : complexLexLE38 z w :=
  (complexLexLE_iff38 z w).mpr (Or.inl h)

theorem sortComplexRoots_getD_mono38 (s : Multiset ℂ) {i j : ℕ}
    (hi : i < (sortComplexRoots38 s).length) (hj : j < (sortComplexRoots38 s).length)
    (hij : i ≤ j) :
    complexLexLE38 ((sortComplexRoots38 s).getD i 0) ((sortComplexRoots38 s).getD j 0) := by
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj]
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact complexLexLE_refl38 _
  · exact (sortComplexRoots_pairwise38 s).rel_getElem_of_lt hi hj hlt

theorem periodicCandidate_mono38 {f : ℂ → ℂ} {N : ℕ}
    (h : RootCountingAt38 f 2 N) {i j : ℤ} (hij : i ≤ j) :
    complexLexLE38 (periodicCandidate38 f N i) (periodicCandidate38 f N j) := by
  by_cases hi : periodicCentralIndex38 N i <;> by_cases hj : periodicCentralIndex38 N j
  · have hii := periodicCandidate_central_index38 h hi
    have hji := periodicCandidate_central_index38 h hj
    have hi' := hi
    have hj' := hj
    unfold periodicCentralIndex38 at hi' hj'
    simpa only [periodicCandidate38, ite_eq_left hi', ite_eq_left hj', centralRoots] using
      sortComplexRoots_getD_mono38 _ hii hji (by omega)
  · have hm : (N : ℤ) < j / 2 := by
      unfold periodicCentralIndex38 at hi hj
      omega
    exact complexLexLE_of_re_lt38 (counting_central_small_re_lt38 hm
      (periodicCandidate_central_mem38 h hi) (periodicCandidate_far_mem38 h hj))
  · have hm : i / 2 < -(N : ℤ) := by
      unfold periodicCentralIndex38 at hi hj
      omega
    exact complexLexLE_of_re_lt38 (counting_small_central_re_lt38 hm
      (periodicCandidate_far_mem38 h hi) (periodicCandidate_central_mem38 h hj))
  · have hq : i / 2 ≤ j / 2 := by omega
    rcases eq_or_lt_of_le hq with heq | hlt
    · have hii := periodicCandidate_far_index38 h hi
      have hji := periodicCandidate_far_index38 h hj
      rw [← heq] at hji
      have hi' := hi
      have hj' := hj
      unfold periodicCentralIndex38 at hi' hj'
      simp only [periodicCandidate38, ite_eq_right hi', ite_eq_right hj', ← heq]
      apply sortComplexRoots_getD_mono38 _ hii hji
      have hlo₁ : 0 ≤ i % 2 := Int.emod_nonneg i (by norm_num)
      have hlo₂ : 0 ≤ j % 2 := Int.emod_nonneg j (by norm_num)
      have hhi₁ : i % 2 < 2 := Int.emod_lt_of_pos i (by norm_num)
      have hhi₂ : j % 2 < 2 := Int.emod_lt_of_pos j (by norm_num)
      omega
    · exact complexLexLE_of_re_lt38 (counting_small_blocks_re_lt38 hlt
        (periodicCandidate_far_mem38 h hi) (periodicCandidate_far_mem38 h hj))

theorem criticalCandidate_mono38 {f : ℂ → ℂ} {N : ℕ}
    (h : RootCountingAt38 f 1 N) {i j : ℤ} (hij : i ≤ j) :
    complexLexLE38 (criticalCandidate38 f N i) (criticalCandidate38 f N j) := by
  by_cases hi : criticalCentralIndex38 N i <;> by_cases hj : criticalCentralIndex38 N j
  · have hii := criticalCandidate_central_index38 h hi
    have hji := criticalCandidate_central_index38 h hj
    have hi' := hi
    have hj' := hj
    unfold criticalCentralIndex38 at hi' hj'
    simpa only [criticalCandidate38, ite_eq_left hi', ite_eq_left hj', centralRoots] using
      sortComplexRoots_getD_mono38 _ hii hji (by omega)
  · have hm : (N : ℤ) < j := by
      unfold criticalCentralIndex38 at hi hj
      omega
    exact complexLexLE_of_re_lt38 (counting_central_small_re_lt38 hm
      (criticalCandidate_central_mem38 h hi) (criticalCandidate_far_mem38 h hj))
  · have hm : i < -(N : ℤ) := by
      unfold criticalCentralIndex38 at hi hj
      omega
    exact complexLexLE_of_re_lt38 (counting_small_central_re_lt38 hm
      (criticalCandidate_far_mem38 h hi) (criticalCandidate_central_mem38 h hj))
  · rcases eq_or_lt_of_le hij with rfl | hlt
    · exact complexLexLE_refl38 _
    · exact complexLexLE_of_re_lt38 (counting_small_blocks_re_lt38 hlt
        (criticalCandidate_far_mem38 h hi) (criticalCandidate_far_mem38 h hj))

end
end NlsGge.GK38
