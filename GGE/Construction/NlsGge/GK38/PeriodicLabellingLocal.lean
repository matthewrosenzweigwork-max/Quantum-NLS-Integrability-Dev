import NlsGge.GK38.PeriodicLabellingSort

/-! # S2: exact multisets supplied by certified candidates -/
set_option autoImplicit false
open Filter Topology Set Metric
namespace NlsGge.GK38
noncomputable section

theorem list_map_range_getD38 (l : List ℂ) (d : ℂ) :
    (List.range l.length).map (fun i => l.getD i d) = l := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.length_map, List.length_range] at hi
    simpa only [List.getElem_map, List.getElem_range] using List.getD_eq_getElem l d hi

theorem map_getD_Icc38 (l : List ℂ) (a b : ℤ) (d : ℂ)
    (h : (b + 1 - a).toNat = l.length) :
    (Finset.Icc a b).val.map (fun k => l.getD (k - a).toNat d) = (l : Multiset ℂ) := by
  rw [Int.Icc_eq_finset_map]
  simp only [Finset.map_val, Multiset.map_map]
  change (Multiset.range (b + 1 - a).toNat).map
    (fun i : ℕ => l.getD ((a + (i : ℤ)) - a).toNat d) = _
  simp only [add_sub_cancel_left, Int.toNat_natCast]
  rw [h]
  change ((List.range l.length).map (fun i => l.getD i d) : Multiset ℂ) = _
  rw [list_map_range_getD38]

theorem periodicCandidate_central_multiset38 {f : ℂ → ℂ} {N : ℕ}
    (h : RootCountingAt38 f 2 N) :
    (Finset.Icc (-(2 * (N : ℤ))) (2 * (N : ℤ) + 1)).val.map (periodicCandidate38 f N) =
      Lib.zeroMultiset f (ball (0 : ℂ) (countingRadius38 N)) := by
  have he : (-(2 * (N : ℤ)) + 2 * (N : ℤ)) = 0 := by ring
  have hlen : ((2 * (N : ℤ) + 1) + 1 - -(2 * (N : ℤ))).toNat = (centralRoots f N).length := by
    rw [centralRoots, sortComplexRoots_length38, h.2.2.2.2.2.1]
    omega
  calc
    _ = (Finset.Icc (-(2 * (N : ℤ))) (2 * (N : ℤ) + 1)).val.map
        (fun k => (centralRoots f N).getD (k - -(2 * (N : ℤ))).toNat 0) := by
      apply Multiset.map_congr rfl
      intro k hk
      have hb : -(2 * (N : ℤ)) ≤ k ∧ k ≤ 2 * (N : ℤ) + 1 := Finset.mem_Icc.mp hk
      simp only [periodicCandidate38, if_pos hb, sub_neg_eq_add]
    _ = (centralRoots f N : Multiset ℂ) := map_getD_Icc38 _ _ _ _ hlen
    _ = _ := sortComplexRoots_multiset38 _

theorem criticalCandidate_central_multiset38 {f : ℂ → ℂ} {N : ℕ}
    (h : RootCountingAt38 f 1 N) :
    (Finset.Icc (-(N : ℤ)) (N : ℤ)).val.map (criticalCandidate38 f N) =
      Lib.zeroMultiset f (ball (0 : ℂ) (countingRadius38 N)) := by
  have hlen : ((N : ℤ) + 1 - -(N : ℤ)).toNat = (centralRoots f N).length := by
    rw [centralRoots, sortComplexRoots_length38, h.2.2.2.2.2.1]
    omega
  calc
    _ = (Finset.Icc (-(N : ℤ)) (N : ℤ)).val.map
        (fun k => (centralRoots f N).getD (k - -(N : ℤ)).toNat 0) := by
      apply Multiset.map_congr rfl
      intro k hk
      have hb : -(N : ℤ) ≤ k ∧ k ≤ (N : ℤ) := Finset.mem_Icc.mp hk
      simp only [criticalCandidate38, if_pos hb, sub_neg_eq_add]
    _ = (centralRoots f N : Multiset ℂ) := map_getD_Icc38 _ _ _ _ hlen
    _ = _ := sortComplexRoots_multiset38 _

theorem periodicCandidate_small_multiset38 {f : ℂ → ℂ} {N : ℕ}
    (h : RootCountingAt38 f 2 N) {n : ℤ} (hn : (N : ℤ) < |n|) :
    (periodicCandidate38 f N (2 * n) ::ₘ periodicCandidate38 f N (2 * n + 1) ::ₘ 0) =
      Lib.zeroMultiset f (ball (countingCenter38 n) (Real.pi / 4)) := by
  have hlen : (smallRoots f n).length = 2 := by
    rw [smallRoots, sortComplexRoots_length38, h.2.2.2.2.1 n hn]
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  have hfar₀ : ¬ (-(2 * (N : ℤ)) ≤ 2 * n ∧ 2 * n ≤ 2 * (N : ℤ) + 1) := by
    intro hbad
    have hn' : |n| ≤ (N : ℤ) := abs_le.mpr (by omega)
    omega
  have hfar₁ : ¬ (-(2 * (N : ℤ)) ≤ 2 * n + 1 ∧ 2 * n + 1 ≤ 2 * (N : ℤ) + 1) := by
    intro hbad
    have hn' : |n| ≤ (N : ℤ) := abs_le.mpr (by omega)
    omega
  obtain ⟨hd₀, hd₁, hm₀, hm₁⟩ := periodic_index_pair38 n
  simp only [periodicCandidate38, if_neg hfar₀, if_neg hfar₁, hd₀, hd₁, hm₀, hm₁,
    Int.toNat_zero, Int.toNat_one, hab, List.getD_cons_zero, List.getD_cons_succ]
  have hs := sortComplexRoots_multiset38 (Lib.zeroMultiset f (ball (countingCenter38 n) (Real.pi / 4)))
  change (smallRoots f n : Multiset ℂ) = _ at hs
  rw [hab] at hs
  exact hs

theorem criticalCandidate_small_multiset38 {f : ℂ → ℂ} {N : ℕ}
    (h : RootCountingAt38 f 1 N) {n : ℤ} (hn : (N : ℤ) < |n|) :
    ({criticalCandidate38 f N n} : Multiset ℂ) =
      Lib.zeroMultiset f (ball (countingCenter38 n) (Real.pi / 4)) := by
  have hlen : (smallRoots f n).length = 1 := by
    rw [smallRoots, sortComplexRoots_length38, h.2.2.2.2.1 n hn]
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hlen
  have hfar : ¬ (-(N : ℤ) ≤ n ∧ n ≤ (N : ℤ)) := by
    intro hbad
    exact (not_le.mpr hn) (abs_le.mpr hbad)
  simp only [criticalCandidate38, if_neg hfar, ha, List.getD_cons_zero]
  have hs := sortComplexRoots_multiset38 (Lib.zeroMultiset f (ball (countingCenter38 n) (Real.pi / 4)))
  change (smallRoots f n : Multiset ℂ) = _ at hs
  rw [ha] at hs
  exact hs

end
end NlsGge.GK38
