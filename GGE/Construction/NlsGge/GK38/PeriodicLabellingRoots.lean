import NlsGge.GK38.PeriodicLabellingSort

/-! # S2: finite analytic orders and certified candidate root values -/
set_option autoImplicit false
open Filter Topology Set Metric
namespace NlsGge.GK38
noncomputable section

theorem counting_order_ne_top38 {f : ℂ → ℂ} {q N : ℕ}
    (h : RootCountingAt38 f q N) (z : ℂ) : analyticOrderAt f z ≠ ⊤ := by
  obtain ⟨w, hw⟩ := h.2.2.1
  apply h.2.1.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (mem_univ w) (mem_univ z)
  rw [(h.2.1 w (mem_univ w)).analyticOrderAt_eq_zero.mpr hw]
  exact ENat.zero_ne_top

theorem counting_mem_zeroMultiset38 {f : ℂ → ℂ} {q N : ℕ}
    (h : RootCountingAt38 f q N) (c : ℂ) (r : ℝ) (z : ℂ) :
    z ∈ Lib.zeroMultiset f (ball c r) ↔ z ∈ ball c r ∧ f z = 0 := by
  rw [Lib.mem_zeroMultiset_ball (h.2.1.mono (subset_univ _))]
  refine and_congr_right fun _ => ?_
  have hz := h.2.1 z (mem_univ z)
  have hnt := counting_order_ne_top38 h z
  have he : (analyticOrderNatAt f z : ℕ∞) = analyticOrderAt f z :=
    Nat.cast_analyticOrderNatAt hnt
  constructor
  · intro hn
    by_contra hz0
    apply hn
    have ho := hz.analyticOrderAt_eq_zero.mpr hz0
    rw [← he] at ho
    exact_mod_cast ho
  · intro hf hn
    have ho : analyticOrderAt f z = 0 := by rw [← he, hn]; rfl
    exact hz.analyticOrderAt_eq_zero.mp ho hf

theorem periodicCandidate_root38 {f : ℂ → ℂ} {N : ℕ}
    (h : RootCountingAt38 f 2 N) (k : ℤ) : f (periodicCandidate38 f N k) = 0 := by
  unfold periodicCandidate38
  split_ifs with hk
  · have hi := periodicCandidate_central_index38 h hk
    have hm : (centralRoots f N).getD (k + 2 * (N : ℤ)).toNat 0 ∈ centralRoots f N := by
      rw [List.getD_eq_getElem _ _ hi]
      exact List.getElem_mem hi
    exact ((counting_mem_zeroMultiset38 h 0 (countingRadius38 N) _).mp
      ((sortComplexRoots_mem38 _ _).mp hm)).2
  · have hi := periodicCandidate_far_index38 h hk
    have hm : (smallRoots f (k / 2)).getD (k % 2).toNat 0 ∈ smallRoots f (k / 2) := by
      rw [List.getD_eq_getElem _ _ hi]
      exact List.getElem_mem hi
    exact ((counting_mem_zeroMultiset38 h (countingCenter38 (k / 2)) (Real.pi / 4) _).mp
      ((sortComplexRoots_mem38 _ _).mp hm)).2

theorem criticalCandidate_root38 {f : ℂ → ℂ} {N : ℕ}
    (h : RootCountingAt38 f 1 N) (n : ℤ) : f (criticalCandidate38 f N n) = 0 := by
  unfold criticalCandidate38
  split_ifs with hn
  · have hi := criticalCandidate_central_index38 h hn
    have hm : (centralRoots f N).getD (n + (N : ℤ)).toNat 0 ∈ centralRoots f N := by
      rw [List.getD_eq_getElem _ _ hi]
      exact List.getElem_mem hi
    exact ((counting_mem_zeroMultiset38 h 0 (countingRadius38 N) _).mp
      ((sortComplexRoots_mem38 _ _).mp hm)).2
  · have hi := criticalCandidate_far_index38 h hn
    have hm : (smallRoots f n).getD 0 0 ∈ smallRoots f n := by
      rw [List.getD_eq_getElem _ _ hi]
      exact List.getElem_mem hi
    exact ((counting_mem_zeroMultiset38 h (countingCenter38 n) (Real.pi / 4) _).mp
      ((sortComplexRoots_mem38 _ _).mp hm)).2

end
end NlsGge.GK38
