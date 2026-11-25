import NlsGge.GK38.PeriodicLabellingRoots
import NlsGge.GK38.PeriodicLabellingGeometry

/-! # S2: the candidate value stays in its selected counting block -/
set_option autoImplicit false
open Filter Topology Set Metric
namespace NlsGge.GK38
noncomputable section

def periodicCentralIndex38 (N : ℕ) (k : ℤ) : Prop :=
  -(2 * (N : ℤ)) ≤ k ∧ k ≤ 2 * (N : ℤ) + 1

def criticalCentralIndex38 (N : ℕ) (n : ℤ) : Prop := -(N : ℤ) ≤ n ∧ n ≤ (N : ℤ)

theorem periodic_far_quotient38 {N : ℕ} {k : ℤ} (hk : ¬ periodicCentralIndex38 N k) :
    (N : ℤ) < |k / 2| := by
  by_contra h
  have hab := abs_le.mp (not_lt.mp h)
  unfold periodicCentralIndex38 at hk
  omega

theorem critical_far_index38 {N : ℕ} {n : ℤ} (hn : ¬ criticalCentralIndex38 N n) :
    (N : ℤ) < |n| := by
  by_contra h
  have hab := abs_le.mp (not_lt.mp h)
  exact hn hab

theorem periodicCandidate_central_mem38 {f : ℂ → ℂ} {N : ℕ}
    (h : RootCountingAt38 f 2 N) {k : ℤ} (hk : periodicCentralIndex38 N k) :
    periodicCandidate38 f N k ∈ ball (0 : ℂ) (countingRadius38 N) := by
  have hi := periodicCandidate_central_index38 h hk
  have hm : (centralRoots f N).getD (k + 2 * (N : ℤ)).toNat 0 ∈ centralRoots f N := by
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  have hr := ((counting_mem_zeroMultiset38 h 0 (countingRadius38 N) _).mp
    ((sortComplexRoots_mem38 _ _).mp hm)).1
  unfold periodicCentralIndex38 at hk
  simpa only [periodicCandidate38, ite_eq_left hk] using hr

theorem periodicCandidate_far_mem38 {f : ℂ → ℂ} {N : ℕ}
    (h : RootCountingAt38 f 2 N) {k : ℤ} (hk : ¬ periodicCentralIndex38 N k) :
    periodicCandidate38 f N k ∈ ball (countingCenter38 (k / 2)) (Real.pi / 4) := by
  have hi := periodicCandidate_far_index38 h hk
  have hm : (smallRoots f (k / 2)).getD (k % 2).toNat 0 ∈ smallRoots f (k / 2) := by
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  have hr := ((counting_mem_zeroMultiset38 h (countingCenter38 (k / 2)) (Real.pi / 4) _).mp
    ((sortComplexRoots_mem38 _ _).mp hm)).1
  unfold periodicCentralIndex38 at hk
  simpa only [periodicCandidate38, ite_eq_right hk] using hr

theorem criticalCandidate_central_mem38 {f : ℂ → ℂ} {N : ℕ}
    (h : RootCountingAt38 f 1 N) {n : ℤ} (hn : criticalCentralIndex38 N n) :
    criticalCandidate38 f N n ∈ ball (0 : ℂ) (countingRadius38 N) := by
  have hi := criticalCandidate_central_index38 h hn
  have hm : (centralRoots f N).getD (n + (N : ℤ)).toNat 0 ∈ centralRoots f N := by
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  have hr := ((counting_mem_zeroMultiset38 h 0 (countingRadius38 N) _).mp
    ((sortComplexRoots_mem38 _ _).mp hm)).1
  unfold criticalCentralIndex38 at hn
  simpa only [criticalCandidate38, ite_eq_left hn] using hr

theorem criticalCandidate_far_mem38 {f : ℂ → ℂ} {N : ℕ}
    (h : RootCountingAt38 f 1 N) {n : ℤ} (hn : ¬ criticalCentralIndex38 N n) :
    criticalCandidate38 f N n ∈ ball (countingCenter38 n) (Real.pi / 4) := by
  have hi := criticalCandidate_far_index38 h hn
  have hm : (smallRoots f n).getD 0 0 ∈ smallRoots f n := by
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  have hr := ((counting_mem_zeroMultiset38 h (countingCenter38 n) (Real.pi / 4) _).mp
    ((sortComplexRoots_mem38 _ _).mp hm)).1
  unfold criticalCentralIndex38 at hn
  simpa only [criticalCandidate38, ite_eq_right hn] using hr

end
end NlsGge.GK38
