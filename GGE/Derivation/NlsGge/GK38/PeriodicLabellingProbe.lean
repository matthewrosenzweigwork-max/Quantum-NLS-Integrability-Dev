import NlsGge.GK38.PeriodicLabelling
import NlsGge.GK38.PairAsymptoticsTriangularProbe

/-! # S2: free, negative, repeated-root, cutoff and nonzero-potential probes -/
set_option autoImplicit false
open Set Metric NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem labelling_probe_negative_pair38 :
    lamSeq 0 (-2) = countingCenter38 (-1) ∧ lamSeq 0 (-1) = countingCenter38 (-1) := by
  constructor <;> rw [lamSeq_zero38] <;> norm_num

theorem labelling_probe_central_double38 :
    lamSeq 0 0 = 0 ∧ lamSeq 0 1 = 0 ∧
      analyticOrderAt (perChar 0) 0 = 2 ∧ Set.encard {k : ℤ | lamSeq 0 k = 0} = 2 := by
  have horder : analyticOrderAt (perChar 0) 0 = 2 := by
    rw [← Nat.cast_analyticOrderNatAt
      (counting_order_ne_top38 (free_periodic_counting38 (N := 1) (by norm_num)) 0), counting_free_order38]
    simp
  refine ⟨?_, ?_, horder, ((lamSeq_enumeration38 0).2.2 0).2.trans horder⟩
  · simp [lamSeq_zero38, countingCenter38]
  · simp [lamSeq_zero38, countingCenter38]

theorem labelling_probe_critical_simple38 :
    lamDot 0 0 = 0 ∧ analyticOrderAt (deriv (discrim 0)) 0 = 1 ∧
      Set.encard {k : ℤ | lamDot 0 k = 0} = 1 := by
  have horder : analyticOrderAt (deriv (discrim 0)) 0 = 1 := by
    rw [← Nat.cast_analyticOrderNatAt
      (counting_order_ne_top38 (free_critical_counting38 (N := 1) (by norm_num)) 0), critical_free_order38]
    simp
  exact ⟨by simp [lamDot_zero38, countingCenter38], horder, (lamDot_occurrence38 0 0).2.trans horder⟩

theorem labelling_probe_changed_cutoff38 :
    periodicCandidate38 (perChar 0) 1 (-3) = countingCenter38 (-2) ∧
      periodicCandidate38 (perChar 0) 3 (-3) = countingCenter38 (-2) ∧
      criticalCandidate38 (deriv (discrim 0)) 1 (-2) = countingCenter38 (-2) ∧
      criticalCandidate38 (deriv (discrim 0)) 3 (-2) = countingCenter38 (-2) := by
  have hp₁ := lamSeq_eq_candidate38 0 (free_periodic_counting38 (N := 1) (by norm_num))
  have hp₃ := lamSeq_eq_candidate38 0 (free_periodic_counting38 (N := 3) (by norm_num))
  have hd₁ := lamDot_eq_candidate38 0 (free_critical_counting38 (N := 1) (by norm_num))
  have hd₃ := lamDot_eq_candidate38 0 (free_critical_counting38 (N := 3) (by norm_num))
  rw [← hp₁, ← hp₃, ← hd₁, ← hd₃, lamSeq_zero38, lamDot_zero38]
  norm_num

theorem labelling_probe_complex_lex38 :
    complexLexLE38 (1 + Complex.I) (1 + 2 * Complex.I) ∧
      complexLexLE38 (Complex.I * 100) 1 := by
  simp [complexLexLE_iff38]

/-- A nonzero triangular potential can retain repeated roots; no real-slice simplicity is used. -/
theorem labelling_probe_triangular38 (u : PhysicalL2) (n : ℤ) :
    lamMinus (u, 0) n = countingCenter38 n ∧ lamPlus (u, 0) n = countingCenter38 n := by
  have he : perChar (u, 0) = perChar 0 := by
    funext z
    rw [triangularPerChar_eq38, perChar_zero]
  have hs := lamSeq_eq_of_perChar_eq38 he
  simpa only [lamMinus, lamPlus, hs] using And.intro (lamMinus_zero38 n) (lamPlus_zero38 n)

end
end NlsGge.GK38
