import NlsGge.Sobolev.SourceWeighted

set_option autoImplicit false
noncomputable section
open scoped ENNReal

namespace NlsGge.Pilot

theorem japaneseBracket_neg (n : ℤ) : japaneseBracket (-n) = japaneseBracket n := by
  simp [japaneseBracket]

theorem sourceRate_neg {lower upper : ℝ} (c : BoundedCoefficients lower upper) (n : ℤ) :
    sourceRate c (-n) = sourceRate c n := by
  unfold sourceRate
  rw [Int.cast_neg, mul_neg]
  exact NlsGge.Weights.weight_even c.val _

theorem fullModeWeight_neg {lower upper : ℝ} (c : BoundedCoefficients lower upper)
    (s : ℝ) (n : ℤ) : fullModeWeight c s (-n) = fullModeWeight c s n := by
  simp only [fullModeWeight, sourceRate_neg, japaneseBracket_neg]

theorem sobolevSquareSummable_reflection (r : ℝ) (x : ℤ → ℂ)
    (hx : SobolevSquareSummable r x) :
    SobolevSquareSummable r (fun n => -x (-n)) := by
  change Summable (fun n => Real.rpow (japaneseBracket n) (2 * r) * ‖-x (-n)‖ ^ 2)
  have h : Summable (fun n => Real.rpow (japaneseBracket (-n)) (2 * r) * ‖x (-n)‖ ^ 2) := by
    simpa only [Function.comp_apply] using! ((Equiv.neg ℤ).summable_iff).2 hx
  exact h.congr (fun n => by rw [japaneseBracket_neg, norm_neg])

theorem weightedSquareSummable_reflection (a : ℤ → ℝ)
    (ha : ∀ n : ℤ, a (-n) = a n) (s : ℝ) (x : ℤ → ℂ)
    (hx : WeightedSquareSummable a s x) :
    WeightedSquareSummable a s (fun n => -x (-n)) := by
  change Summable (fun n => a n * Real.rpow (japaneseBracket n) (-2 * s) * ‖-x (-n)‖ ^ 2)
  have h : Summable (fun n => a (-n) * Real.rpow (japaneseBracket (-n)) (-2 * s) *
      ‖x (-n)‖ ^ 2) := by
    simpa only [Function.comp_apply] using! ((Equiv.neg ℤ).summable_iff).2 hx
  exact h.congr (fun n => by rw [ha, japaneseBracket_neg, norm_neg])

end NlsGge.Pilot
