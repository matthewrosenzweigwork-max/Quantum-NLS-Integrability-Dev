import Mathlib
import NlsGge.Sobolev.SourceWeighted
import NlsGge.Measure.FourierGaussian

                                                                                                                      
                                                                                                                      
                                                                                                              
                                                                                                    

set_option autoImplicit false

namespace NlsGge.Atomic.I003

open NlsGge.Pilot

theorem i003 (lower upper : ℝ) (c : BoundedCoefficients lower upper) (r : ℝ) :
    let t : ℝ := Real.sqrt |r|
    HasSum (fun j : ℕ => t ^ j / (j.factorial : ℝ)) (Real.exp t) ∧
    Summable (fun j : ℕ => t ^ (4 * j) / (j.factorial : ℝ) ^ 4) ∧
    (∑' j : ℕ, t ^ (4 * j) / (j.factorial : ℝ) ^ 4) ≤
      (∑' j : ℕ, t ^ j / (j.factorial : ℝ)) ^ 4 ∧
    (∑' j : ℕ, t ^ j / (j.factorial : ℝ)) ^ 4 = Real.exp (4 * t) ∧
    NlsGge.Weights.weight c.val r ≤ upper * Real.exp (4 * t) ∧
    ∀ m : ℕ, NlsGge.Weights.partialWeight c.val m r ≤ upper * Real.exp (4 * t) := by
  intro t
  obtain ⟨hl, _hlu, hbd⟩ := c.2
  have hbound : ∀ j : ℕ, lower ≤ c.val j := fun j => (hbd j).1
  have hupper : ∀ j : ℕ, c.val j ≤ upper := fun j => (hbd j).2
  have ht : 0 ≤ t := Real.sqrt_nonneg _
  have hS : HasSum (fun j : ℕ => t ^ j / (j.factorial : ℝ)) (Real.exp t) :=
    NlsGge.Weights.expSeries_hasSum t
  have hpow : ∀ j : ℕ, t ^ (4 * j) / (j.factorial : ℝ) ^ 4 = (t ^ j / (j.factorial : ℝ)) ^ 4 := by
    intro j
    rw [div_pow, ← pow_mul, mul_comm]
  have hsum4 : Summable (fun j : ℕ => (t ^ j / (j.factorial : ℝ)) ^ 4) := by
    refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_)
      (hS.summable.mul_left (Real.exp t ^ 3))
    exact NlsGge.Weights.fourth_power_le_exp_majorant t ht j
  have hS_eq : (∑' j : ℕ, t ^ j / (j.factorial : ℝ)) = Real.exp t := hS.tsum_eq
  refine ⟨hS, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hpow]
    exact hsum4
  · simp only [hpow]
    rw [hS_eq]
    have hterm : ∀ j : ℕ, (t ^ j / (j.factorial : ℝ)) ^ 4 ≤ Real.exp t ^ 3 * (t ^ j / (j.factorial : ℝ)) := by
      intro j
      exact NlsGge.Weights.fourth_power_le_exp_majorant t ht j
    calc ∑' j : ℕ, (t ^ j / (j.factorial : ℝ)) ^ 4
        ≤ ∑' j : ℕ, Real.exp t ^ 3 * (t ^ j / (j.factorial : ℝ)) :=
          Summable.tsum_le_tsum hterm hsum4 (hS.summable.mul_left _)
      _ = Real.exp t ^ 3 * Real.exp t := by rw [tsum_mul_left, hS.tsum_eq]
      _ = Real.exp t ^ 4 := by ring
  · rw [hS_eq, ← Real.exp_nat_mul]
    norm_num
  · exact NlsGge.Weights.weight_upper lower upper c.val hl hbound hupper r
  · intro m
    exact NlsGge.Weights.partialWeight_upper lower upper c.val hl hbound hupper m r

#print axioms NlsGge.Atomic.I003.i003

end NlsGge.Atomic.I003
