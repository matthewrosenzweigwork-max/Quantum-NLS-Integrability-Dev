import Mathlib
import NlsGge.Weights.PoissonMoments
import NlsGge.Weights.Entire

                                                                                                                    
                                                                                                                          
                                                                                                                      

set_option autoImplicit false
open NlsGge.Weights

namespace NlsGge.Atomic.R072

theorem weight_poissonFourth_identity (c : ℕ → ℝ) (r : ℝ) (hr : 0 < r) :
    weight c r = Real.exp (4 * Real.sqrt r) * ∑' j, c j * (poissonTerm (Real.sqrt r) j) ^ 4 := by
  have hsq : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr.le
  have hp : ∀ j : ℕ, (Real.sqrt r ^ j) ^ 4 = r ^ (2 * j) := by
    intro j
    rw [← pow_mul, show j * 4 = 2 * (2 * j) by ring, pow_mul, hsq]
  have he : Real.exp (4 * Real.sqrt r) * (Real.exp (-Real.sqrt r)) ^ 4 = 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    have h0 : 4 * Real.sqrt r + ((4 : ℕ) : ℝ) * (-Real.sqrt r) = 0 := by push_cast; ring
    rw [h0, Real.exp_zero]
  have hterm : ∀ j : ℕ, weightTerm c r j =
      Real.exp (4 * Real.sqrt r) * (c j * (poissonTerm (Real.sqrt r) j) ^ 4) := by
    intro j
    unfold weightTerm coefficient poissonTerm
    have e : Real.exp (4 * Real.sqrt r) * (c j * (Real.exp (-Real.sqrt r) * Real.sqrt r ^ j /
        (Nat.factorial j : ℝ)) ^ 4)
        = c j * (Real.exp (4 * Real.sqrt r) * (Real.exp (-Real.sqrt r)) ^ 4) *
          (Real.sqrt r ^ j) ^ 4 / (Nat.factorial j : ℝ) ^ 4 := by ring
    rw [e, he, hp j]
    ring
  show ∑' j, weightTerm c r j = _
  rw [tsum_congr hterm, tsum_mul_left]


end NlsGge.Atomic.R072
