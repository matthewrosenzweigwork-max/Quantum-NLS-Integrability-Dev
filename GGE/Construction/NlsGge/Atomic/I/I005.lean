                                                                                                                                         
                                                    
import Mathlib
import NlsGge.Weights.Regularity
import NlsGge.Birkhoff.W05FiniteGap38

                                                                                       
                                                                                                            
                                                                                                                     
                                                                                                   
                                                                                                   

set_option autoImplicit false
open NlsGge.Weights NlsGge.Birkhoff NlsGge.Pilot

namespace NlsGge.ThirdConsultation.I

theorem termDeriv_nonneg {lower : ℝ} {c : ℕ → ℝ} (hl : 0 < lower) (hb : ∀ j : ℕ, lower ≤ c j)
    {r : ℝ} (hr : 0 < r) (j : ℕ) : 0 ≤ weightTermDerivative c r j := by
  unfold weightTermDerivative NlsGge.coefficient
  have hc : 0 ≤ c j / (Nat.factorial j : ℝ) ^ 4 :=
    div_nonneg (by linarith [hb j]) (by positivity)
  positivity

theorem i005 (lower upper : ℝ) (c : BoundedCoefficients lower upper) :
    (∀ r : ℝ, 0 < r →
      0 < weight c.val r ∧
      HasDerivAt (weight c.val) (deriv (weight c.val) r) r ∧
      0 ≤ deriv (weight c.val) r / weight c.val r ∧
      deriv (weight c.val) r / weight c.val r ≤
        2 * (upper / lower) ^ (1 / 4 : ℝ) * r ^ (-1 / 2 : ℝ)) ∧
    (∀ (m : ℕ) (r : ℝ), 0 < r →
      0 < partialWeight c.val m r ∧
      HasDerivAt (partialWeight c.val m) (deriv (partialWeight c.val m) r) r ∧
      0 ≤ deriv (partialWeight c.val m) r / partialWeight c.val m r ∧
      deriv (partialWeight c.val m) r / partialWeight c.val m r ≤
        2 * (upper / lower) ^ (1 / 4 : ℝ) * r ^ (-1 / 2 : ℝ)) ∧
    (∀ r : ℝ, deriv (partialWeight c.val 0) r = 0) := by
  have hl : 0 < lower := coef_lower38 c
  have hb : ∀ j : ℕ, lower ≤ c.val j := coef_bound38 c
  have hu : ∀ j : ℕ, c.val j ≤ upper := coef_upper38 c
  refine ⟨fun r hr => ?_, fun m r hr => ?_, fun r => partialWeight_deriv_order_zero c.val r⟩
  · have hD := weight_hasDerivAt lower upper c.val hl hb hu r
    have hpos := weight_pos lower upper c.val hl hb hu r
    have hdnn : 0 ≤ deriv (weight c.val) r := by
      rw [hD.deriv]
      exact tsum_nonneg fun j => termDeriv_nonneg hl hb hr j
    refine ⟨hpos, ?_, div_nonneg hdnn hpos.le, ?_⟩
    · rw [hD.deriv]; exact hD
    · exact weight_logDerivative_le lower upper c.val hl hb hu r hr
  · have hD := partialWeight_hasDerivAt c.val m r
    have hpos := partialWeight_pos lower c.val hl hb m r
    have hdnn : 0 ≤ deriv (partialWeight c.val m) r := by
      rw [hD.deriv]
      exact Finset.sum_nonneg fun j _ => termDeriv_nonneg hl hb hr j
    refine ⟨hpos, ?_, div_nonneg hdnn hpos.le, ?_⟩
    · rw [hD.deriv]; exact hD
    · exact partialWeight_logDerivative_le lower upper c.val hl hb hu m r hr

end NlsGge.ThirdConsultation.I
