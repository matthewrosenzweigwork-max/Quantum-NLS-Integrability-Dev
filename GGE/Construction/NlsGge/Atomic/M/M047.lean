import Mathlib
import NlsGge.Atomic.M.M047Host

                                                                                                           
                                                                                    
                                                                                                           
                                                                                                               
                                                                                                        
                                                                                                     
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.M

theorem inverse_polynomial_domination (m : ℕ) (hm : 2 ≤ m) :
    ∃ C : ℝ, 0 < C ∧
      ∀ A0 A1 Am : ℝ, ActionMomentRelations m A0 A1 Am →
        A0 ^ (2 * m + 1) +
          (1 + A0) ^ (2 * m - 1) * A1 ^ (2 * m - 1) ≤
        C * (Am + (1 + A1) ^ (4 * m - 3) * A0) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have e1 : 2 * (k + 2) - 1 = 2 * k + 3 := by omega
  have e2 : 4 * (k + 2) - 3 = 4 * k + 5 := by omega
  have e3 : k + 2 - 1 = k + 1 := by omega
  -- elementary max lemma: T^(k+2) ≤ P*Q^(k+1) with P,Q ≥ 0 forces T ≤ P + Q
  have key : ∀ T P Q : ℝ, 0 ≤ P → 0 ≤ Q → T ^ (k + 2) ≤ P * Q ^ (k + 1) → T ≤ P + Q := by
    intro T P Q hP hQ h
    by_contra hlt
    replace hlt := not_le.mp hlt
    have hTP : P < T := by linarith
    have hTQ : Q < T := by linarith
    have hT0 : 0 < T := lt_of_le_of_lt hQ hTQ
    have h1 : Q ^ (k + 1) ≤ T ^ (k + 1) := pow_le_pow_left₀ hQ hTQ.le _
    have h2 : 0 < T ^ (k + 1) := pow_pos hT0 _
    have h3 : P * Q ^ (k + 1) < T ^ (k + 2) := by
      calc P * Q ^ (k + 1) ≤ P * T ^ (k + 1) := mul_le_mul_of_nonneg_left h1 hP
        _ < T * T ^ (k + 1) := mul_lt_mul_of_pos_right hTP h2
        _ = T ^ (k + 2) := by ring
    linarith
  refine ⟨2 ^ (2 * k + 4), by positivity, ?_⟩
  intro A0 A1 Am hrel
  have hrel' : actionMomentRelations (k + 2) A0 A1 Am := hrel
  unfold actionMomentRelations at hrel'
  obtain ⟨h0, h01, h1m, hpow⟩ := hrel'
  rw [e3] at hpow
  rw [e1, e2]
  have hA1 : 0 ≤ A1 := h0.trans h01
  have hAm : 0 ≤ Am := hA1.trans h1m
  have hB1 : (1 : ℝ) ≤ 1 + A1 := by linarith
  have hA1B : A1 ≤ 1 + A1 := by linarith
  have hA0B : A0 ≤ 1 + A1 := by linarith
  have hQ : 0 ≤ (1 + A1) ^ (4 * k + 5) * A0 := by positivity
  -- term 1
  have t1 : A0 ^ (2 * (k + 2) + 1) ≤ (1 + A1) ^ (4 * k + 5) * A0 := by
    calc A0 ^ (2 * (k + 2) + 1) = A0 ^ (2 * k + 4) * A0 := by ring
      _ ≤ (1 + A1) ^ (2 * k + 4) * A0 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 hA0B _) h0
      _ ≤ (1 + A1) ^ (4 * k + 5) * A0 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hB1 (by omega)) h0
  -- term 2
  have t2 : (1 + A0) ^ (2 * k + 3) * A1 ^ (2 * k + 3) ≤
      2 ^ (2 * k + 3) * (Am + (1 + A1) ^ (4 * k + 5) * A0) := by
    rcases le_total A0 1 with hs | hs
    · have hT : A1 ^ (2 * k + 3) ≤ Am + (1 + A1) ^ (4 * k + 5) * A0 := by
        apply key _ _ _ hAm hQ
        have hexp : (2 * k + 2) * (k + 2) ≤ (4 * k + 5) * (k + 1) := by nlinarith
        calc (A1 ^ (2 * k + 3)) ^ (k + 2)
            = A1 ^ (k + 2) * A1 ^ ((2 * k + 2) * (k + 2)) := by
              rw [← pow_mul, ← pow_add]; congr 1; ring
          _ ≤ (Am * A0 ^ (k + 1)) * (1 + A1) ^ ((4 * k + 5) * (k + 1)) :=
              mul_le_mul hpow
                (le_trans (pow_le_pow_left₀ hA1 hA1B _) (pow_le_pow_right₀ hB1 hexp))
                (by positivity) (by positivity)
          _ = Am * ((1 + A1) ^ (4 * k + 5) * A0) ^ (k + 1) := by
              rw [mul_pow, ← pow_mul]; ring
      exact mul_le_mul (pow_le_pow_left₀ (by linarith) (by linarith : 1 + A0 ≤ 2) _) hT
        (by positivity) (by positivity)
    · calc (1 + A0) ^ (2 * k + 3) * A1 ^ (2 * k + 3)
          ≤ (2 * A0) ^ (2 * k + 3) * A1 ^ (2 * k + 3) :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) (by linarith) _)
              (by positivity)
        _ = 2 ^ (2 * k + 3) * ((A0 ^ (2 * k + 2) * A1 ^ (2 * k + 3)) * A0) := by ring
        _ ≤ 2 ^ (2 * k + 3) * (((1 + A1) ^ (2 * k + 2) * (1 + A1) ^ (2 * k + 3)) * A0) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply mul_le_mul_of_nonneg_right _ h0
            exact mul_le_mul (pow_le_pow_left₀ h0 hA0B _) (pow_le_pow_left₀ hA1 hA1B _)
              (by positivity) (by positivity)
        _ = 2 ^ (2 * k + 3) * ((1 + A1) ^ (4 * k + 5) * A0) := by ring
        _ ≤ 2 ^ (2 * k + 3) * (Am + (1 + A1) ^ (4 * k + 5) * A0) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hp : (1 : ℝ) ≤ 2 ^ (2 * k + 3) := one_le_pow₀ (by norm_num)
  have hS0 : 0 ≤ Am + (1 + A1) ^ (4 * k + 5) * A0 := by linarith
  have hS : Am + (1 + A1) ^ (4 * k + 5) * A0 ≤
      2 ^ (2 * k + 3) * (Am + (1 + A1) ^ (4 * k + 5) * A0) := le_mul_of_one_le_left hS0 hp
  have h24 : (2 : ℝ) ^ (2 * k + 4) * (Am + (1 + A1) ^ (4 * k + 5) * A0) =
      2 * (2 ^ (2 * k + 3) * (Am + (1 + A1) ^ (4 * k + 5) * A0)) := by ring
  rw [h24]
  linarith

end NlsGge.ThirdConsultation.M
