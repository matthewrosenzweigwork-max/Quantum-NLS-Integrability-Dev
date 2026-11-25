import Mathlib
import NlsGge.ThirdConsultation.S.SShared06
import NlsGge.Schur.ActualSchurBallConstants38V1

                                                                                                            
                                                                                                                              
                                                                                                                           
                                                                                                                       
                        
set_option autoImplicit false
noncomputable section
open NlsGge.Pilot NlsGge.Analysis NlsGge.Schur NlsGge.Measure
namespace NlsGge.ThirdConsultation.S

theorem lowGaussianProduct_bound (lo up : ℝ) (hl : 0 < lo) (hlu : lo ≤ up)
    (A : ℝ) (hA : 1 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : BoundedCoefficients lo up) (R : ℝ), 1 ≤ R →
      (∏ n ∈ normalizerModes (splitCutoff A R), R ^ 2 * fullWeightRate c.val n) ≤
        Real.exp (C * (1 + R) ^ 9) := by
  have hup : 0 < up := lt_of_lt_of_le hl hlu
  refine ⟨ballLowConstant38 A up, ?_, ?_⟩
  · unfold ballLowConstant38
    have h1 : 0 < 2 * A + 3 := by linarith
    have h2 : 0 < 2 + |Real.log up| + 4 * Real.sqrt (2 * Real.pi * (A + 1)) := by
      have := abs_nonneg (Real.log up)
      have := Real.sqrt_nonneg (2 * Real.pi * (A + 1))
      linarith
    exact mul_pos h1 h2
  · intro c R hR
    have hR6 : 0 ≤ R ^ 6 := by positivity
    have hMle : ((splitCutoff A R : ℕ) : ℝ) ≤ A * R ^ 6 + 1 :=
      (Nat.ceil_lt_add_one (by positivity : 0 ≤ A * R ^ 6)).le
    have hn : ∀ i ∈ normalizerModes (splitCutoff A R), |(fun i : ℤ => i) i| ≤ ((splitCutoff A R : ℕ) : ℤ) := by
      intro i hi
      unfold normalizerModes at hi
      rw [Finset.mem_Icc] at hi
      exact abs_le.mpr hi
    have hcard : ((normalizerModes (splitCutoff A R)).card : ℝ) ≤ 2 * ((splitCutoff A R : ℕ) : ℝ) + 1 := by
      unfold normalizerModes
      rw [Int.card_Icc]
      have h : (((splitCutoff A R : ℕ) : ℤ) + 1 - -((splitCutoff A R : ℕ) : ℤ)).toNat =
          2 * splitCutoff A R + 1 := by omega
      rw [h]
      push_cast
      exact le_rfl
    have := ballLowProduct_le38 (ι := ℤ) lo up c.val c.property A R hA hR (splitCutoff A R) hMle
      (normalizerModes (splitCutoff A R)) (fun i => i) hn hcard
    exact this

end NlsGge.ThirdConsultation.S

end
