import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS003Host
import NlsGge.ThirdConsultation.KSPS.KSPS020Host
import NlsGge.ThirdConsultation.KSPS.KSPS011Support4

                                                                                                                    
                                                                                                            
                                                                                                  
                                                                                                                   
                                                                        
                                                                           
                                                                              
                                                                                                                         
                                                              
set_option autoImplicit false
open scoped BigOperators

namespace NlsGge.ThirdConsultation.KSPS026W
noncomputable section
open NlsGge.ThirdConsultation.KSPS

theorem periodicPlus_eq_of_toPair {N : ℕ} (φ : SobolevC N) (φ' : SobolevC 1)
    (h : NlsGge.ThirdConsultation.KSPSVolterra.toPair φ' = toPotPair φ) (n : ℤ) :
    periodicPlus φ' n = periodicPlus φ n := by
  unfold periodicPlus
  rw [← h]
  rfl

theorem periodicMinus_eq_of_toPair {N : ℕ} (φ : SobolevC N) (φ' : SobolevC 1)
    (h : NlsGge.ThirdConsultation.KSPSVolterra.toPair φ' = toPotPair φ) (n : ℤ) :
    periodicMinus φ' n = periodicMinus φ n := by
  unfold periodicMinus
  rw [← h]
  rfl

theorem indexWeight_le_two_natAbs (n : ℤ) (hn : 1 ≤ n.natAbs) : indexWeight n ≤ 2 * (n.natAbs : ℝ) := by
  have h1 : (1 : ℝ) ≤ (n.natAbs : ℝ) := by exact_mod_cast hn
  have h2 : (n : ℝ) ^ 2 = (n.natAbs : ℝ) ^ 2 := by
    rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]
  unfold indexWeight
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  rw [h2]
  nlinarith

theorem indexWeight_pos' (n : ℤ) : 0 < indexWeight n := by
  unfold indexWeight
  exact Real.sqrt_pos.2 (by positivity)

/-- Rough localization of both periodic endpoints, for every n, with a weight-1 constant. -/
theorem periodic_localization_of {N : ℕ} (hN : 1 ≤ N) (φ : SobolevC N)
    (h20 : ∀ B : ℝ, 0 < B →
      ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ φ : SobolevC 1, sobolevNorm 1 φ ≤ B →
        ∀ n : ℤ, N ≤ n.natAbs →
          max ‖periodicPlus φ n-(n:ℂ)*Real.pi‖
              ‖periodicMinus φ n-(n:ℂ)*Real.pi‖ ≤
            C/(n.natAbs:ℝ)) :
    ∃ a : ℝ, 0 ≤ a ∧ ∀ n : ℤ,
      ‖periodicPlus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n ∧
      ‖periodicMinus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n := by
  obtain ⟨φ', hφ'⟩ := NlsGge.ThirdConsultation.KSPS011Support4.exists_toPair_eq hN φ
  have hB : 0 < sobolevNorm 1 φ' + 1 := by
    have : 0 ≤ sobolevNorm 1 φ' := Real.sqrt_nonneg _
    linarith
  obtain ⟨C, M, hC, hb⟩ := h20 _ hB
  set f : ℤ → ℝ := fun n => max ‖periodicPlus φ n - (n : ℂ) * (Real.pi : ℂ)‖
    ‖periodicMinus φ n - (n : ℂ) * (Real.pi : ℂ)‖ with hfdef
  have hf0 : ∀ n, 0 ≤ f n := fun n => le_max_of_le_left (norm_nonneg _)
  set S : Finset ℤ := Finset.Icc (-((M : ℤ) + 1)) ((M : ℤ) + 1) with hSdef
  set K : ℝ := ∑ k ∈ S, f k * indexWeight k with hKdef
  have hK0 : 0 ≤ K := Finset.sum_nonneg (fun k _ => mul_nonneg (hf0 k) (indexWeight_pos' k).le)
  refine ⟨2 * C + K, by positivity, fun n => ?_⟩
  have hw0 := indexWeight_pos' n
  suffices hfn : f n ≤ (2 * C + K) / indexWeight n from
    ⟨(le_max_left _ _).trans hfn, (le_max_right _ _).trans hfn⟩
  rw [le_div_iff₀ hw0]
  by_cases hn : n ∈ S
  · have h1 : f n * indexWeight n ≤ K :=
      Finset.single_le_sum (f := fun k => f k * indexWeight k)
        (fun k _ => mul_nonneg (hf0 k) (indexWeight_pos' k).le) hn
    linarith
  · have hn' : M + 1 < n.natAbs := by
      rw [hSdef, Finset.mem_Icc, not_and_or, not_le, not_le] at hn
      omega
    have hb' := hb φ' (by linarith) n (by omega)
    rw [periodicPlus_eq_of_toPair φ φ' hφ', periodicMinus_eq_of_toPair φ φ' hφ'] at hb'
    have hν : (1 : ℝ) ≤ (n.natAbs : ℝ) := by exact_mod_cast (by omega : 1 ≤ n.natAbs)
    have hν0 : (0 : ℝ) < (n.natAbs : ℝ) := by linarith
    have hw2 := indexWeight_le_two_natAbs n (by omega)
    have h3 : f n * (n.natAbs : ℝ) ≤ C := by
      have := (le_div_iff₀ hν0).1 hb'
      exact this
    have h4 : f n * indexWeight n ≤ f n * (2 * (n.natAbs : ℝ)) :=
      mul_le_mul_of_nonneg_left hw2 (hf0 n)
    linarith

end
end NlsGge.ThirdConsultation.KSPS026W
