import Mathlib
import NlsGge.Atomic.KSN.KSN011
import NlsGge.GK38.Lib.EntireProductsC34b

                                                                                      
                                                                                                               
                                                                                                              
                                                                                                                 
                                                                                                            
                                                                                        
set_option autoImplicit false
open scoped BigOperators

namespace NlsGge.ThirdConsultation.KSN012L
noncomputable section
open NlsGge.Pilot

theorem jb_pos (n : ℤ) : 0 < japaneseBracket n := by
  unfold japaneseBracket; exact Real.sqrt_pos.2 (by positivity)

/-- ⟨n⟩ mass_n ≤ √S. -/
theorem mass_pointwise (mass : ℤ → ℝ) (hm0 : ∀ k, 0 ≤ mass k) (S : ℝ)
    (hs : Summable (fun k : ℤ => (japaneseBracket k * mass k) ^ 2))
    (hS : (∑' k : ℤ, (japaneseBracket k * mass k) ^ 2) ≤ S) (n : ℤ) :
    japaneseBracket n * mass n ≤ Real.sqrt S := by
  have h1 : (japaneseBracket n * mass n) ^ 2 ≤ S :=
    (hs.le_tsum n (fun k _ => sq_nonneg _)).trans hS
  have h0 : 0 ≤ japaneseBracket n * mass n := mul_nonneg (jb_pos n).le (hm0 n)
  have := Real.abs_le_sqrt h1
  rwa [abs_of_nonneg h0] at this

/-- KSN-011 Cauchy–Schwarz bound for a sum dominated by mass·c3w. -/
theorem beta_pure :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (C : ℝ), 0 ≤ C → ∀ (mass : ℤ → ℝ), (∀ k, 0 ≤ mass k) →
      ∀ S : ℝ, Summable (fun k : ℤ => (japaneseBracket k * mass k) ^ 2) →
      (∑' k : ℤ, (japaneseBracket k * mass k) ^ 2) ≤ S →
      ∀ (n : ℤ) (β : ℂ) (f : ℤ → ℂ), HasSum f β →
      (∀ m : ℤ, ‖f m‖ ≤ C * mass m * NlsGge.GK38.Lib.c3w n m) →
        ‖β‖ ≤ K * C * Real.sqrt S / japaneseBracket n := by
  obtain ⟨K0, hK0⟩ := NlsGge.Atomic.KSN011.ksn011_statement
  refine ⟨max K0 0, le_max_right _ _, fun C hC mass hm0 S hs hS n β f hf hb => ?_⟩
  set v : ℤ → ℂ := fun k => ((japaneseBracket k * mass k : ℝ) : ℂ) with hv
  have hvn : ∀ k, ‖v k‖ = japaneseBracket k * mass k := fun k => by
    simp only [hv, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (mul_nonneg (jb_pos k).le (hm0 k))
  have hmem : Memℓp v 2 := by
    refine memℓp_gen ?_
    refine hs.congr (fun k => ?_)
    rw [hvn k, ENNReal.toReal_ofNat, Real.rpow_two]
  set a : lp (fun _ : ℤ => ℂ) 2 := ⟨v, hmem⟩ with ha
  have hak : ∀ k, ‖a k‖ = japaneseBracket k * mass k := fun k => hvn k
  have hnorm : ‖a‖ ≤ Real.sqrt S := by
    have h0 := lp.norm_rpow_eq_tsum (p := (2 : ENNReal)) (by norm_num) a
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h0
    have h2 : ‖a‖ ^ 2 ≤ S := by
      rw [h0]
      refine le_trans (le_of_eq (tsum_congr (fun k => ?_))) hS
      rw [hak k]
    have := Real.abs_le_sqrt h2
    rwa [abs_of_nonneg (norm_nonneg _)] at this
  obtain ⟨hsumg, hbd⟩ := hK0 a n
  set g : ℤ → ℝ := fun k => if k = n then (0 : ℝ) else
    ‖a k‖ / (japaneseBracket k * |(k : ℝ) - (n : ℝ)|) with hg
  have hfg : ∀ m, ‖f m‖ ≤ C * g m := by
    intro m
    refine (hb m).trans (le_of_eq ?_)
    simp only [hg]
    unfold NlsGge.GK38.Lib.c3w
    split_ifs with hmn
    · subst hmn; simp
    · rw [hak m]
      have hj := (jb_pos m).ne'
      field_simp
  have hg0 : ∀ m, 0 ≤ g m := fun m => by
    simp only [hg]; split_ifs
    · exact le_rfl
    · exact div_nonneg (norm_nonneg _) (mul_nonneg (jb_pos m).le (abs_nonneg _))
  have hsf : Summable (fun m => ‖f m‖) :=
    Summable.of_nonneg_of_le (fun m => norm_nonneg _) hfg (hsumg.mul_left C)
  have h1 : ‖β‖ ≤ ∑' m, ‖f m‖ := by
    rw [← hf.tsum_eq]; exact norm_tsum_le_tsum_norm hsf
  have h2 : ∑' m, ‖f m‖ ≤ C * ∑' m, g m := by
    rw [← tsum_mul_left]; exact hsf.tsum_le_tsum hfg (hsumg.mul_left C)
  have hjn := jb_pos n
  have h3 : ∑' m, g m ≤ max K0 0 * Real.sqrt S / japaneseBracket n := by
    rw [le_div_iff₀ hjn, mul_comm]
    refine hbd.trans ?_
    calc K0 * ‖a‖ ≤ max K0 0 * ‖a‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
      _ ≤ max K0 0 * Real.sqrt S := mul_le_mul_of_nonneg_left hnorm (le_max_right _ _)
  calc ‖β‖ ≤ C * ∑' m, g m := h1.trans h2
    _ ≤ C * (max K0 0 * Real.sqrt S / japaneseBracket n) := mul_le_mul_of_nonneg_left h3 hC
    _ = max K0 0 * C * Real.sqrt S / japaneseBracket n := by ring

end
end NlsGge.ThirdConsultation.KSN012L
