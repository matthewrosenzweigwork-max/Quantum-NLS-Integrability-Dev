import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS026Support3
import NlsGge.ThirdConsultation.KSPS.KSPS011Quant5Core

                                                                                  
                                                                                                              
                                                                                                               
                                                                       
                                                                                                                  
                                                                                                                      
                                                                                               
                                                                                                                  
                             
                                                         
                                                                                                              
                                                              
                                                                                      
                                                                    
                                                                                                                     
                                                                              
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

namespace NlsGge.ThirdConsultation.KSPS025U12
noncomputable section
open NlsGge.Pilot NlsGge.GK38 NlsGge.GKDefinitionDesign NlsGge.ThirdConsultation.KSPS
open NlsGge.ThirdConsultation.KSPSWKB

theorem entries_tail_of (N : ℕ) (hN : 1 ≤ N) (B₀ : ℝ) (hB₀ : 0 ≤ B₀) (a : ℝ) (ha : 0 ≤ a)
    (hloc : ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ → ∀ n : ℤ,
      ‖periodicPlus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n ∧
      ‖periodicMinus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n)
    (T0 : ℝ) (hthr : ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      NlsGge.ThirdConsultation.KSPSVolterra.threshold N (sobolevNorm N φ) ≤ T0)
    (hLR : ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      integralRiccatiLeft φ (N + 1) = integralRiccatiRight φ (N + 1))
    (P : ℝ) (hfour : ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ → ∀ F : Finset ℤ, (∀ n ∈ F, (1 : ℤ) ≤ |n|) →
      ∑ n ∈ F, ‖physicalFourier (iteratedDerivative N φ.1) (-n)‖ ^ 2 ≤ P ∧
      ∑ n ∈ F, ‖physicalFourier (iteratedDerivative N φ.2) n‖ ^ 2 ≤ P)
    (NL : ℕ) (CL : ℝ)
    (hL : ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      ∀ (xi : ℤ → ℂ), (∀ n : ℤ, ‖xi n - (n : ℂ) * Real.pi‖ ≤ a / indexWeight n) →
      ∀ F : Finset ℤ, (∀ n ∈ F, (NL : ℤ) ≤ |n|) →
      ∑ n ∈ F, ‖(indexWeight n : ℂ) *
        ((if hz : xi n = 0 then 0 else
            sourceRemainderVector φ false ⟨xi n, hz⟩ 1 (if false then 0 else 1)) -
          (if false then -Complex.I else Complex.I) * (-1 : ℂ) ^ n *
            (if false then (-1 : ℂ) ^ (N + 1) else -1) *
            physicalFourier (iteratedDerivative N (if false then φ.1 else φ.2))
              ((if false then (-1 : ℤ) else 1) * n))‖ ^ 2 ≤ CL)
    (NU : ℕ) (CU : ℝ)
    (hU : ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      ∀ (xi : ℤ → ℂ), (∀ n : ℤ, ‖xi n - (n : ℂ) * Real.pi‖ ≤ a / indexWeight n) →
      ∀ F : Finset ℤ, (∀ n ∈ F, (NU : ℤ) ≤ |n|) →
      ∑ n ∈ F, ‖(indexWeight n : ℂ) *
        ((if hz : xi n = 0 then 0 else
            sourceRemainderVector φ true ⟨xi n, hz⟩ 1 (if true then 0 else 1)) -
          (if true then -Complex.I else Complex.I) * (-1 : ℂ) ^ n *
            (if true then (-1 : ℂ) ^ (N + 1) else -1) *
            physicalFourier (iteratedDerivative N (if true then φ.1 else φ.2))
              ((if true then (-1 : ℤ) else 1) * n))‖ ^ 2 ≤ CU)
    (N1 : ℕ) (C1 : ℝ)
    (h1 : ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      ∀ (xi : ℤ → ℂ), (∀ n : ℤ, ‖xi n - (n : ℂ) * Real.pi‖ ≤ a / indexWeight n) →
      ∀ F : Finset ℤ, (∀ n ∈ F, (N1 : ℤ) ≤ |n|) →
      ∑ n ∈ F, ‖(indexWeight n : ℂ) *
        (endpointDiagonalLower N φ xi n -
          (-1 : ℂ) ^ n / (2 * Complex.I * xi n) * integralRiccatiLeft φ (N + 1))‖ ^ 2 ≤ C1)
    (N2 : ℕ) (C2 : ℝ)
    (h2 : ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      ∀ (xi : ℤ → ℂ), (∀ n : ℤ, ‖xi n - (n : ℂ) * Real.pi‖ ≤ a / indexWeight n) →
      ∀ F : Finset ℤ, (∀ n ∈ F, (N2 : ℤ) ≤ |n|) →
      ∑ n ∈ F, ‖(indexWeight n : ℂ) *
        (endpointDiagonalUpper N φ xi n -
          (-1 : ℂ) ^ (n + 1) / (2 * Complex.I * xi n) * integralRiccatiRight φ (N + 1))‖ ^ 2 ≤ C2) :
    ∃ (M : ℕ) (CE : ℝ), ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      ∀ (upper : Bool) (i j : Fin 2) (F : Finset ℤ), (∀ n ∈ F, (M : ℤ) ≤ |n|) →
        ∑ n ∈ F, (indexWeight n ^ (N + 1) *
          ‖NlsGge.ThirdConsultation.KSPSWKB.endpointEntryError N φ upper i j n‖) ^ 2 ≤ CE := by
  set A : ℝ := (N : ℝ) * 2 ^ N * (2 * a) with hA
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  refine ⟨max (max (max NL NU) (max N1 N2)) (⌈a⌉₊ + ⌈T0⌉₊ + 1),
    6 * (C1 + C2 + A ^ 2 * P + A ^ 2 * P + CU + CL), fun φ hφ upper i j F hF => ?_⟩
  have hFL : ∀ n ∈ F, (NL : ℤ) ≤ |n| := fun n hn => by have := hF n hn; omega
  have hFU : ∀ n ∈ F, (NU : ℤ) ≤ |n| := fun n hn => by have := hF n hn; omega
  have hF1 : ∀ n ∈ F, (N1 : ℤ) ≤ |n| := fun n hn => by have := hF n hn; omega
  have hF2 : ∀ n ∈ F, (N2 : ℤ) ≤ |n| := fun n hn => by have := hF n hn; omega
  have hFo : ∀ n ∈ F, (1 : ℤ) ≤ |n| := fun n hn => by have := hF n hn; omega
  have hFT : ∀ n ∈ F, ((⌈a⌉₊ + ⌈NlsGge.ThirdConsultation.KSPSVolterra.threshold N (sobolevNorm N φ)⌉₊ + 1 : ℕ) : ℤ)
      ≤ |n| := by
    intro n hn
    have hc : ⌈NlsGge.ThirdConsultation.KSPSVolterra.threshold N (sobolevNorm N φ)⌉₊ ≤ ⌈T0⌉₊ :=
      Nat.ceil_mono (hthr φ hφ)
    have := hF n hn
    push_cast at this ⊢
    omega
  set xi : ℤ → ℂ := fun n => if upper then periodicPlus φ n else periodicMinus φ n with hxidef
  have hxe : ∀ n, (if upper then periodicPlus φ n else periodicMinus φ n) = xi n := fun n => rfl
  have hxi : ∀ n : ℤ, ‖xi n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n := by
    intro n
    cases upper
    · exact (hloc φ hφ n).2
    · exact (hloc φ hφ n).1
  have hw : ∀ n : ℤ, (indexWeight n : ℂ) ≠ 0 := fun n => by
    exact_mod_cast (lt_of_lt_of_le one_pos (NlsGge.ThirdConsultation.KSPS015W.one_le_w n)).ne'
  have hm1 : (-1 : ℂ) ≠ 0 := by norm_num
  obtain ⟨eL, hLs, hLe⟩ : ∃ e : ℤ → ℂ,
      (∀ F : Finset ℤ, (∀ n ∈ F, (NL : ℤ) ≤ |n|) → ∑ n ∈ F, ‖e n‖ ^ 2 ≤ CL) ∧
      ∀ n : ℤ, e n = (indexWeight n : ℂ) *
        (NlsGge.ThirdConsultation.KSPSWKB.endpointRemainderLower N φ xi n -
          Complex.I * (-1 : ℂ) ^ n * (-1 : ℂ) *
            NlsGge.Pilot.physicalFourier (iteratedDerivative N φ.2) n) :=
    ⟨_, hL φ hφ xi hxi, fun n => by simp [NlsGge.ThirdConsultation.KSPSWKB.endpointRemainderLower]⟩
  obtain ⟨eU, hUs, hUe⟩ : ∃ e : ℤ → ℂ,
      (∀ F : Finset ℤ, (∀ n ∈ F, (NU : ℤ) ≤ |n|) → ∑ n ∈ F, ‖e n‖ ^ 2 ≤ CU) ∧
      ∀ n : ℤ, e n = (indexWeight n : ℂ) *
        ((if hz : xi n = 0 then 0 else
            NlsGge.ThirdConsultation.KSPSWKB.sourceRemainderVector φ true ⟨xi n, hz⟩ 1 0) -
          (-Complex.I) * (-1 : ℂ) ^ n * (-1 : ℂ) ^ (N + 1) *
            NlsGge.Pilot.physicalFourier (iteratedDerivative N φ.1) (-n)) :=
    ⟨_, hU φ hφ xi hxi, fun n => by simp⟩
  set e1 : ℤ → ℂ := fun n => (indexWeight n : ℂ) *
      (NlsGge.ThirdConsultation.KSPSWKB.endpointDiagonalLower N φ xi n -
        (-1 : ℂ) ^ n / (2 * Complex.I * xi n) * integralRiccatiLeft φ (N + 1)) with he1
  set e2 : ℤ → ℂ := fun n => (indexWeight n : ℂ) *
      (NlsGge.ThirdConsultation.KSPSWKB.endpointDiagonalUpper N φ xi n -
        (-1 : ℂ) ^ (n + 1) / (2 * Complex.I * xi n) * integralRiccatiRight φ (N + 1)) with he2
  set eUp : ℤ → ℂ := fun n => (-1 : ℂ) ^ N * eU n with heUp
  have h11 : ∀ n : ℤ,
      NlsGge.ThirdConsultation.KSPSWKB.endpointRemainderLower N φ xi n =
        Complex.I * ((-1 : ℂ) ^ (n + 1)) *
          NlsGge.Pilot.physicalFourier
            (NlsGge.ThirdConsultation.KSPS.iteratedDerivative N φ.2) n +
          eL n / indexValue n ∧
      NlsGge.ThirdConsultation.KSPSWKB.endpointRemainderUpper N φ xi n =
        Complex.I * ((-1 : ℂ) ^ n) *
          NlsGge.Pilot.physicalFourier
            (NlsGge.ThirdConsultation.KSPS.iteratedDerivative N φ.1) (-n) +
          eUp n / indexValue n := by
    intro n
    refine ⟨?_, ?_⟩
    · rw [hLe n, zpow_add_one₀ hm1]
      unfold indexValue
      field_simp [hw n]
      ring
    · have hpow : (-1 : ℂ) ^ N * (-1 : ℂ) ^ (N + 1) = -1 := by
        rw [pow_succ, ← mul_assoc, ← mul_pow]; simp
      unfold NlsGge.ThirdConsultation.KSPSWKB.endpointRemainderUpper indexValue
      rw [heUp]
      beta_reduce
      rw [hUe n]
      have hcancel : ∀ y z : ℂ, y * ((indexWeight n : ℂ) * z) / (indexWeight n : ℂ) = y * z :=
        fun y z => by field_simp [hw n]
      rw [hcancel]
      by_cases hz : xi n = 0
      · simp only [dif_pos hz]
        linear_combination (-(Complex.I * (-1 : ℂ) ^ n *
          NlsGge.Pilot.physicalFourier (iteratedDerivative N φ.1) (-n))) * hpow
      · simp only [dif_neg hz]
        linear_combination (-(Complex.I * (-1 : ℂ) ^ n *
          NlsGge.Pilot.physicalFourier (iteratedDerivative N φ.1) (-n))) * hpow
  have h12 : ∀ n : ℤ,
      NlsGge.ThirdConsultation.KSPSWKB.endpointDiagonalLower N φ xi n =
          (-1 : ℂ) ^ n / (2 * Complex.I * xi n) *
            integralRiccatiLeft φ (N + 1) +
          e1 n / (indexValue n : ℂ) ∧
        NlsGge.ThirdConsultation.KSPSWKB.endpointDiagonalUpper N φ xi n =
          (-1 : ℂ) ^ (n + 1) / (2 * Complex.I * xi n) *
            integralRiccatiRight φ (N + 1) +
          e2 n / (indexValue n : ℂ) := by
    intro n
    refine ⟨?_, ?_⟩
    · show _ = _ + (indexWeight n : ℂ) * _ / (indexWeight n : ℂ)
      rw [mul_div_cancel_left₀ _ (hw n)]
      ring
    · show _ = _ + (indexWeight n : ℂ) * _ / (indexWeight n : ℂ)
      rw [mul_div_cancel_left₀ _ (hw n)]
      ring
  have hUpn : ∀ n : ℤ, ‖eUp n‖ = ‖eU n‖ := fun n => by
    rw [heUp]; beta_reduce
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  have hpt : ∀ n ∈ F,
      0 ≤ indexWeight n ^ (N + 1) * ‖KSPSWKB.endpointEntryError N φ upper i j n‖ ∧
      indexWeight n ^ (N + 1) * ‖KSPSWKB.endpointEntryError N φ upper i j n‖ ≤
        ‖e1 n‖ + ‖e2 n‖ + A * ‖physicalFourier (iteratedDerivative N φ.1) (-n)‖ +
          A * ‖physicalFourier (iteratedDerivative N φ.2) n‖ + ‖eU n‖ + ‖eL n‖ := by
    intro n hn
    have hw1 := NlsGge.ThirdConsultation.KSPS015W.one_le_w n
    have tb := NlsGge.ThirdConsultation.KSPS026W.entry_tail_bound N φ upper xi hxe a ha hxi eL eUp e1 e2 n
      (h11 n) (h12 n) (hLR φ hφ) (hFT n hn) i j
    rw [hUpn n, ← hA] at tb
    refine ⟨mul_nonneg (pow_nonneg (by linarith) _) (norm_nonneg _), tb.trans (le_of_eq ?_)⟩
    ring
  obtain ⟨hP1, hP2⟩ := hfour φ hφ F hFo
  have hA1 : ∑ n ∈ F, (A * ‖physicalFourier (iteratedDerivative N φ.1) (-n)‖) ^ 2 ≤ A ^ 2 * P := by
    have e : ∑ n ∈ F, (A * ‖physicalFourier (iteratedDerivative N φ.1) (-n)‖) ^ 2 =
        A ^ 2 * ∑ n ∈ F, ‖physicalFourier (iteratedDerivative N φ.1) (-n)‖ ^ 2 := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun n _ => by ring)
    rw [e]; exact mul_le_mul_of_nonneg_left hP1 (sq_nonneg _)
  have hA2 : ∑ n ∈ F, (A * ‖physicalFourier (iteratedDerivative N φ.2) n‖) ^ 2 ≤ A ^ 2 * P := by
    have e : ∑ n ∈ F, (A * ‖physicalFourier (iteratedDerivative N φ.2) n‖) ^ 2 =
        A ^ 2 * ∑ n ∈ F, ‖physicalFourier (iteratedDerivative N φ.2) n‖ ^ 2 := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun n _ => by ring)
    rw [e]; exact mul_le_mul_of_nonneg_left hP2 (sq_nonneg _)
  have hs1 : ∑ n ∈ F, ‖e1 n‖ ^ 2 ≤ C1 := h1 φ hφ xi hxi F hF1
  have hs2 : ∑ n ∈ F, ‖e2 n‖ ^ 2 ≤ C2 := h2 φ hφ xi hxi F hF2
  exact NlsGge.ThirdConsultation.KSPSQ5C.sum_sq_le_six F _ (fun n => ‖e1 n‖) (fun n => ‖e2 n‖)
    (fun n => A * ‖physicalFourier (iteratedDerivative N φ.1) (-n)‖)
    (fun n => A * ‖physicalFourier (iteratedDerivative N φ.2) n‖) (fun n => ‖eU n‖) (fun n => ‖eL n‖)
    hpt _ _ _ _ _ _ hs1 hs2 hA1 hA2 (hUs F hFU) (hLs F hFL)

end
end NlsGge.ThirdConsultation.KSPS025U12
