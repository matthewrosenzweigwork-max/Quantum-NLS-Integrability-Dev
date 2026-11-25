import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS026Support2
import NlsGge.ThirdConsultation.KSPS.KSPS026Support5

                                                                                                                    
                                                                                                                      
                                                                                                               
                                                                                                  
                                                                                                  
                                                                                       
                                                                                                                    
                                                                                          
                                                                                                                
set_option autoImplicit false
open MeasureTheory Filter
open scoped BigOperators

namespace NlsGge.ThirdConsultation.KSPS026W
noncomputable section
open NlsGge.Pilot NlsGge.GK38 NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.KSPS

theorem endpoint_quadratic_expansion_of
    (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N)
    (h11 : ∀ xi : ℤ → ℂ, (∃ a : ℝ, 0 ≤ a ∧ ∀ n,
      ‖xi n - (n : ℂ) * Real.pi‖ ≤ a / indexWeight n) →
      ∃ eLower eUpper : ℤ → ℂ,
        SquareSummable eLower ∧ SquareSummable eUpper ∧
        ∀ n : ℤ,
          NlsGge.ThirdConsultation.KSPSWKB.endpointRemainderLower N φ xi n =
            Complex.I * ((-1 : ℂ) ^ (n + 1)) *
              NlsGge.Pilot.physicalFourier
                (NlsGge.ThirdConsultation.KSPS.iteratedDerivative N φ.2) n +
              eLower n / indexValue n ∧
          NlsGge.ThirdConsultation.KSPSWKB.endpointRemainderUpper N φ xi n =
            Complex.I * ((-1 : ℂ) ^ n) *
              NlsGge.Pilot.physicalFourier
                (NlsGge.ThirdConsultation.KSPS.iteratedDerivative N φ.1) (-n) +
              eUpper n / indexValue n)
    (h12 : ∀ xi : ℤ → ℂ, (∃ a : ℝ, 0 ≤ a ∧ ∀ n : ℤ,
      ‖xi n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n) →
      ∃ e1 e2 : ℤ → ℂ,
        SquareSummable e1 ∧ SquareSummable e2 ∧
        ∀ n : ℤ,
          NlsGge.ThirdConsultation.KSPSWKB.endpointDiagonalLower N φ xi n =
            (-1 : ℂ) ^ n / (2 * Complex.I * xi n) *
              integralRiccatiLeft φ (N + 1) +
            e1 n / (indexValue n : ℂ) ∧
          NlsGge.ThirdConsultation.KSPSWKB.endpointDiagonalUpper N φ xi n =
            (-1 : ℂ) ^ (n + 1) / (2 * Complex.I * xi n) *
              integralRiccatiRight φ (N + 1) +
            e2 n / (indexValue n : ℂ))
    (h13 : ∀ k : ℕ, (1 ≤ k ∧ k ≤ N + 1) → integralRiccatiLeft φ k = integralRiccatiRight φ k)
    (h14 : ∀ lam : {z : ℂ // z ≠ 0}, WKBThreshold N (sobolevNorm N φ) lam.1 →
      monodromyPair (toPotPair φ) lam.1 = KSPSWKB.explicitWKBMonodromy N φ lam)
    (h15 : ∀ xi : ℤ → ℂ, (∃ a : ℝ, 0 ≤ a ∧ ∀ n : ℤ,
      ‖xi n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n) →
      WeightedL2Error ((N + 1 : ℕ) : ℝ)
        (fun n : ℤ => NlsGge.ThirdConsultation.KSPS.discriminant φ (xi n) -
          2 * Complex.cos (NlsGge.ThirdConsultation.KSPS.wkbPhase φ (xi n))))
    (h20 : ∀ B : ℝ, 0 < B →
      ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ φ : SobolevC 1, sobolevNorm 1 φ ≤ B →
        ∀ n : ℤ, N ≤ n.natAbs →
          max ‖periodicPlus φ n-(n:ℂ)*Real.pi‖
              ‖periodicMinus φ n-(n:ℂ)*Real.pi‖ ≤
            C/(n.natAbs:ℝ)) :
    EndpointQuadraticWKB N φ := by
  obtain ⟨a, ha, hloc⟩ := periodic_localization_of hN φ h20
  have hP : ∀ n : ℤ, ‖periodicPlus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n := fun n => (hloc n).1
  have hM : ∀ n : ℤ, ‖periodicMinus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n := fun n => (hloc n).2
  have hxeP : ∀ n : ℤ, (if true then periodicPlus φ n else periodicMinus φ n) = periodicPlus φ n :=
    fun n => if_pos rfl
  have hxeM : ∀ n : ℤ, (if false then periodicPlus φ n else periodicMinus φ n) = periodicMinus φ n :=
    fun n => if_neg (by simp)
  have rootP : ∀ n : ℤ, NlsGge.ThirdConsultation.KSPS.discriminant φ (periodicPlus φ n) ^ 2 = 4 :=
    fun n => (periodic_disc_sq φ n).1
  have rootM : ∀ n : ℤ, NlsGge.ThirdConsultation.KSPS.discriminant φ (periodicMinus φ n) ^ 2 = 4 :=
    fun n => (periodic_disc_sq φ n).2
  obtain ⟨hplus, sP, eP⟩ := endpoint_side_of N hN φ true (periodicPlus φ) hxeP a ha hP
    (h11 _ ⟨a, ha, hP⟩) (h12 _ ⟨a, ha, hP⟩) h13 h14 (h15 _ ⟨a, ha, hP⟩) rootP
  obtain ⟨hminus, sM, eM⟩ := endpoint_side_of N hN φ false (periodicMinus φ) hxeM a ha hM
    (h11 _ ⟨a, ha, hM⟩) (h12 _ ⟨a, ha, hM⟩) h13 h14 (h15 _ ⟨a, ha, hM⟩) rootM
  refine ⟨?_, hplus, hminus, sP, sM, ?_⟩
  · intro upper i j
    cases upper
    · exact entry_errors_of N hN φ false (periodicMinus φ) hxeM a ha hM
        (h11 _ ⟨a, ha, hM⟩) (h12 _ ⟨a, ha, hM⟩) h13 i j
    · exact entry_errors_of N hN φ true (periodicPlus φ) hxeP a ha hP
        (h11 _ ⟨a, ha, hP⟩) (h12 _ ⟨a, ha, hP⟩) h13 i j
  · rw [Filter.cocompact_eq_cofinite]
    filter_upwards [eP, eM] with n hPn hMn
    obtain ⟨hp, hPq⟩ := hPn
    obtain ⟨hm, hMq⟩ := hMn
    exact ⟨hp, hm, hPq, hMq⟩

end
end NlsGge.ThirdConsultation.KSPS026W
