import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS017Support2
import NlsGge.ThirdConsultation.KSPS.KSPS017Support5
import NlsGge.ThirdConsultation.KSPS.KSPS017Support8
import NlsGge.ThirdConsultation.KSPS.KSPS017Support10
import NlsGge.ThirdConsultation.KSPS.KSPS012Support11

                                                                                                                    
                                                                                                                 
                                                                                                   
                                                                                                                  
                                                     
                                                                     
                                                                                                                 
                                            
set_option autoImplicit false
open MeasureTheory Set Filter
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Atomic.Common NlsGge.GK38
open NlsGge.Schur NlsGge.Analysis NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.KSPS017W
noncomputable section
open NlsGge.ThirdConsultation.KSPS

theorem h17o_holds {N : ℕ} (hN : 1 ≤ N) (φ : SobolevC N) (xi : ℤ → ℂ) (a : ℝ) (ha : 0 ≤ a)
    (hxi : ∀ n : ℤ, ‖xi n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n) :
    ∃ fU fL : ℤ → ℂ, SquareSummable fU ∧ SquareSummable fL ∧ ∀ n : ℤ,
      ‖deriv (Rfun φ true 0) (xi n)‖ ≤ ‖fU n‖ ∧ ‖deriv (Rfun φ false 1) (xi n)‖ ≤ ‖fL n‖ := by
  have hU := offdiag_deriv_sq_summable hN φ true a ha xi hxi (Rfun φ true 0)
    (fun z hz => Rfun_differentiableAt φ true 0 hz) (fun z hz => by simp [Rfun, hz])
  have hL := offdiag_deriv_sq_summable hN φ false a ha xi hxi (Rfun φ false 1)
    (fun z hz => Rfun_differentiableAt φ false 1 hz) (fun z hz => by simp [Rfun, hz])
  refine ⟨fun n => ((‖deriv (Rfun φ true 0) (xi n)‖ : ℝ) : ℂ),
    fun n => ((‖deriv (Rfun φ false 1) (xi n)‖ : ℝ) : ℂ), ?_, ?_, fun n => ⟨?_, ?_⟩⟩
  · unfold SquareSummable; simpa using hU
  · unfold SquareSummable; simpa using hL
  · simp
  · simp

theorem diag_deriv_expansion {N : ℕ} (hN : 1 ≤ N) (φ : SobolevC N) (b : Bool) (a : ℝ) (ha : 0 ≤ a)
    (xi : ℤ → ℂ) (hxi : ∀ n : ℤ, ‖xi n - (n : ℂ) * Real.pi‖ ≤ a / indexWeight n) :
    Summable (fun n : ℤ => (indexWeight n * ‖deriv (Rfun φ b (if b then 1 else 0)) (xi n) -
      -Complex.I * (-1 : ℂ) ^ n / (2 * Complex.I * xi n) *
        (if b then integralRiccatiRight φ (N + 1) else integralRiccatiLeft φ (N + 1))‖) ^ 2) := by
  obtain ⟨φ', hφ'⟩ := NlsGge.ThirdConsultation.KSPS011Support4.exists_toPair_eq hN φ
  obtain ⟨C, L, hC, hL, hs⟩ := diag_strip N hN φ φ' hφ' b (a + 1) (by linarith)
  have hJ : (∫ t in (0 : ℝ)..1, coverRep38 (physicalSobolevEmbed 1 (if b then φ'.2 else φ'.1)) t *
      coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b (N + 1)) t) =
      (if b then integralRiccatiRight φ (N + 1) else integralRiccatiLeft φ (N + 1)) := by
    cases b
    · rw [KSPSWKB.integralRiccatiLeft_eq, ← hφ']; rfl
    · rw [KSPSWKB.integralRiccatiRight_eq, ← hφ']; rfl
  refine diag_deriv_generic (if b then -1 else 1) (by cases b <;> simp)
    (c := coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b (N + 1)))
    (d := coverRep38 (physicalSobolevDerivative38 1 (if b then φ'.2 else φ'.1)))
    (NlsGge.ThirdConsultation.KSPSSupport.coverRep38_memLp_Icc _)
    (stronglyMeasurable_coverRep38 _).aestronglyMeasurable
    (intervalIntegrable_coverRep38_sq_one _) (intervalIntegrable_coverRep38_one _)
    (sobolevPointValue 1 (if b then φ'.2 else φ'.1) 1)
    (if b then integralRiccatiRight φ (N + 1) else integralRiccatiLeft φ (N + 1)) a ha xi hxi
    (Rfun φ b (if b then 1 else 0)) (fun z hz => Rfun_differentiableAt φ b _ hz)
    ⟨C, L, hC, hL, fun z hz hzL him => ?_⟩
  have h := hs z hz hzL him
  rw [hJ] at h
  have hR : Rfun φ b (if b then 1 else 0) z =
      KSPSWKB.sourceRemainderVector φ b ⟨z, hz⟩ 1 (if b then 1 else 0) := by
    unfold Rfun; rw [dif_neg hz]
  rw [hR]
  exact h

theorem h17d_holds {N : ℕ} (hN : 1 ≤ N) (φ : SobolevC N) (xi : ℤ → ℂ) (a : ℝ) (ha : 0 ≤ a)
    (hxi : ∀ n : ℤ, ‖xi n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n) :
    ∃ g1 g2 : ℤ → ℂ, SquareSummable g1 ∧ SquareSummable g2 ∧ ∀ n : ℤ,
      deriv (Rfun φ false 0) (xi n) =
          -Complex.I * (-1 : ℂ) ^ n / (2 * Complex.I * xi n) * integralRiccatiLeft φ (N + 1) +
            g1 n / (indexValue n : ℂ) ∧
      deriv (Rfun φ true 1) (xi n) =
          -Complex.I * (-1 : ℂ) ^ n / (2 * Complex.I * xi n) * integralRiccatiRight φ (N + 1) +
            g2 n / (indexValue n : ℂ) := by
  have hF := diag_deriv_expansion hN φ false a ha xi hxi
  have hT := diag_deriv_expansion hN φ true a ha xi hxi
  simp only [Bool.false_eq_true, ↓reduceIte] at hF hT
  have hw : ∀ n : ℤ, (indexWeight n : ℂ) ≠ 0 := fun n => by
    exact_mod_cast (indexWeight_pos n).ne'
  refine ⟨fun n => (indexWeight n : ℂ) * (deriv (Rfun φ false 0) (xi n) -
      -Complex.I * (-1 : ℂ) ^ n / (2 * Complex.I * xi n) * integralRiccatiLeft φ (N + 1)),
    fun n => (indexWeight n : ℂ) * (deriv (Rfun φ true 1) (xi n) -
      -Complex.I * (-1 : ℂ) ^ n / (2 * Complex.I * xi n) * integralRiccatiRight φ (N + 1)),
    ?_, ?_, fun n => ⟨?_, ?_⟩⟩
  · unfold SquareSummable
    refine hF.congr (fun n => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (indexWeight_pos n).le]
  · unfold SquareSummable
    refine hT.congr (fun n => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (indexWeight_pos n).le]
  · show _ = _ + (indexWeight n : ℂ) * _ / (indexWeight n : ℂ)
    rw [mul_div_cancel_left₀ _ (hw n)]
    ring
  · show _ = _ + (indexWeight n : ℂ) * _ / (indexWeight n : ℂ)
    rw [mul_div_cancel_left₀ _ (hw n)]
    ring

end
end NlsGge.ThirdConsultation.KSPS017W
