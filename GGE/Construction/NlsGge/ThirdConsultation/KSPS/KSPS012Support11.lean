import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS012Host
import NlsGge.ThirdConsultation.KSPS.KSPS012Support8
import NlsGge.ThirdConsultation.KSPS.KSPS012Support10

                                                                                                                      
                                                                                                           
                                                                                                      
                                                                            
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Atomic.Common NlsGge.GK38
open NlsGge.Schur NlsGge.Analysis NlsGge.GKDefinitionDesign NlsGge.ThirdConsultation.KSPS

namespace NlsGge.ThirdConsultation.KSPSWKB

theorem integralRiccatiLeft_eq {N : ℕ} (φ : SobolevC N) (k : ℕ) :
    integralRiccatiLeft φ k = ∫ x in (0 : ℝ)..1,
      coverRep38 (toPotPair φ).1 x * coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ false k) x := by
  unfold integralRiccatiLeft
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [coverRep38_ae_phys (toPotPair φ).1,
    coverRep38_ae_phys (riccatiLeft φ k)] with x h1 h2 _
  rw [h1]
  show _ = _ * coverRep38 (riccatiLeft φ k) x
  rw [h2]

theorem integralRiccatiRight_eq {N : ℕ} (φ : SobolevC N) (k : ℕ) :
    integralRiccatiRight φ k = ∫ x in (0 : ℝ)..1,
      coverRep38 (toPotPair φ).2 x * coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ true k) x := rfl

theorem diag_lower_sq_summable {N : ℕ} (hN : 1 ≤ N) (φ : SobolevC N) (a : ℝ) (ha : 0 ≤ a)
    (xi : ℤ → ℂ) (hxi : ∀ n : ℤ, ‖xi n - (n : ℂ) * Real.pi‖ ≤ a / indexWeight n) :
    SquareSummable (fun n : ℤ => (indexWeight n : ℂ) *
      (endpointDiagonalLower N φ xi n -
        (-1 : ℂ) ^ n / (2 * Complex.I * xi n) * integralRiccatiLeft φ (N + 1))) := by
  obtain ⟨φ', hφ'⟩ := NlsGge.ThirdConsultation.KSPS011Support4.exists_toPair_eq hN φ
  obtain ⟨C, L, hC, hL1, hap⟩ := diag_approx_false hN φ φ' hφ' a ha
  have core := core_l2 φ'.1 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ false (N + 1)) a ha
    xi hxi 1 (Or.inl rfl)
  simp only [Int.cast_one, one_mul] at core
  have hu : coverRep38 (physicalSobolevEmbed 1 φ'.1) = coverRep38 (toPotPair φ).1 := by
    rw [← hφ']; rfl
  have hP : integralRiccatiLeft φ (N + 1) = ∫ t in (0 : ℝ)..1,
      coverRep38 (physicalSobolevEmbed 1 φ'.1) t *
        coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ false (N + 1)) t := by
    rw [integralRiccatiLeft_eq, hu]
  have S_inv := realSqSummable_inv_abs
  have Stot := (S_inv.mul_left (2 * C)).add core
  set N0 : ℕ := ⌈L + a + 2⌉₊ with hN0
  refine squareSummable_of_bound _ _ Stot 1 N0 (fun n hn => ?_) (fun n => ?_)
  swap
  · beta_reduce
    have hn1 := indexWeight_pos n
    refine add_nonneg (by positivity) (by positivity)
  have hN0r : L + a + 2 ≤ (N0 : ℝ) := Nat.le_ceil _
  have hnabs : L + a + 2 ≤ |(n : ℝ)| := by
    have h1 : ((N0 : ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ) := Int.cast_le.2 hn
    rw [Int.cast_abs] at h1
    simp only [Int.cast_natCast] at h1
    linarith
  have hL0 : 1 ≤ L := hL1
  have hm1 : 1 ≤ |(n : ℝ)| := by linarith
  set m : ℝ := |(n : ℝ)| with hmdef
  have hmpos : 0 < m := by linarith
  have hw := indexWeight_pos n
  have hwm : indexWeight n ≤ 2 * m := iw_le_two_mul n hm1
  obtain ⟨hlow, himxi⟩ := xi_lower_bound a xi hxi n
  have hπ : 3 ≤ Real.pi := Real.pi_gt_three.le
  have hΛm : m ≤ ‖xi n‖ := by nlinarith [mul_le_mul_of_nonneg_right hπ hmpos.le]
  have hΛL : L ≤ ‖xi n‖ := by linarith
  have hΛpos : 0 < ‖xi n‖ := by linarith
  have hz : xi n ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hΛpos; exact lt_irrefl _ hΛpos
  have happ := hap ⟨xi n, hz⟩ hΛL himxi
  dsimp only at happ
  unfold endpointDiagonalLower
  beta_reduce
  rw [dif_neg hz, hP, norm_mul, Complex.norm_real, Real.norm_of_nonneg hw.le]
  set R := sourceRemainderVector φ false ⟨xi n, hz⟩ 1 0 with hR
  set X := -Complex.exp (-(2 * Complex.I * xi n)) * endpointOsc (xi n) (fun t =>
          (∫ s in t..1, Complex.exp (2 * Complex.I * xi n * (s : ℂ)) *
            coverRep38 (physicalSobolevEmbed 1 φ'.1) s) *
          coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ false (N + 1)) t) with hX
  set P := ∫ t in (0 : ℝ)..1, coverRep38 (physicalSobolevEmbed 1 φ'.1) t *
        coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ false (N + 1)) t with hPdef
  have e : R - (-1 : ℂ) ^ n / (2 * Complex.I * xi n) * P =
      (R - X) + (X - (-1 : ℂ) ^ n / (2 * Complex.I * xi n) * P) := by ring
  rw [e]
  have h1 : indexWeight n * ‖R - X‖ ≤ 2 * C * (1 / m) := by
    have : ‖R - X‖ ≤ C / ‖xi n‖ ^ 2 := by simpa [hR, hX] using happ
    have h2 : C / ‖xi n‖ ^ 2 ≤ C / m ^ 2 :=
      div_le_div_of_nonneg_left hC (by positivity) (by nlinarith)
    calc indexWeight n * ‖R - X‖ ≤ (2 * m) * (C / m ^ 2) :=
          mul_le_mul hwm (this.trans h2) (norm_nonneg _) (by positivity)
      _ = 2 * C * (1 / m) := by field_simp
  have h3 := norm_add_le (R - X) (X - (-1 : ℂ) ^ n / (2 * Complex.I * xi n) * P)
  calc indexWeight n * ‖(R - X) + (X - (-1 : ℂ) ^ n / (2 * Complex.I * xi n) * P)‖
      ≤ indexWeight n * (‖R - X‖ + ‖X - (-1 : ℂ) ^ n / (2 * Complex.I * xi n) * P‖) :=
        mul_le_mul_of_nonneg_left h3 hw.le
    _ = indexWeight n * ‖R - X‖ + indexWeight n * ‖X - (-1 : ℂ) ^ n / (2 * Complex.I * xi n) * P‖ := by
        ring
    _ ≤ 1 * (2 * C * (1 / m) + indexWeight n * ‖X - (-1 : ℂ) ^ n / (2 * Complex.I * xi n) * P‖) := by
        rw [one_mul]; linarith

theorem diag_upper_sq_summable {N : ℕ} (hN : 1 ≤ N) (φ : SobolevC N) (a : ℝ) (ha : 0 ≤ a)
    (xi : ℤ → ℂ) (hxi : ∀ n : ℤ, ‖xi n - (n : ℂ) * Real.pi‖ ≤ a / indexWeight n) :
    SquareSummable (fun n : ℤ => (indexWeight n : ℂ) *
      (endpointDiagonalUpper N φ xi n -
        (-1 : ℂ) ^ (n + 1) / (2 * Complex.I * xi n) * integralRiccatiRight φ (N + 1))) := by
  obtain ⟨φ', hφ'⟩ := NlsGge.ThirdConsultation.KSPS011Support4.exists_toPair_eq hN φ
  obtain ⟨C, L, hC, hL1, hap⟩ := diag_approx_true hN φ φ' hφ' a ha
  have core := core_l2 φ'.2 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ true (N + 1)) a ha
    xi hxi (-1) (Or.inr rfl)
  simp only [Int.cast_neg, Int.cast_one, neg_one_mul] at core
  have hu : coverRep38 (physicalSobolevEmbed 1 φ'.2) = coverRep38 (toPotPair φ).2 := by
    rw [← hφ']; rfl
  have hP : integralRiccatiRight φ (N + 1) = ∫ t in (0 : ℝ)..1,
      coverRep38 (physicalSobolevEmbed 1 φ'.2) t *
        coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ true (N + 1)) t := by
    rw [integralRiccatiRight_eq, hu]
  have S_inv := realSqSummable_inv_abs
  have Stot := (S_inv.mul_left (2 * C)).add core
  set N0 : ℕ := ⌈L + a + 2⌉₊ with hN0
  refine squareSummable_of_bound _ _ Stot 1 N0 (fun n hn => ?_) (fun n => ?_)
  swap
  · beta_reduce
    have hn1 := indexWeight_pos n
    refine add_nonneg (by positivity) (by positivity)
  have hN0r : L + a + 2 ≤ (N0 : ℝ) := Nat.le_ceil _
  have hnabs : L + a + 2 ≤ |(n : ℝ)| := by
    have h1 : ((N0 : ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ) := Int.cast_le.2 hn
    rw [Int.cast_abs] at h1
    simp only [Int.cast_natCast] at h1
    linarith
  have hL0 : 1 ≤ L := hL1
  have hm1 : 1 ≤ |(n : ℝ)| := by linarith
  set m : ℝ := |(n : ℝ)| with hmdef
  have hmpos : 0 < m := by linarith
  have hw := indexWeight_pos n
  have hwm : indexWeight n ≤ 2 * m := iw_le_two_mul n hm1
  obtain ⟨hlow, himxi⟩ := xi_lower_bound a xi hxi n
  have hπ : 3 ≤ Real.pi := Real.pi_gt_three.le
  have hΛm : m ≤ ‖xi n‖ := by nlinarith [mul_le_mul_of_nonneg_right hπ hmpos.le]
  have hΛL : L ≤ ‖xi n‖ := by linarith
  have hΛpos : 0 < ‖xi n‖ := by linarith
  have hz : xi n ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hΛpos; exact lt_irrefl _ hΛpos
  have happ := hap ⟨xi n, hz⟩ hΛL himxi
  dsimp only at happ
  unfold endpointDiagonalUpper
  beta_reduce
  rw [dif_neg hz, hP, norm_mul, Complex.norm_real, Real.norm_of_nonneg hw.le]
  set R := sourceRemainderVector φ true ⟨xi n, hz⟩ 1 1 with hR
  set X := -Complex.exp (-(2 * Complex.I * -xi n)) * endpointOsc (-xi n) (fun t =>
          (∫ s in t..1, Complex.exp (2 * Complex.I * -xi n * (s : ℂ)) *
            coverRep38 (physicalSobolevEmbed 1 φ'.2) s) *
          coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ true (N + 1)) t) with hX
  set P := ∫ t in (0 : ℝ)..1, coverRep38 (physicalSobolevEmbed 1 φ'.2) t *
        coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ true (N + 1)) t with hPdef
  have hlead : (-1 : ℂ) ^ (n + 1) / (2 * Complex.I * xi n) * P =
      (-1 : ℂ) ^ n / (2 * Complex.I * -xi n) * P := by
    rw [zpow_add_one₀ (by norm_num : (-1 : ℂ) ≠ 0)]
    have : (2 * Complex.I * xi n) ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) hz
    field_simp
  have e : R - (-1 : ℂ) ^ (n + 1) / (2 * Complex.I * xi n) * P =
      (R - X) + (X - (-1 : ℂ) ^ n / (2 * Complex.I * -xi n) * P) := by
    rw [hlead]; ring
  rw [e]
  have h1 : indexWeight n * ‖R - X‖ ≤ 2 * C * (1 / m) := by
    have : ‖R - X‖ ≤ C / ‖xi n‖ ^ 2 := by simpa [hR, hX] using happ
    have h2 : C / ‖xi n‖ ^ 2 ≤ C / m ^ 2 :=
      div_le_div_of_nonneg_left hC (by positivity) (by nlinarith)
    calc indexWeight n * ‖R - X‖ ≤ (2 * m) * (C / m ^ 2) :=
          mul_le_mul hwm (this.trans h2) (norm_nonneg _) (by positivity)
      _ = 2 * C * (1 / m) := by field_simp
  have h3 := norm_add_le (R - X) (X - (-1 : ℂ) ^ n / (2 * Complex.I * -xi n) * P)
  calc indexWeight n * ‖(R - X) + (X - (-1 : ℂ) ^ n / (2 * Complex.I * -xi n) * P)‖
      ≤ indexWeight n * (‖R - X‖ + ‖X - (-1 : ℂ) ^ n / (2 * Complex.I * -xi n) * P‖) :=
        mul_le_mul_of_nonneg_left h3 hw.le
    _ = indexWeight n * ‖R - X‖ + indexWeight n * ‖X - (-1 : ℂ) ^ n / (2 * Complex.I * -xi n) * P‖ := by
        ring
    _ ≤ 1 * (2 * C * (1 / m) + indexWeight n * ‖X - (-1 : ℂ) ^ n / (2 * Complex.I * -xi n) * P‖) := by
        rw [one_mul]; linarith

end NlsGge.ThirdConsultation.KSPSWKB
