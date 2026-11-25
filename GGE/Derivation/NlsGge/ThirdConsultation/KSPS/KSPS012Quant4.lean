import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS012Host
import NlsGge.ThirdConsultation.KSPS.KSPS012Quant2
import NlsGge.ThirdConsultation.KSPSSupport.UNI01
import NlsGge.ThirdConsultation.KSPS.KSPS007Support6

/- KSPS012Q4 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/ThirdConsultation/KSPS/KSPS012Quant4.lean. Pro round-15 SUPPORT (never a packet).
   Ball-uniform TAIL finite-sum bounds of the weighted KSPS-012 diagonal remainders
     ‖w_n (endpointDiagonalLower − (−1)^n/(2iξ_n) I_{N+1})‖,  ‖w_n (endpointDiagonalUpper − (−1)^{n+1}/(2iξ_n) J_{N+1})‖,
   from (i) an explicit diag_approx hypothesis of EXACTLY the conclusion body of KSPS012Q3.diag_approx_false_U_of /
   _true_U_of for constants C, L (discharged in the glue module KSPSAntitraceUniform), (ii) KSPS012Q2.core_tail_U with
   ‖φ'.i‖ ≤ sobolevNorm 1 φ' ≤ B and ‖c_{N+1}‖ ≤ D (KSPSSupport.h161_coef_top on ‖φ.1‖+‖φ.2‖ ≤ KB). Per-index algebra
   copied from KSPS012Support11.diag_lower/upper_sq_summable; N0 and the constant are chosen before φ, φ', ξ, F.
   No hypothesis added beyond the documented diag_approx split. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Atomic.Common NlsGge.GK38
open NlsGge.Schur NlsGge.Analysis NlsGge.GKDefinitionDesign NlsGge.ThirdConsultation.KSPS

namespace NlsGge.ThirdConsultation.KSPS012Q4
open NlsGge.ThirdConsultation.KSPSWKB

theorem sum_sq_le_two {ι : Type*} (F : Finset ι) (x t1 t2 : ι → ℝ)
    (h : ∀ n ∈ F, 0 ≤ x n ∧ x n ≤ t1 n + t2 n) (T1 T2 : ℝ)
    (h1 : ∑ n ∈ F, t1 n ^ 2 ≤ T1) (h2 : ∑ n ∈ F, t2 n ^ 2 ≤ T2) :
    ∑ n ∈ F, x n ^ 2 ≤ 2 * (T1 + T2) := by
  have hp : ∀ n ∈ F, x n ^ 2 ≤ 2 * (t1 n ^ 2 + t2 n ^ 2) := by
    intro n hn
    obtain ⟨h0, hle⟩ := h n hn
    exact (pow_le_pow_left₀ h0 hle 2).trans (by nlinarith [sq_nonneg (t1 n - t2 n)])
  refine (Finset.sum_le_sum hp).trans ?_
  rw [← Finset.mul_sum]
  simp only [Finset.sum_add_distrib]
  linarith

theorem coef_top_norm_U (N : ℕ) (hN : 1 ≤ N) (KB : ℝ) (hKB : 0 ≤ KB) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ φ : SobolevC N, ‖φ.1‖ + ‖φ.2‖ ≤ KB → ∀ b : Bool,
      ‖NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b (N + 1)‖ ≤ D := by
  obtain ⟨D, hD, hTop⟩ := NlsGge.ThirdConsultation.KSPSSupport.h161_coef_top N hN KB hKB
  refine ⟨D, hD, fun φ hφ b => ?_⟩
  have h := hTop φ hφ b
  rw [Nat.sub_self, Nat.cast_zero, NlsGge.ThirdConsultation.KSPSSupport.h161_norm_eq_psn0] at h
  exact h

theorem integralRiccatiLeft_eq' {N : ℕ} (φ : SobolevC N) (k : ℕ) :
    integralRiccatiLeft φ k = ∫ x in (0 : ℝ)..1,
      coverRep38 (toPotPair φ).1 x * coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ false k) x := by
  unfold integralRiccatiLeft
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [coverRep38_ae_phys (toPotPair φ).1,
    coverRep38_ae_phys (riccatiLeft φ k)] with x h1 h2 _
  rw [h1]
  show _ = _ * coverRep38 (riccatiLeft φ k) x
  rw [h2]

theorem diag_lower_tail_of {N : ℕ} (hN : 1 ≤ N) (KB B : ℝ) (hKB : 0 ≤ KB) (hB : 0 ≤ B)
    (a : ℝ) (ha : 0 ≤ a) (C L : ℝ) (hC : 0 ≤ C) (hL1 : 1 ≤ L)
    (hap : ∀ φ : SobolevC N, ‖φ.1‖ + ‖φ.2‖ ≤ KB →
      ∀ φ' : SobolevC 1, sobolevNorm 1 φ' ≤ B →
      NlsGge.ThirdConsultation.KSPSVolterra.toPair φ' = toPotPair φ →
      ∀ lam : {z : ℂ // z ≠ 0}, L ≤ ‖lam.1‖ → |lam.1.im| ≤ a →
      ‖sourceRemainderVector φ false lam 1 0 -
        (-Complex.exp (-(2 * Complex.I * lam.1)) * endpointOsc lam.1 (fun t =>
          (∫ s in t..1, Complex.exp (2 * Complex.I * lam.1 * (s : ℂ)) *
            coverRep38 (physicalSobolevEmbed 1 φ'.1) s) *
          coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ false (N + 1)) t))‖ ≤
        C / ‖lam.1‖ ^ 2) :
    ∃ (N0 : ℕ) (Ct : ℝ), 0 ≤ Ct ∧ ∀ φ : SobolevC N, ‖φ.1‖ + ‖φ.2‖ ≤ KB →
      ∀ φ' : SobolevC 1, sobolevNorm 1 φ' ≤ B →
      NlsGge.ThirdConsultation.KSPSVolterra.toPair φ' = toPotPair φ →
      ∀ (xi : ℤ → ℂ), (∀ n : ℤ, ‖xi n - (n : ℂ) * Real.pi‖ ≤ a / indexWeight n) →
      ∀ F : Finset ℤ, (∀ n ∈ F, (N0 : ℤ) ≤ |n|) →
      ∑ n ∈ F, ‖(indexWeight n : ℂ) *
        (endpointDiagonalLower N φ xi n -
          (-1 : ℂ) ^ n / (2 * Complex.I * xi n) * integralRiccatiLeft φ (N + 1))‖ ^ 2 ≤ Ct := by
  obtain ⟨D, hD, hDb⟩ := coef_top_norm_U N hN KB hKB
  obtain ⟨Cc, hCc, hcore⟩ := NlsGge.ThirdConsultation.KSPS012Q2.core_tail_U a ha B D hB hD
  have hS0 := NlsGge.ThirdConsultation.KSPS012Q2.inv_tsum_nonneg
  refine ⟨max ⌈L + a + 2⌉₊ ⌈2 * a + 2⌉₊,
    2 * ((2 * C) ^ 2 * (∑' n : ℤ, (1 / |(n : ℝ)|) ^ 2) + Cc), by positivity,
    fun φ hφ φ' hφ'B hφ' xi hxi F hF => ?_⟩
  have hu : ‖φ'.1‖ ≤ B := (NlsGge.ThirdConsultation.KSPS007Support6.norm_fst_le_s φ').trans hφ'B
  have core := hcore φ'.1 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ false (N + 1)) hu
    (hDb φ hφ false) xi hxi 1 (Or.inl rfl) F (fun n hn =>
      le_trans (by exact_mod_cast le_max_right _ _) (hF n hn))
  simp only [Int.cast_one, one_mul] at core
  have huc : coverRep38 (physicalSobolevEmbed 1 φ'.1) = coverRep38 (toPotPair φ).1 := by
    rw [← hφ']; rfl
  have hP : integralRiccatiLeft φ (N + 1) = ∫ t in (0 : ℝ)..1,
      coverRep38 (physicalSobolevEmbed 1 φ'.1) t *
        coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ false (N + 1)) t := by
    rw [integralRiccatiLeft_eq', huc]
  refine sum_sq_le_two F _ (fun n => 2 * C * (1 / |(n : ℝ)|)) _ ?_ _ _ ?_ core
  · intro n hnF
    beta_reduce
    refine ⟨norm_nonneg _, ?_⟩
    have hn : ((⌈L + a + 2⌉₊ : ℕ) : ℤ) ≤ |n| :=
      le_trans (by exact_mod_cast le_max_left _ _) (hF n hnF)
    have hN0r : L + a + 2 ≤ ((⌈L + a + 2⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have hnabs : L + a + 2 ≤ |(n : ℝ)| := by
      have h1 : (((⌈L + a + 2⌉₊ : ℕ) : ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ) := Int.cast_le.2 hn
      rw [Int.cast_abs] at h1
      simp only [Int.cast_natCast] at h1
      linarith
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
    have happ := hap φ hφ φ' hφ'B hφ' ⟨xi n, hz⟩ hΛL himxi
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
      _ ≤ 2 * C * (1 / m) + indexWeight n * ‖X - (-1 : ℂ) ^ n / (2 * Complex.I * xi n) * P‖ := by
          linarith
  · simp_rw [mul_pow]
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (NlsGge.ThirdConsultation.KSPS012Q2.inv_sum_le F) (by positivity)

theorem diag_upper_tail_of {N : ℕ} (hN : 1 ≤ N) (KB B : ℝ) (hKB : 0 ≤ KB) (hB : 0 ≤ B)
    (a : ℝ) (ha : 0 ≤ a) (C L : ℝ) (hC : 0 ≤ C) (hL1 : 1 ≤ L)
    (hap : ∀ φ : SobolevC N, ‖φ.1‖ + ‖φ.2‖ ≤ KB →
      ∀ φ' : SobolevC 1, sobolevNorm 1 φ' ≤ B →
      NlsGge.ThirdConsultation.KSPSVolterra.toPair φ' = toPotPair φ →
      ∀ lam : {z : ℂ // z ≠ 0}, L ≤ ‖lam.1‖ → |lam.1.im| ≤ a →
      ‖sourceRemainderVector φ true lam 1 1 -
        (-Complex.exp (-(2 * Complex.I * (-lam.1))) * endpointOsc (-lam.1) (fun t =>
          (∫ s in t..1, Complex.exp (2 * Complex.I * (-lam.1) * (s : ℂ)) *
            coverRep38 (physicalSobolevEmbed 1 φ'.2) s) *
          coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ true (N + 1)) t))‖ ≤
        C / ‖lam.1‖ ^ 2) :
    ∃ (N0 : ℕ) (Ct : ℝ), 0 ≤ Ct ∧ ∀ φ : SobolevC N, ‖φ.1‖ + ‖φ.2‖ ≤ KB →
      ∀ φ' : SobolevC 1, sobolevNorm 1 φ' ≤ B →
      NlsGge.ThirdConsultation.KSPSVolterra.toPair φ' = toPotPair φ →
      ∀ (xi : ℤ → ℂ), (∀ n : ℤ, ‖xi n - (n : ℂ) * Real.pi‖ ≤ a / indexWeight n) →
      ∀ F : Finset ℤ, (∀ n ∈ F, (N0 : ℤ) ≤ |n|) →
      ∑ n ∈ F, ‖(indexWeight n : ℂ) *
        (endpointDiagonalUpper N φ xi n -
          (-1 : ℂ) ^ (n + 1) / (2 * Complex.I * xi n) * integralRiccatiRight φ (N + 1))‖ ^ 2 ≤ Ct := by
  obtain ⟨D, hD, hDb⟩ := coef_top_norm_U N hN KB hKB
  obtain ⟨Cc, hCc, hcore⟩ := NlsGge.ThirdConsultation.KSPS012Q2.core_tail_U a ha B D hB hD
  have hS0 := NlsGge.ThirdConsultation.KSPS012Q2.inv_tsum_nonneg
  refine ⟨max ⌈L + a + 2⌉₊ ⌈2 * a + 2⌉₊,
    2 * ((2 * C) ^ 2 * (∑' n : ℤ, (1 / |(n : ℝ)|) ^ 2) + Cc), by positivity,
    fun φ hφ φ' hφ'B hφ' xi hxi F hF => ?_⟩
  have hu : ‖φ'.2‖ ≤ B := (NlsGge.ThirdConsultation.KSPS007Support6.norm_snd_le_s φ').trans hφ'B
  have core := hcore φ'.2 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ true (N + 1)) hu
    (hDb φ hφ true) xi hxi (-1) (Or.inr rfl) F (fun n hn =>
      le_trans (by exact_mod_cast le_max_right _ _) (hF n hn))
  simp only [Int.cast_neg, Int.cast_one, neg_one_mul] at core
  have huc : coverRep38 (physicalSobolevEmbed 1 φ'.2) = coverRep38 (toPotPair φ).2 := by
    rw [← hφ']; rfl
  have hP : integralRiccatiRight φ (N + 1) = ∫ t in (0 : ℝ)..1,
      coverRep38 (physicalSobolevEmbed 1 φ'.2) t *
        coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ true (N + 1)) t := by
    unfold integralRiccatiRight
    rw [huc]
    rfl
  refine sum_sq_le_two F _ (fun n => 2 * C * (1 / |(n : ℝ)|)) _ ?_ _ _ ?_ core
  · intro n hnF
    beta_reduce
    refine ⟨norm_nonneg _, ?_⟩
    have hn : ((⌈L + a + 2⌉₊ : ℕ) : ℤ) ≤ |n| :=
      le_trans (by exact_mod_cast le_max_left _ _) (hF n hnF)
    have hN0r : L + a + 2 ≤ ((⌈L + a + 2⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have hnabs : L + a + 2 ≤ |(n : ℝ)| := by
      have h1 : (((⌈L + a + 2⌉₊ : ℕ) : ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ) := Int.cast_le.2 hn
      rw [Int.cast_abs] at h1
      simp only [Int.cast_natCast] at h1
      linarith
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
    have happ := hap φ hφ φ' hφ'B hφ' ⟨xi n, hz⟩ hΛL himxi
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
      _ ≤ 2 * C * (1 / m) + indexWeight n * ‖X - (-1 : ℂ) ^ n / (2 * Complex.I * -xi n) * P‖ := by
          linarith
  · simp_rw [mul_pow]
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (NlsGge.ThirdConsultation.KSPS012Q2.inv_sum_le F) (by positivity)

end NlsGge.ThirdConsultation.KSPS012Q4
