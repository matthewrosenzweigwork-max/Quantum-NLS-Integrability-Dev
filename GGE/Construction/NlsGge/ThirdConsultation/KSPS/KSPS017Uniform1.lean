import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS017Support8
import NlsGge.ThirdConsultation.KSPS.KSPS011Quant1
import NlsGge.ThirdConsultation.KSPS.KSPS012Quant1
import NlsGge.ThirdConsultation.KSPS.KSPS017Uniform0

                                                                                 
                                                                                                                  
                                                                                                 
                                                                                                         
                                                                            
                                             
                                                                                                             
                                                        
                                                                                                                
                                                                                                               
                                                                                                    
                          
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped BigOperators Topology

namespace NlsGge.ThirdConsultation.KSPS017U1
noncomputable section
open NlsGge.Pilot NlsGge.GK38
open NlsGge.ThirdConsultation.KSPS NlsGge.ThirdConsultation.KSPS017W
open NlsGge.ThirdConsultation.KSPS017U0

theorem integral_norm_le_of_sq {c : ℝ → ℂ} (hc1 : IntervalIntegrable c volume 0 1)
    (hc2 : IntervalIntegrable (fun t => ‖c t‖ ^ 2) volume 0 1) :
    ∫ t in (0 : ℝ)..1, ‖c t‖ ≤ (1 + ∫ t in (0 : ℝ)..1, ‖c t‖ ^ 2) / 2 := by
  have hg : IntervalIntegrable (fun t => (1 + ‖c t‖ ^ 2) / 2) volume 0 1 :=
    (intervalIntegrable_const.add hc2).div_const 2
  have h1 : ∫ t in (0 : ℝ)..1, ‖c t‖ ≤ ∫ t in (0 : ℝ)..1, (1 + ‖c t‖ ^ 2) / 2 :=
    intervalIntegral.integral_mono_on zero_le_one hc1.norm hg
      (fun t _ => by nlinarith [sq_nonneg (‖c t‖ - 1)])
  have h2 : ∫ t in (0 : ℝ)..1, (1 + ‖c t‖ ^ 2) / 2 = (1 + ∫ t in (0 : ℝ)..1, ‖c t‖ ^ 2) / 2 := by
    rw [intervalIntegral.integral_div, intervalIntegral.integral_add intervalIntegrable_const hc2]
    simp
  linarith

/-- Tz at the lattice points σnπ is the integral of KSPS012Q1.T_sum_le. -/
theorem Tz_lattice (c d : ℝ → ℂ) (k : ℤ) :
    NlsGge.ThirdConsultation.KSPS012Support5.Tz c d ((k : ℂ) * (Real.pi : ℂ)) =
      ∫ t in (0 : ℝ)..1, (Complex.exp (-(2 * Real.pi * Complex.I * k * t)) * c t) *
        ∫ s in t..1, Complex.exp (2 * Real.pi * Complex.I * k * s) * d s := by
  unfold NlsGge.ThirdConsultation.KSPS012Support5.Tz
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  have e1 : Complex.exp (-(2 * Complex.I * ((k : ℂ) * (Real.pi : ℂ)) * (t : ℂ))) =
      Complex.exp (-(2 * Real.pi * Complex.I * k * t)) := by congr 1; ring
  have e2 : ∫ s in t..1, Complex.exp (2 * Complex.I * ((k : ℂ) * (Real.pi : ℂ)) * (s : ℂ)) * d s =
      ∫ s in t..1, Complex.exp (2 * Real.pi * Complex.I * k * s) * d s := by
    refine intervalIntegral.integral_congr (fun s _ => ?_)
    have : Complex.exp (2 * Complex.I * ((k : ℂ) * (Real.pi : ℂ)) * (s : ℂ)) =
        Complex.exp (2 * Real.pi * Complex.I * k * s) := by congr 1; ring
    rw [this]
  rw [e1, e2]

/-- Finite Bessel bound for Tz at σnπ. -/
theorem Tz_lattice_sum_le {c d : ℝ → ℂ} (hcm : AEStronglyMeasurable c volume)
    (hc1 : IntervalIntegrable c volume 0 1)
    (hc2 : IntervalIntegrable (fun t => ‖c t‖ ^ 2) volume 0 1)
    (hd : IntervalIntegrable d volume 0 1) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) (F : Finset ℤ) :
    ∑ n ∈ F, ‖NlsGge.ThirdConsultation.KSPS012Support5.Tz c d (((σ * n : ℤ) : ℂ) * (Real.pi : ℂ))‖ ^ 2 ≤
      (∫ s in (0 : ℝ)..1, ‖d s‖) * ((∫ s in (0 : ℝ)..1, ‖d s‖) * ∫ t in (0 : ℝ)..1, ‖c t‖ ^ 2) := by
  have h := NlsGge.ThirdConsultation.KSPS012Q1.T_sum_le hcm hc1 hc2 hd
  rcases hσ with rfl | rfl
  · refine le_trans (le_of_eq ?_) (h F)
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [one_mul, Tz_lattice]
  · refine le_trans (le_of_eq ?_) (h (F.image (fun n => -n)))
    rw [NlsGge.ThirdConsultation.KSPSQ1.sum_neg_reindex]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    beta_reduce
    rw [show (-1 : ℤ) * -m = m by ring, Tz_lattice]

/-- Finite Bessel bound for Tz along σξ_n on the tail |n| ≥ 2a+1. -/
theorem Tz_xi_sum_le {c d : ℝ → ℂ} (hcm : AEStronglyMeasurable c volume)
    (hc1 : IntervalIntegrable c volume 0 1)
    (hc2 : IntervalIntegrable (fun t => ‖c t‖ ^ 2) volume 0 1)
    (hd : IntervalIntegrable d volume 0 1) (a : ℝ) (ha : 0 ≤ a) (xi : ℤ → ℂ)
    (hxi : ∀ n : ℤ, ‖xi n - (n : ℂ) * Real.pi‖ ≤ a / indexWeight n)
    (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) (F : Finset ℤ) (hF : ∀ n ∈ F, 2 * a + 1 ≤ |(n : ℝ)|) :
    ∑ n ∈ F, ‖NlsGge.ThirdConsultation.KSPS012Support5.Tz c d ((σ : ℂ) * xi n)‖ ^ 2 ≤
      1 ^ 2 * ((2 : ℕ) * ((∫ s in (0 : ℝ)..1, ‖d s‖) * ((∫ s in (0 : ℝ)..1, ‖d s‖) *
          ∫ t in (0 : ℝ)..1, ‖c t‖ ^ 2) +
        (4 * (Real.exp (2 * a) + 1) * (∫ s in (0 : ℝ)..1, ‖d s‖) * (∫ t in (0 : ℝ)..1, ‖c t‖) * a) ^ 2 *
          ∑' n : ℤ, (1 / |(n : ℝ)|) ^ 2)) := by
  set K : ℝ := 4 * (Real.exp (2 * a) + 1) * (∫ s in (0 : ℝ)..1, ‖d s‖) * ∫ t in (0 : ℝ)..1, ‖c t‖ with hK
  have hK0 : 0 ≤ K := by
    have := intervalIntegral.integral_nonneg (μ := volume) zero_le_one
      (fun s (_ : s ∈ Icc (0 : ℝ) 1) => norm_nonneg (d s))
    have := intervalIntegral.integral_nonneg (μ := volume) zero_le_one
      (fun s (_ : s ∈ Icc (0 : ℝ) 1) => norm_nonneg (c s))
    rw [hK]; positivity
  have hpt : ∀ n ∈ F, ‖NlsGge.ThirdConsultation.KSPS012Support5.Tz c d ((σ : ℂ) * xi n)‖ ≤
      ‖NlsGge.ThirdConsultation.KSPS012Support5.Tz c d (((σ * n : ℤ) : ℂ) * (Real.pi : ℂ))‖ +
        K * a * (1 / |(n : ℝ)|) := by
    intro n hn
    have hnR := hF n hn
    have hn1 : 1 ≤ |(n : ℝ)| := by linarith
    have hn0 : 0 < |(n : ℝ)| := by linarith
    have hw : |(n : ℝ)| ≤ indexWeight n := by
      unfold indexWeight; exact Real.abs_le_sqrt (by nlinarith [sq_nonneg (n : ℝ)])
    have hδ0 : ‖xi n - (n : ℂ) * Real.pi‖ ≤ a / |(n : ℝ)| :=
      (hxi n).trans (div_le_div_of_nonneg_left ha hn0 hw)
    have hδ : ‖(σ : ℂ) * xi n - (((σ * n : ℤ) : ℂ)) * (Real.pi : ℂ)‖ ≤ a / |(n : ℝ)| := by
      have e : (σ : ℂ) * xi n - (((σ * n : ℤ) : ℂ)) * (Real.pi : ℂ) =
          (σ : ℂ) * (xi n - (n : ℂ) * Real.pi) := by push_cast; ring
      have hs1 : ‖(σ : ℂ)‖ = 1 := by rcases hσ with rfl | rfl <;> simp
      rw [e, norm_mul, hs1, one_mul]; exact hδ0
    have hhalf : a / |(n : ℝ)| ≤ 1 / 2 := by
      rw [div_le_iff₀ hn0]; linarith
    have him : |((σ : ℂ) * xi n).im| ≤ a := by
      have h1 : |(xi n).im| ≤ a := by
        have : (xi n).im = (xi n - (n : ℂ) * Real.pi).im := by simp
        rw [this]
        exact (Complex.abs_im_le_norm _).trans (hδ0.trans (div_le_self ha hn1))
      rcases hσ with rfl | rfl <;> simpa using h1
    have hlip := NlsGge.ThirdConsultation.KSPS012Support5.Tz_lip hc1 hd ha (σ * n) him (hδ.trans hhalf)
    have hlip' : ‖NlsGge.ThirdConsultation.KSPS012Support5.Tz c d ((σ : ℂ) * xi n) -
        NlsGge.ThirdConsultation.KSPS012Support5.Tz c d (((σ * n : ℤ) : ℂ) * (Real.pi : ℂ))‖ ≤
        K * ‖(σ : ℂ) * xi n - (((σ * n : ℤ) : ℂ)) * (Real.pi : ℂ)‖ := by rw [hK]; exact hlip
    have h1 := norm_sub_norm_le (NlsGge.ThirdConsultation.KSPS012Support5.Tz c d ((σ : ℂ) * xi n))
      (NlsGge.ThirdConsultation.KSPS012Support5.Tz c d (((σ * n : ℤ) : ℂ) * (Real.pi : ℂ)))
    have h2 : K * ‖(σ : ℂ) * xi n - (((σ * n : ℤ) : ℂ)) * (Real.pi : ℂ)‖ ≤ K * a * (1 / |(n : ℝ)|) := by
      exact (mul_le_mul_of_nonneg_left hδ hK0).trans (le_of_eq (by ring))
    linarith [hlip']
  refine sum_sq_le_fin F _ ![fun n => ‖NlsGge.ThirdConsultation.KSPS012Support5.Tz c d
      (((σ * n : ℤ) : ℂ) * (Real.pi : ℂ))‖, fun n => K * a * (1 / |(n : ℝ)|)] 1 zero_le_one ?_
    ![(∫ s in (0 : ℝ)..1, ‖d s‖) * ((∫ s in (0 : ℝ)..1, ‖d s‖) * ∫ t in (0 : ℝ)..1, ‖c t‖ ^ 2),
      (K * a) ^ 2 * ∑' n : ℤ, (1 / |(n : ℝ)|) ^ 2] ?_ |>.trans (le_of_eq ?_)
  · intro n hn
    refine ⟨norm_nonneg _, ?_⟩
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, one_mul]
    exact hpt n hn
  · intro j
    fin_cases j
    · simpa using Tz_lattice_sum_le hcm hc1 hc2 hd σ hσ F
    · show ∑ n ∈ F, (K * a * (1 / |(n : ℝ)|)) ^ 2 ≤ (K * a) ^ 2 * ∑' n : ℤ, (1 / |(n : ℝ)|) ^ 2
      rw [show ∑ n ∈ F, (K * a * (1 / |(n : ℝ)|)) ^ 2 = (K * a) ^ 2 * ∑ n ∈ F, (1 / |(n : ℝ)|) ^ 2 by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun n _ => by ring)]
      exact mul_le_mul_of_nonneg_left (inv_abs_sum_le F) (sq_nonneg _)
  · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-- The pointwise estimate of diag_deriv_generic (landed body), on one tail index. -/
theorem diag_pointwise (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) {c d : ℝ → ℂ}
    (hc1 : IntervalIntegrable c volume 0 1) (hd : IntervalIntegrable d volume 0 1)
    (u1 J : ℂ) (a : ℝ) (ha : 0 ≤ a) (xi : ℤ → ℂ)
    (hxi : ∀ n : ℤ, ‖xi n - (n : ℂ) * Real.pi‖ ≤ a / indexWeight n)
    (g : ℂ → ℂ) (hgd : ∀ z : ℂ, z ≠ 0 → DifferentiableAt ℂ g z)
    (C L : ℝ) (hC : 0 ≤ C) (hL : 1 ≤ L)
    (happ : ∀ z : ℂ, z ≠ 0 → L ≤ ‖z‖ → |z.im| ≤ a + 1 → ‖g z - Pdiag σ c d u1 J z‖ ≤ C / ‖z‖ ^ 2)
    (n : ℤ) (hnabs : a + L + 2 ≤ |(n : ℝ)|) :
    indexWeight n * ‖deriv g (xi n) - -Complex.I * (-1 : ℂ) ^ n / (2 * Complex.I * xi n) * J‖ ≤
      ‖u1‖ * (‖NlsGge.ThirdConsultation.KSPSWKB.endpointOsc ((σ : ℂ) * xi n) c‖ +
        ‖NlsGge.ThirdConsultation.KSPSWKB.endpointOsc ((σ : ℂ) * xi n) (fun t => Complex.I * ((1 - 2 * t : ℝ) : ℂ) * c t)‖) +
      2 * Real.exp a * (‖NlsGge.ThirdConsultation.KSPS012Support5.Tz c d ((σ : ℂ) * xi n)‖ +
        2 * (‖NlsGge.ThirdConsultation.KSPS012Support5.Tz c (fun s => (s : ℂ) * d s) ((σ : ℂ) * xi n)‖ +
          ‖NlsGge.ThirdConsultation.KSPS012Support5.Tz (fun t => (t : ℂ) * c t) d ((σ : ℂ) * xi n)‖)) +
      (4 * C + Real.exp a * ‖J‖ + a * ‖J‖) * (1 / |(n : ℝ)|) := by
  have hσn : ‖(σ : ℂ)‖ = 1 := by rcases hσ with rfl | rfl <;> simp
  set H' : ℝ → ℂ := fun t => Complex.I * ((1 - 2 * t : ℝ) : ℂ) * c t with hH'def
  set ds : ℝ → ℂ := fun s => (s : ℂ) * d s with hdsdef
  set tc : ℝ → ℂ := fun t => (t : ℂ) * c t with htcdef
  set EA : ℝ := Real.exp a with hEA
  have hw1 := NlsGge.ThirdConsultation.KSPS.one_le_indexWeight n
  have hδ0 := hxi n
  have hπ : 3 ≤ Real.pi := Real.pi_gt_three.le
  have hm0 : 0 ≤ |(n : ℝ)| := abs_nonneg _
  have hnpi : ‖(n : ℂ) * (Real.pi : ℂ)‖ = Real.pi * |(n : ℝ)| := by
    rw [norm_mul, Complex.norm_intCast, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]; ring
  have hδa : a / indexWeight n ≤ a := div_le_self ha hw1
  have hX : |(n : ℝ)| + L + 2 ≤ ‖xi n‖ := by
    have h1 := norm_sub_norm_le ((n : ℂ) * (Real.pi : ℂ)) (xi n)
    rw [norm_sub_rev, hnpi] at h1
    have : 3 * |(n : ℝ)| ≤ Real.pi * |(n : ℝ)| := mul_le_mul_of_nonneg_right hπ hm0
    linarith
  have himξ : |(xi n).im| ≤ a := by
    have : (xi n).im = (xi n - (n : ℂ) * Real.pi).im := by simp
    rw [this]; exact (Complex.abs_im_le_norm _).trans (hδ0.trans hδa)
  have hn1 : 1 ≤ |(n : ℝ)| := by linarith
  have hNn : 0 < |(n : ℝ)| := by linarith
  have hNw : |(n : ℝ)| ≤ indexWeight n := by
    unfold indexWeight; exact Real.abs_le_sqrt (by nlinarith [sq_nonneg (n : ℝ)])
  have hwle : indexWeight n ≤ |(n : ℝ)| + 1 := by
    unfold indexWeight
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have : (n : ℝ) ^ 2 = |(n : ℝ)| ^ 2 := (sq_abs _).symm
    rw [this]; nlinarith
  have hwX : indexWeight n ≤ ‖xi n‖ := by linarith
  have hw0 : 0 < indexWeight n := by linarith
  have hX1 : 1 ≤ ‖xi n‖ := by linarith
  have hX2 : 2 ≤ ‖xi n‖ := by linarith
  have hz : xi n ≠ 0 := by intro h; rw [h, norm_zero] at hX2; norm_num at hX2
  -- Cauchy estimate for E = g - Pdiag
  set E : ℂ → ℂ := fun w => g w - Pdiag σ c d u1 J w with hEdef
  have hball : ∀ z ∈ Metric.closedBall (xi n) 1, ‖xi n‖ - 1 ≤ ‖z‖ ∧ |z.im| ≤ a + 1 := by
    intro z hzb
    rw [Metric.mem_closedBall, dist_eq_norm] at hzb
    have h1 := norm_sub_norm_le (xi n) z
    have h4 : ‖xi n - z‖ ≤ 1 := by rw [norm_sub_rev]; exact hzb
    have h2 : |z.im - (xi n).im| ≤ ‖z - xi n‖ := by rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _
    have h3 := abs_sub_abs_le_abs_sub z.im (xi n).im
    constructor <;> linarith
  have hEdb : ∀ z ∈ Metric.closedBall (xi n) 1, DifferentiableAt ℂ E z := by
    intro z hzb
    have h := (hball z hzb).1
    have hz0 : z ≠ 0 := by intro h0; rw [h0, norm_zero] at h; linarith
    exact (hgd z hz0).sub (hasDerivAt_Pdiag σ hσ hc1 hd u1 J hz0).differentiableAt
  have hEs : ∀ z ∈ Metric.sphere (xi n) 1, ‖E z‖ ≤ 4 * C / ‖xi n‖ ^ 2 := by
    intro z hzs
    obtain ⟨h1, h2⟩ := hball z (Metric.sphere_subset_closedBall hzs)
    have hz0 : z ≠ 0 := by intro h0; rw [h0, norm_zero] at h1; linarith
    refine (happ z hz0 (by linarith) h2).trans ?_
    have hzpos : 0 < ‖z‖ := by linarith
    have hhalf : ‖xi n‖ / 2 ≤ ‖z‖ := by linarith
    have hsq : (‖xi n‖ / 2) ^ 2 ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ (by positivity) hhalf 2
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : 4 * C * ‖z‖ ^ 2 - C * ‖xi n‖ ^ 2 = 4 * C * (‖z‖ ^ 2 - (‖xi n‖ / 2) ^ 2) := by ring
    nlinarith [mul_nonneg hC (sub_nonneg.2 hsq)]
  have hcauchy := norm_deriv_le_of_sphere one_pos hEdb hEs
  rw [div_one] at hcauchy
  have hP := hasDerivAt_Pdiag σ hσ hc1 hd u1 J hz
  have h1 := ((hgd (xi n) hz).hasDerivAt.sub hP)
  have hE' : deriv E (xi n) = deriv g (xi n) - _ := h1.deriv
  -- facts for diag_pure
  have hρn : ‖(2 * Complex.I * ((σ : ℂ) * xi n))⁻¹‖ = 1 / (2 * ‖xi n‖) := by
    rw [norm_inv, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_ofNat, hσn, mul_one, one_mul,
      one_div]
  have hρ'n : ‖-(2 * Complex.I * ((σ : ℂ) * xi n))⁻¹ * (xi n)⁻¹‖ ≤ 1 / (2 * ‖xi n‖ ^ 2) := by
    rw [norm_mul, norm_neg, hρn, norm_inv]
    apply le_of_eq; field_simp
  have hEAn : ‖Complex.exp (-(Complex.I * ((σ : ℂ) * xi n)))‖ ≤ EA := by
    rw [Complex.norm_exp, hEA]
    refine Real.exp_le_exp.2 ?_
    have hre : (-(Complex.I * ((σ : ℂ) * xi n))).re = ((σ : ℂ) * xi n).im := by simp
    rw [hre]
    have : |((σ : ℂ) * xi n).im| ≤ a := by rcases hσ with rfl | rfl <;> simpa using himξ
    exact (le_abs_self _).trans this
  have hρσ : (σ : ℂ) * (2 * Complex.I * ((σ : ℂ) * xi n))⁻¹ = (2 * Complex.I * xi n)⁻¹ := by
    rcases hσ with rfl | rfl
    · simp
    · push_cast
      simp only [neg_one_mul, mul_neg, inv_neg, neg_neg]
  have hlead : ‖Complex.exp (-(Complex.I * ((σ : ℂ) * xi n))) - (-1 : ℂ) ^ n‖ ≤ 2 * a / indexWeight n := by
    rw [← exp_neg_I_pi_int8 σ n hσ]
    have hz0n : ‖Complex.exp (-(Complex.I * (((σ * n : ℤ) : ℂ) * (Real.pi : ℂ))))‖ = 1 := by
      rw [exp_neg_I_pi_int8 σ n hσ, norm_zpow, norm_neg, norm_one, one_zpow]
    have hdiff : ‖-(Complex.I * ((σ : ℂ) * xi n)) - -(Complex.I * (((σ * n : ℤ) : ℂ) * (Real.pi : ℂ)))‖ =
        ‖xi n - (n : ℂ) * Real.pi‖ := by
      have e : -(Complex.I * ((σ : ℂ) * xi n)) - -(Complex.I * (((σ * n : ℤ) : ℂ) * (Real.pi : ℂ))) =
          (-(Complex.I * (σ : ℂ))) * (xi n - (n : ℂ) * Real.pi) := by push_cast; ring
      rw [e, norm_mul, norm_neg, norm_mul, Complex.norm_I, hσn, one_mul, one_mul]
    have hle1 : ‖xi n - (n : ℂ) * Real.pi‖ ≤ 1 := by
      refine hδ0.trans ?_
      rw [div_le_one hw0]; linarith
    refine (NlsGge.ThirdConsultation.KSPS012Support5.exp_lip hz0n (by rw [hdiff]; exact hle1)).trans ?_
    rw [hdiff]
    have := mul_le_mul_of_nonneg_left hδ0 (by norm_num : (0 : ℝ) ≤ 2)
    calc 2 * ‖xi n - (n : ℂ) * Real.pi‖ ≤ 2 * (a / indexWeight n) := this
      _ = 2 * a / indexWeight n := by ring
  exact diag_pure (indexWeight n) ‖xi n‖ EA a |(n : ℝ)| C u1 J
    (NlsGge.ThirdConsultation.KSPSWKB.endpointOsc ((σ : ℂ) * xi n) c) (NlsGge.ThirdConsultation.KSPSWKB.endpointOsc ((σ : ℂ) * xi n) H')
    (NlsGge.ThirdConsultation.KSPS012Support5.Tz c d ((σ : ℂ) * xi n))
    (NlsGge.ThirdConsultation.KSPS012Support5.Tz c ds ((σ : ℂ) * xi n))
    (NlsGge.ThirdConsultation.KSPS012Support5.Tz tc d ((σ : ℂ) * xi n))
    (Complex.exp (-(Complex.I * ((σ : ℂ) * xi n)))) ((-1 : ℂ) ^ n)
    (2 * Complex.I * ((σ : ℂ) * xi n))⁻¹ (-(2 * Complex.I * ((σ : ℂ) * xi n))⁻¹ * (xi n)⁻¹) (σ : ℂ) (xi n)
    (deriv E (xi n)) (deriv g (xi n) - -Complex.I * (-1 : ℂ) ^ n / (2 * Complex.I * xi n) * J)
    hw0 hwX hX1 hNn (by linarith) hNw (by positivity) ha hC rfl hρn hρ'n hEAn hσn hρσ hlead hcauchy
    (by rw [hE']; ring)

/-- Uniform (finite-sum) S017-2, generic form: one constant K before c, d, u1, J, ξ, g, F. -/
theorem diag_deriv_tail_U (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) (a : ℝ) (ha : 0 ≤ a)
    (C L : ℝ) (hC : 0 ≤ C) (hL : 1 ≤ L) (Bu BJ Bc Bd : ℝ) (hBu : 0 ≤ Bu) (hBJ : 0 ≤ BJ)
    (hBc : 0 ≤ Bc) (hBd : 0 ≤ Bd) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (c d : ℝ → ℂ),
      MemLp c 2 NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure → AEStronglyMeasurable c volume →
      IntervalIntegrable (fun t => ‖c t‖ ^ 2) volume 0 1 → IntervalIntegrable d volume 0 1 →
      (∫ t in (0 : ℝ)..1, ‖c t‖ ^ 2) ≤ Bc → (∫ s in (0 : ℝ)..1, ‖d s‖) ≤ Bd →
      ∀ (u1 J : ℂ), ‖u1‖ ≤ Bu → ‖J‖ ≤ BJ →
      ∀ (xi : ℤ → ℂ), (∀ n : ℤ, ‖xi n - (n : ℂ) * Real.pi‖ ≤ a / indexWeight n) →
      ∀ (g : ℂ → ℂ), (∀ z : ℂ, z ≠ 0 → DifferentiableAt ℂ g z) →
      (∀ z : ℂ, z ≠ 0 → L ≤ ‖z‖ → |z.im| ≤ a + 1 → ‖g z - Pdiag σ c d u1 J z‖ ≤ C / ‖z‖ ^ 2) →
      ∀ F : Finset ℤ, (∀ n ∈ F, ((⌈2 * a + L + 2⌉₊ : ℕ) : ℤ) ≤ |n|) →
      ∑ n ∈ F, (indexWeight n *
        ‖deriv g (xi n) - -Complex.I * (-1 : ℂ) ^ n / (2 * Complex.I * xi n) * J‖) ^ 2 ≤ K := by
  set EA : ℝ := Real.exp a with hEA
  have hEA0 : 0 ≤ EA := (Real.exp_pos a).le
  set E2 : ℝ := Real.exp (2 * a) + 1 with hE2
  have hE20 : 0 ≤ E2 := by positivity
  set B1 : ℝ := (1 + Bc) / 2 with hB1
  have hB10 : 0 ≤ B1 := by positivity
  set Z : ℝ := ∑' n : ℤ, (1 / |(n : ℝ)|) ^ 2 with hZ
  have hZ0 : 0 ≤ Z := inv_abs_tsum_nonneg
  set TT : ℝ := 1 ^ 2 * ((2 : ℕ) * (Bd * (Bd * Bc) + (4 * E2 * Bd * B1 * a) ^ 2 * Z)) with hTT
  have hTT0 : 0 ≤ TT := by positivity
  set Km : ℝ := Bu + 4 * EA + (4 * C + EA * BJ + a * BJ) with hKm
  have hKm0 : 0 ≤ Km := by positivity
  refine ⟨Km ^ 2 * (((6 : ℕ) : ℝ) * (2 * E2 * Bc + 2 * E2 * Bc + TT + TT + TT + Z)), by positivity,
    fun c d hcmem hcm hc2 hd hBcc hBdd u1 J hu1 hJ xi hxi g hgd happ F hF => ?_⟩
  have hc1 : IntervalIntegrable c volume 0 1 := NlsGge.ThirdConsultation.KSPSWKB.intervalIntegrable_of_memLp hcmem
  set H' : ℝ → ℂ := fun t => Complex.I * ((1 - 2 * t : ℝ) : ℂ) * c t with hH'def
  have hH'mem : MemLp H' 2 NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure :=
    NlsGge.ThirdConsultation.KSPSSupport.h150_memLp_mul_bdd c (fun t => Complex.I * ((1 - 2 * t : ℝ) : ℂ))
      hcmem (Continuous.continuousOn (by fun_prop))
  set ds : ℝ → ℂ := fun s => (s : ℂ) * d s with hdsdef
  set tc : ℝ → ℂ := fun t => (t : ℂ) * c t with htcdef
  have hds : IntervalIntegrable ds volume 0 1 :=
    hd.continuousOn_mul (by fun_prop : Continuous fun s : ℝ => (s : ℂ)).continuousOn
  have htcm : AEStronglyMeasurable tc volume :=
    (by fun_prop : Continuous fun t : ℝ => (t : ℂ)).aestronglyMeasurable.mul hcm
  have htc1 : IntervalIntegrable tc volume 0 1 :=
    hc1.continuousOn_mul (by fun_prop : Continuous fun t : ℝ => (t : ℂ)).continuousOn
  have hcmp : ∀ t ∈ Icc (0 : ℝ) 1, ‖(t : ℂ)‖ ≤ 1 := by
    intro t ht
    rw [Complex.norm_real, Real.norm_of_nonneg ht.1]; exact ht.2
  have htc2 : IntervalIntegrable (fun t => ‖tc t‖ ^ 2) volume 0 1 := by
    refine hc2.mono_fun ((htcm.norm.pow 2).restrict) ?_
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    rw [uIoc_of_le zero_le_one] at ht
    simp only [htcdef, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (by positivity)]
    have h1 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
    calc t ^ 2 * ‖c t‖ ^ 2 ≤ 1 * ‖c t‖ ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      _ = ‖c t‖ ^ 2 := one_mul _
  have hH'm : AEStronglyMeasurable H' volume :=
    (by fun_prop : Continuous fun t : ℝ => Complex.I * ((1 - 2 * t : ℝ) : ℂ)).aestronglyMeasurable.mul hcm
  have hH'pt : ∀ t ∈ Icc (0 : ℝ) 1, ‖H' t‖ ^ 2 ≤ ‖c t‖ ^ 2 := by
    intro t ht
    simp only [hH'def, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    have h1 : (1 - 2 * t) ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
    calc (1 - 2 * t) ^ 2 * ‖c t‖ ^ 2 ≤ 1 * ‖c t‖ ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      _ = ‖c t‖ ^ 2 := one_mul _
  have hH'2 : IntervalIntegrable (fun t => ‖H' t‖ ^ 2) volume 0 1 := by
    refine hc2.mono_fun ((hH'm.norm.pow 2).restrict) ?_
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    rw [uIoc_of_le zero_le_one] at ht
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg _)]
    exact hH'pt t ⟨ht.1.le, ht.2⟩
  -- integral bounds
  have hLc0 : 0 ≤ ∫ t in (0 : ℝ)..1, ‖c t‖ :=
    intervalIntegral.integral_nonneg zero_le_one (fun _ _ => norm_nonneg _)
  have hLd0 : 0 ≤ ∫ s in (0 : ℝ)..1, ‖d s‖ :=
    intervalIntegral.integral_nonneg zero_le_one (fun _ _ => norm_nonneg _)
  have hCc0 : 0 ≤ ∫ t in (0 : ℝ)..1, ‖c t‖ ^ 2 :=
    intervalIntegral.integral_nonneg zero_le_one (fun _ _ => sq_nonneg _)
  have hLc : ∫ t in (0 : ℝ)..1, ‖c t‖ ≤ B1 := (integral_norm_le_of_sq hc1 hc2).trans (by rw [hB1]; linarith)
  have hLds : ∫ s in (0 : ℝ)..1, ‖ds s‖ ≤ ∫ s in (0 : ℝ)..1, ‖d s‖ :=
    intervalIntegral.integral_mono_on zero_le_one hds.norm hd.norm (fun s hs => by
      simp only [hdsdef, norm_mul]
      exact (mul_le_mul_of_nonneg_right (hcmp s hs) (norm_nonneg _)).trans (le_of_eq (one_mul _)))
  have hLds0 : 0 ≤ ∫ s in (0 : ℝ)..1, ‖ds s‖ :=
    intervalIntegral.integral_nonneg zero_le_one (fun _ _ => norm_nonneg _)
  have hLtc : ∫ t in (0 : ℝ)..1, ‖tc t‖ ≤ ∫ t in (0 : ℝ)..1, ‖c t‖ :=
    intervalIntegral.integral_mono_on zero_le_one htc1.norm hc1.norm (fun t ht => by
      simp only [htcdef, norm_mul]
      exact (mul_le_mul_of_nonneg_right (hcmp t ht) (norm_nonneg _)).trans (le_of_eq (one_mul _)))
  have hLtc0 : 0 ≤ ∫ t in (0 : ℝ)..1, ‖tc t‖ :=
    intervalIntegral.integral_nonneg zero_le_one (fun _ _ => norm_nonneg _)
  have hCtc : ∫ t in (0 : ℝ)..1, ‖tc t‖ ^ 2 ≤ ∫ t in (0 : ℝ)..1, ‖c t‖ ^ 2 :=
    intervalIntegral.integral_mono_on zero_le_one htc2 hc2 (fun t ht => by
      simp only [htcdef, norm_mul, mul_pow]
      have h1 : ‖(t : ℂ)‖ ^ 2 ≤ 1 := by
        have := hcmp t ht
        nlinarith [norm_nonneg (t : ℂ)]
      exact (mul_le_mul_of_nonneg_right h1 (sq_nonneg _)).trans (le_of_eq (one_mul _)))
  have hCtc0 : 0 ≤ ∫ t in (0 : ℝ)..1, ‖tc t‖ ^ 2 :=
    intervalIntegral.integral_nonneg zero_le_one (fun _ _ => sq_nonneg _)
  have hCH' : ∫ t in (0 : ℝ)..1, ‖H' t‖ ^ 2 ≤ ∫ t in (0 : ℝ)..1, ‖c t‖ ^ 2 :=
    intervalIntegral.integral_mono_on zero_le_one hH'2 hc2 hH'pt
  -- tail facts
  have hn0' : 2 * a + L + 2 ≤ ((⌈2 * a + L + 2⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have hFn : ∀ n ∈ F, 2 * a + L + 2 ≤ |(n : ℝ)| := by
    intro n hn
    have h1 : ((((⌈2 * a + L + 2⌉₊ : ℕ) : ℤ)) : ℝ) ≤ ((|n| : ℤ) : ℝ) := Int.cast_le.2 (hF n hn)
    rw [Int.cast_abs] at h1
    simp only [Int.cast_natCast] at h1
    linarith
  have hF2 : ∀ n ∈ F, 2 * a + 1 ≤ |(n : ℝ)| := fun n hn => by linarith [hFn n hn]
  -- the Tz bound, monotone in the integrals
  have hTzmono : ∀ (p q r : ℝ), 0 ≤ p → p ≤ Bd → 0 ≤ q → q ≤ B1 → 0 ≤ r → r ≤ Bc →
      1 ^ 2 * ((2 : ℕ) * (p * (p * r) + (4 * E2 * p * q * a) ^ 2 * Z)) ≤ TT := by
    intro p q r hp0 hp hq0 hq hr0 hr
    rw [hTT]
    have h1 : p * (p * r) ≤ Bd * (Bd * Bc) :=
      mul_le_mul hp (mul_le_mul hp hr hr0 hBd) (by positivity) hBd
    have h2 : 4 * E2 * p * q * a ≤ 4 * E2 * Bd * B1 * a := by
      have : p * q ≤ Bd * B1 := mul_le_mul hp hq hq0 hBd
      have h3 : 4 * E2 * (p * q) * a ≤ 4 * E2 * (Bd * B1) * a :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this (by positivity)) ha
      linarith [h3]
    have h4 : (4 * E2 * p * q * a) ^ 2 ≤ (4 * E2 * Bd * B1 * a) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h2 2
    have h5 := mul_le_mul_of_nonneg_right h4 hZ0
    have : (2 : ℝ) * (p * (p * r) + (4 * E2 * p * q * a) ^ 2 * Z) ≤
        2 * (Bd * (Bd * Bc) + (4 * E2 * Bd * B1 * a) ^ 2 * Z) := by linarith
    simpa using this
  have hT := Tz_xi_sum_le hcm hc1 hc2 hd a ha xi hxi σ hσ F hF2
  have hTa := Tz_xi_sum_le hcm hc1 hc2 hds a ha xi hxi σ hσ F hF2
  have hTb := Tz_xi_sum_le htcm htc1 htc2 hd a ha xi hxi σ hσ F hF2
  have hO := NlsGge.ThirdConsultation.KSPSQ1.osc_sq_finite hcmem a ha xi hxi σ hσ F
  have hOH := NlsGge.ThirdConsultation.KSPSQ1.osc_sq_finite hH'mem a ha xi hxi σ hσ F
  refine sum_sq_le_fin F _ ![fun n => ‖NlsGge.ThirdConsultation.KSPSWKB.endpointOsc ((σ : ℂ) * xi n) c‖,
      fun n => ‖NlsGge.ThirdConsultation.KSPSWKB.endpointOsc ((σ : ℂ) * xi n) H'‖,
      fun n => ‖NlsGge.ThirdConsultation.KSPS012Support5.Tz c d ((σ : ℂ) * xi n)‖,
      fun n => ‖NlsGge.ThirdConsultation.KSPS012Support5.Tz c ds ((σ : ℂ) * xi n)‖,
      fun n => ‖NlsGge.ThirdConsultation.KSPS012Support5.Tz tc d ((σ : ℂ) * xi n)‖,
      fun n => 1 / |(n : ℝ)|] Km hKm0 ?_
    ![2 * E2 * Bc, 2 * E2 * Bc, TT, TT, TT, Z] ?_ |>.trans (le_of_eq ?_)
  · intro n hn
    refine ⟨mul_nonneg (indexWeight_pos n).le (norm_nonneg _), ?_⟩
    have hp := diag_pointwise σ hσ hc1 hd u1 J a ha xi hxi g hgd C L hC hL happ n (by linarith [hFn n hn])
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero]
    refine hp.trans ?_
    set O1 := ‖NlsGge.ThirdConsultation.KSPSWKB.endpointOsc ((σ : ℂ) * xi n) c‖
    set O2 := ‖NlsGge.ThirdConsultation.KSPSWKB.endpointOsc ((σ : ℂ) * xi n) H'‖
    set T1 := ‖NlsGge.ThirdConsultation.KSPS012Support5.Tz c d ((σ : ℂ) * xi n)‖
    set T2 := ‖NlsGge.ThirdConsultation.KSPS012Support5.Tz c ds ((σ : ℂ) * xi n)‖
    set T3 := ‖NlsGge.ThirdConsultation.KSPS012Support5.Tz tc d ((σ : ℂ) * xi n)‖
    have hO1 : 0 ≤ O1 := norm_nonneg _
    have hO2 : 0 ≤ O2 := norm_nonneg _
    have hT1 : 0 ≤ T1 := norm_nonneg _
    have hT2 : 0 ≤ T2 := norm_nonneg _
    have hT3 : 0 ≤ T3 := norm_nonneg _
    have hi : 0 ≤ 1 / |(n : ℝ)| := by positivity
    have hEB := mul_nonneg hEA0 hBJ
    have haB := mul_nonneg ha hBJ
    have k1 : ‖u1‖ * (O1 + O2) ≤ Km * (O1 + O2) :=
      mul_le_mul_of_nonneg_right (by rw [hKm]; linarith) (by positivity)
    have k2 : 2 * EA * T1 ≤ Km * T1 := mul_le_mul_of_nonneg_right (by rw [hKm]; linarith) hT1
    have k3 : 4 * EA * (T2 + T3) ≤ Km * (T2 + T3) :=
      mul_le_mul_of_nonneg_right (by rw [hKm]; linarith) (by positivity)
    have hJ' : (4 * C + EA * ‖J‖ + a * ‖J‖) ≤ 4 * C + EA * BJ + a * BJ := by
      have := mul_le_mul_of_nonneg_left hJ hEA0
      have := mul_le_mul_of_nonneg_left hJ ha
      linarith
    have k4 : (4 * C + EA * ‖J‖ + a * ‖J‖) * (1 / |(n : ℝ)|) ≤ Km * (1 / |(n : ℝ)|) :=
      mul_le_mul_of_nonneg_right (hJ'.trans (by rw [hKm]; linarith)) hi
    have e : 2 * EA * (T1 + 2 * (T2 + T3)) = 2 * EA * T1 + 4 * EA * (T2 + T3) := by ring
    rw [e]
    calc _ ≤ Km * (O1 + O2) + Km * T1 + Km * (T2 + T3) + Km * (1 / |(n : ℝ)|) := by linarith
      _ = _ := by ring
  · intro j
    fin_cases j
    · simp only [Fin.zero_eta, Matrix.cons_val_zero]
      refine hO.trans ?_
      exact mul_le_mul_of_nonneg_left hBcc (by positivity)
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.head_cons]
      refine hOH.trans ?_
      exact mul_le_mul_of_nonneg_left (hCH'.trans hBcc) (by positivity)
    · simp only [Fin.reduceFinMk, Matrix.cons_val]
      exact hT.trans (hTzmono _ _ _ hLd0 hBdd hLc0 hLc hCc0 hBcc)
    · simp only [Fin.reduceFinMk, Matrix.cons_val]
      exact hTa.trans (hTzmono _ _ _ hLds0 (hLds.trans hBdd) hLc0 hLc hCc0 hBcc)
    · simp only [Fin.reduceFinMk, Matrix.cons_val]
      exact hTb.trans (hTzmono _ _ _ hLd0 hBdd hLtc0 (hLtc.trans hLc) hCtc0 (hCtc.trans hBcc))
    · simp only [Fin.reduceFinMk, Matrix.cons_val]
      exact inv_abs_sum_le F
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero]
    ring

end
end NlsGge.ThirdConsultation.KSPS017U1
