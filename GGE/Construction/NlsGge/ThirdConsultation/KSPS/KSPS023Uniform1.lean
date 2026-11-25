import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS023Support
import NlsGge.ThirdConsultation.KSPS.KSPSUniformU4
import NlsGge.ThirdConsultation.KSPS.KSPS025Host

                                                                                 
                                                                                                                    
                                                                                                                     
                                                                                            
                                                         
                                                                                                              
                                                                                                     
                                                                                                                    
                                                                 
                                                                                         
                                                                             
                                                                                         
                                                                                        
                                                                                                                
                                                                                                   
                                                                                                                 
                                                                                                             
                                                                                                                  
                                                      
set_option autoImplicit false
open MeasureTheory Filter
open scoped BigOperators Topology

namespace NlsGge.ThirdConsultation.KSPS023U
noncomputable section
open NlsGge.Pilot NlsGge.GK38
open NlsGge.ThirdConsultation.KSPS NlsGge.ThirdConsultation.KSPS021W NlsGge.ThirdConsultation.KSPS023W

def psiU (N : ℕ) (φ : SobolevC N) (n : ℤ) : ℝ :=
  (4 * KSPS016W.Sb φ + 4 * KSPS016W.Sb φ ^ 2) * tau N φ n + 4 * tau N φ n ^ 2 +
    indexWeight n ^ (N + 1) * ‖KSPSWKB.dirichletError N φ (mu φ) n‖ / 2

def boundU (N : ℕ) (φ : SobolevC N) (CT : ℝ) (n : ℤ) : ℝ :=
  psiU N φ n + Lsum φ * (4 * (‖physicalFourier (iteratedDerivative N φ.1) (-n)‖ +
      ‖physicalFourier (iteratedDerivative N φ.2) n‖) + 2 * psiU N φ n) +
    CT * 2 ^ (N + 2) * (1 / indexWeight n)

theorem sq_weight_le_U (N : ℕ) (hN : 1 ≤ N) (w s t : ℝ) (hw : 1 ≤ w) (hs : 0 ≤ s)
    (hst : w ^ N * s ≤ t) :
    w ^ (N + 1) * s ^ 2 ≤ t ^ 2 := by
  have hw0 : 0 ≤ w := by linarith
  have h0 : 0 ≤ w ^ N * s := mul_nonneg (pow_nonneg hw0 _) hs
  have h1 : w ^ (N + 1) ≤ w ^ (2 * N) := pow_le_pow_right₀ hw (by omega)
  have h2 : w ^ (N + 1) * s ^ 2 ≤ w ^ (2 * N) * s ^ 2 :=
    mul_le_mul_of_nonneg_right h1 (sq_nonneg s)
  have h3 : w ^ (2 * N) * s ^ 2 = (w ^ N * s) ^ 2 := by ring
  have h4 : (w ^ N * s) ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ h0 hst 2
  linarith

theorem tail023A_U (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N) (a : ℝ) (ha : 0 ≤ a)
    (hxi : ∀ n : ℤ, ‖mu φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n)
    (n : ℤ)
    (h1 : ((⌈a⌉₊ + ⌈KSPSVolterra.threshold N (sobolevNorm N φ)⌉₊ + 1 : ℕ) : ℤ) ≤ |n|)
    (h2 : ((⌈a⌉₊ + ⌈2 * KSPS016W.Sb φ⌉₊ + 1 : ℕ) : ℤ) ≤ |n|)
    (h3 : (1 : ℤ) ≤ |n|)
    (h4 : 2 * (a + Jsum φ) ≤ indexWeight n) :
    ∃ r2 : ℂ, indexWeight n ^ (N + 1) * ‖r2‖ ≤ psiU N φ n ∧
      mu φ n + KSPSRiccati.phasePolynomial φ (N + 1) (mu φ n)⁻¹ - (n : ℂ) * (Real.pi : ℂ) =
        (physicalFourier (toPotPair φ).1 (-n) + physicalFourier (toPotPair φ).2 n) / 2 + r2 := by
  obtain ⟨hst, hε⟩ := sine_tail N hN φ a ha hxi n h1 h2 h3 h4
  obtain ⟨hX1, hXT, hwX⟩ := KSPS015W.tail_facts a _ ha (mu φ) hxi n h1
  obtain ⟨-, hXS, -⟩ := KSPS015W.tail_facts a _ ha (mu φ) hxi n h2
  obtain ⟨hν1, hνa⟩ := KSPS016W.tail_nat a _ n h1
  have hX0 : 0 < ‖mu φ n‖ := by linarith
  have hthr : WKBThreshold N (sobolevNorm N φ) (mu φ n) := ⟨hX0, hXT⟩
  have hw1 := KSPS015W.one_le_w n
  have hw0 : 0 < indexWeight n := by linarith
  obtain ⟨hDinv, -, hα, hβ⟩ := KSPS016W.dinv_facts φ (mu φ n) (indexWeight n) hX1 hthr hw0 hwX
  have hS0 := KSPS016W.Sb_nonneg φ
  have hq : KSPS016W.Sb φ / (2 * ‖mu φ n‖) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hα4 := hα.trans hq
  have hβ4 := hβ.trans hq
  have hD : 1 - KSPSWKB.alpha φ (mu φ n) 0 * KSPSWKB.beta φ (mu φ n) 0 ≠ 0 := by
    intro h0
    have h6 : ‖KSPSWKB.alpha φ (mu φ n) 0 * KSPSWKB.beta φ (mu φ n) 0‖ = 1 := by
      rw [show KSPSWKB.alpha φ (mu φ n) 0 * KSPSWKB.beta φ (mu φ n) 0 = 1 by linear_combination -h0]
      simp
    rw [norm_mul] at h6
    linarith [mul_le_mul hα4 hβ4 (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 4)]
  have hn1R : (1 : ℝ) ≤ |(n : ℝ)| := hν1
  obtain ⟨-, -, hF1, hF2⟩ := KSPS016W.fourier_facts φ n hn1R
  -- (1) the exact sine identity at the Dirichlet root
  obtain ⟨-, hsn⟩ := shift (NlsGge.ThirdConsultation.KSPS.wkbPhase φ (mu φ n)) n
  set θ : ℂ := NlsGge.ThirdConsultation.KSPS.wkbPhase φ (mu φ n) with hθ
  set ε : ℂ := θ - (n : ℂ) * (Real.pi : ℂ) with hεdef
  have hsg1 : (-1 : ℂ) ^ (n + 1) = -(-1 : ℂ) ^ n := by
    rw [zpow_add_one₀ (by norm_num : (-1 : ℂ) ≠ 0)]; ring
  have hdE : KSPSWKB.dirichletError N φ (mu φ) n = 0 -
      ((1 - KSPSWKB.alpha φ (mu φ n) 0) * (1 - KSPSWKB.beta φ (mu φ n) 0) /
        (1 - KSPSWKB.alpha φ (mu φ n) 0 * KSPSWKB.beta φ (mu φ n) 0) *
          (2 * Complex.I * ((-1 : ℂ) ^ n * Complex.sin ε)) +
        Complex.I * (-(-1 : ℂ) ^ n) *
          (physicalFourier (toPotPair φ).1 (-n) + physicalFourier (toPotPair φ).2 n) +
        2 * (-(-1 : ℂ) ^ n) / (2 * Complex.I * mu φ n) ^ (N + 1) * integralRiccatiLeft φ (N + 1)) := by
    unfold KSPSWKB.dirichletError
    rw [dirichletNumerator_mu φ n, ← hθ, hsn, hsg1]
  have hsi := sine_identity _ (Complex.sin ε) _ _ _ _ _ (neg_one_zpow_mul_self n) hdE
  -- (2) eps versus sin eps
  have hsε : ‖Complex.sin ε‖ = ‖Complex.sin θ‖ := by
    rw [hsn, norm_mul, norm_neg_one_zpow, one_mul]
  have hεs := eps_le_two_sin ε hε
  have hss := norm_sin_sub_self_le ε (by linarith)
  have hQ1 := one_sub_Q_bound (indexWeight n) ‖mu φ n‖ (KSPS016W.Sb φ) (KSPSWKB.alpha φ (mu φ n) 0)
    (KSPSWKB.beta φ (mu φ n) 0) hw1 hwX hS0 hD hDinv hα hβ
  set C1 : ℝ := 4 * KSPS016W.Sb φ + 4 * KSPS016W.Sb φ ^ 2 with hC1
  have hC10 : 0 ≤ C1 := by positivity
  set r2 : ℂ := (ε - Complex.sin ε) +
    ((1 - (1 - KSPSWKB.alpha φ (mu φ n) 0) * (1 - KSPSWKB.beta φ (mu φ n) 0) /
        (1 - KSPSWKB.alpha φ (mu φ n) 0 * KSPSWKB.beta φ (mu φ n) 0)) * Complex.sin ε +
      Complex.I * (-1 : ℂ) ^ n * KSPSWKB.dirichletError N φ (mu φ) n / 2) with hr2def
  have hr2 : indexWeight n ^ (N + 1) * ‖r2‖ ≤ psiU N φ n := by
    have hb : ‖r2‖ ≤ 4 * ‖Complex.sin θ‖ ^ 2 + C1 / indexWeight n * ‖Complex.sin θ‖ +
        ‖KSPSWKB.dirichletError N φ (mu φ) n‖ / 2 := by
      have e1 : ‖ε - Complex.sin ε‖ ≤ 4 * ‖Complex.sin θ‖ ^ 2 := by
        rw [norm_sub_rev]
        refine hss.trans ?_
        rw [← hsε]
        calc ‖ε‖ ^ 2 ≤ (2 * ‖Complex.sin ε‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hεs 2
          _ = 4 * ‖Complex.sin ε‖ ^ 2 := by ring
      have e2 : ‖(1 - (1 - KSPSWKB.alpha φ (mu φ n) 0) * (1 - KSPSWKB.beta φ (mu φ n) 0) /
          (1 - KSPSWKB.alpha φ (mu φ n) 0 * KSPSWKB.beta φ (mu φ n) 0)) * Complex.sin ε‖ ≤
          C1 / indexWeight n * ‖Complex.sin θ‖ := by
        rw [norm_mul, hsε]
        exact mul_le_mul_of_nonneg_right hQ1 (norm_nonneg _)
      have e3 : ‖Complex.I * (-1 : ℂ) ^ n * KSPSWKB.dirichletError N φ (mu φ) n / 2‖ =
          ‖KSPSWKB.dirichletError N φ (mu φ) n‖ / 2 := by
        rw [norm_div, norm_mul, norm_mul, Complex.norm_I, norm_neg_one_zpow, Complex.norm_ofNat]
        ring
      calc ‖r2‖ ≤ ‖ε - Complex.sin ε‖ +
            (‖(1 - (1 - KSPSWKB.alpha φ (mu φ n) 0) * (1 - KSPSWKB.beta φ (mu φ n) 0) /
              (1 - KSPSWKB.alpha φ (mu φ n) 0 * KSPSWKB.beta φ (mu φ n) 0)) * Complex.sin ε‖ +
            ‖Complex.I * (-1 : ℂ) ^ n * KSPSWKB.dirichletError N φ (mu φ) n / 2‖) := by
            rw [hr2def]
            exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
        _ ≤ _ := by rw [e3]; linarith
    have hsq := sq_weight_le_U N hN (indexWeight n) ‖Complex.sin θ‖ (tau N φ n) hw1 (norm_nonneg _) hst
    have hlin : indexWeight n ^ (N + 1) * (C1 / indexWeight n * ‖Complex.sin θ‖) ≤ C1 * tau N φ n := by
      have e : indexWeight n ^ (N + 1) * (C1 / indexWeight n * ‖Complex.sin θ‖) =
          C1 * (indexWeight n ^ N * ‖Complex.sin θ‖) := by
        rw [pow_succ]; field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_left hst hC10
    have hwp : 0 ≤ indexWeight n ^ (N + 1) := pow_nonneg hw0.le _
    have h6 := mul_le_mul_of_nonneg_left hb hwp
    have e : indexWeight n ^ (N + 1) * (4 * ‖Complex.sin θ‖ ^ 2 + C1 / indexWeight n * ‖Complex.sin θ‖ +
        ‖KSPSWKB.dirichletError N φ (mu φ) n‖ / 2) =
        4 * (indexWeight n ^ (N + 1) * ‖Complex.sin θ‖ ^ 2) +
          indexWeight n ^ (N + 1) * (C1 / indexWeight n * ‖Complex.sin θ‖) +
          indexWeight n ^ (N + 1) * ‖KSPSWKB.dirichletError N φ (mu φ) n‖ / 2 := by ring
    rw [e] at h6
    unfold psiU
    rw [← hC1]
    linarith
  -- g(mu) - n pi = G/2 + r2
  have hg : mu φ n + KSPSRiccati.phasePolynomial φ (N + 1) (mu φ n)⁻¹ - (n : ℂ) * (Real.pi : ℂ) =
      (physicalFourier (toPotPair φ).1 (-n) + physicalFourier (toPotPair φ).2 n) / 2 + r2 := by
    rw [phase_poly_eq φ (mu φ n), ← hθ]
    have e : θ = ε + (n : ℂ) * (Real.pi : ℂ) := by rw [hεdef]; ring
    rw [e, hr2def]
    linear_combination hsi
  exact ⟨r2, hr2, hg⟩

theorem tail023_U (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N) (a : ℝ) (ha : 0 ≤ a)
    (hxi : ∀ n : ℤ, ‖mu φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n)
    (ζ : ℂ → ℂ) (CT : ℝ) (hCT : 0 ≤ CT) (n : ℤ)
    (h1 : ((⌈a⌉₊ + ⌈KSPSVolterra.threshold N (sobolevNorm N φ)⌉₊ + 1 : ℕ) : ℤ) ≤ |n|)
    (h2 : ((⌈a⌉₊ + ⌈2 * KSPS016W.Sb φ⌉₊ + 1 : ℕ) : ℤ) ≤ |n|)
    (h3 : (1 : ℤ) ≤ |n|)
    (h4 : 2 * (a + Jsum φ) ≤ indexWeight n)
    (hL : 2 * Lsum φ ≤ |(n : ℝ)| ^ 2)
    (hne : (Real.pi : ℂ) + (n : ℂ)⁻¹ * ζ (n : ℂ)⁻¹ ≠ 0)
    (heq : ζ (n : ℂ)⁻¹ + KSPSRiccati.phasePolynomial φ (N + 1)
      ((n : ℂ)⁻¹ / ((Real.pi : ℂ) + (n : ℂ)⁻¹ * ζ (n : ℂ)⁻¹)) = 0)
    (hsmall : ‖ζ (n : ℂ)⁻¹‖ ≤ 1)
    (htay : ‖ζ (n : ℂ)⁻¹ - ∑ k ∈ Finset.Icc 1 (N + 1),
        KSPSRiccati.spectralCoefficient φ k * ((n : ℂ)⁻¹) ^ k‖ ≤ CT * ‖(n : ℂ)⁻¹‖ ^ (N + 2)) :
    indexWeight n ^ (N + 1) *
      ‖mu φ n - spectralPolynomial φ n -
        (physicalFourier (toPotPair φ).1 (-n) + physicalFourier (toPotPair φ).2 n) / 2‖ ≤
      boundU N φ CT n := by
  obtain ⟨r2, hr2, hg⟩ := tail023A_U N hN φ a ha hxi n h1 h2 h3 h4
  obtain ⟨hν1, hνa⟩ := KSPS016W.tail_nat a _ n h1
  have hn1R : (1 : ℝ) ≤ |(n : ℝ)| := hν1
  have hw1 := KSPS015W.one_le_w n
  have hw0 : 0 < indexWeight n := by linarith
  obtain ⟨-, -, hF1, hF2⟩ := KSPS016W.fourier_facts φ n hn1R
  -- (3) the exact solution lam*
  have hnC : (n : ℂ) ≠ 0 := by
    intro h0
    have : (n : ℝ) = 0 := by exact_mod_cast h0
    rw [this, abs_zero] at hn1R
    linarith
  set ls : ℂ := (n : ℂ) * (Real.pi : ℂ) + ζ (n : ℂ)⁻¹ with hls
  have hgs := lamStar_eq φ ζ n hnC hne heq
  rw [← hls] at hgs
  -- norms
  have hnpi : ‖(n : ℂ) * (Real.pi : ℂ)‖ = Real.pi * |(n : ℝ)| := by
    rw [norm_mul, Complex.norm_intCast, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]; ring
  have hpi := Real.pi_gt_three
  have hμν : |(n : ℝ)| ≤ ‖mu φ n‖ := by
    have h7 := norm_sub_norm_le ((n : ℂ) * (Real.pi : ℂ)) (mu φ n)
    rw [norm_sub_rev, hnpi] at h7
    have h8 : a / indexWeight n ≤ a := div_le_self ha hw1
    have h9 := hxi n
    have h10 : 3 * |(n : ℝ)| ≤ Real.pi * |(n : ℝ)| := mul_le_mul_of_nonneg_right hpi.le (abs_nonneg _)
    linarith
  have hlsν : |(n : ℝ)| ≤ ‖ls‖ := by
    have h7 := norm_sub_norm_le ((n : ℂ) * (Real.pi : ℂ)) ls
    rw [norm_sub_rev, hnpi] at h7
    have h8 : ls - (n : ℂ) * (Real.pi : ℂ) = ζ (n : ℂ)⁻¹ := by rw [hls]; ring
    rw [h8] at h7
    have h10 : 3 * |(n : ℝ)| ≤ Real.pi * |(n : ℝ)| := mul_le_mul_of_nonneg_right hpi.le (abs_nonneg _)
    linarith
  have hν0 : 0 < |(n : ℝ)| := by linarith
  have hμ0 : mu φ n ≠ 0 := by intro h0; rw [h0, norm_zero] at hμν; linarith
  have hls0 : ls ≠ 0 := by intro h0; rw [h0, norm_zero] at hlsν; linarith
  have hμi : ‖(mu φ n)⁻¹‖ ≤ 1 := by
    rw [norm_inv]; exact inv_le_one_of_one_le₀ (by linarith)
  have hlsi : ‖ls⁻¹‖ ≤ 1 := by
    rw [norm_inv]; exact inv_le_one_of_one_le₀ (by linarith)
  have hinv : ‖(mu φ n)⁻¹ - ls⁻¹‖ ≤ ‖mu φ n - ls‖ / |(n : ℝ)| ^ 2 := by
    rw [inv_sub_inv hμ0 hls0, norm_div, norm_mul, norm_sub_rev]
    apply div_le_div_of_nonneg_left (norm_nonneg _) (pow_pos hν0 2)
    rw [pow_two]
    exact mul_le_mul hμν hlsν hν0.le (norm_nonneg _)
  have hlip := phasePoly_lip φ (N + 1) _ _ hμi hlsi
  have hΔp : ‖KSPSRiccati.phasePolynomial φ (N + 1) (mu φ n)⁻¹ -
      KSPSRiccati.phasePolynomial φ (N + 1) ls⁻¹‖ ≤ Lsum φ * ‖mu φ n - ls‖ / |(n : ℝ)| ^ 2 := by
    have hL0 : 0 ≤ Lsum φ := Finset.sum_nonneg (fun k _ => by positivity)
    refine hlip.trans ?_
    unfold Lsum
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hinv (Finset.sum_nonneg (fun k _ => by positivity))
  have hDeq : (mu φ n - ls) + (KSPSRiccati.phasePolynomial φ (N + 1) (mu φ n)⁻¹ -
      KSPSRiccati.phasePolynomial φ (N + 1) ls⁻¹) =
      (physicalFourier (toPotPair φ).1 (-n) + physicalFourier (toPotPair φ).2 n) / 2 + r2 := by
    rw [← hg]
    linear_combination (-1 : ℂ) * hgs
  -- Taylor error
  have hT0 : ‖ls - spectralPolynomial φ n‖ ≤ CT / |(n : ℝ)| ^ (N + 2) := by
    rw [spoly_eq, hls]
    have e : (n : ℂ) * (Real.pi : ℂ) + ζ (n : ℂ)⁻¹ - ((n : ℂ) * (Real.pi : ℂ) +
        ∑ k ∈ Finset.Icc 1 (N + 1), KSPSRiccati.spectralCoefficient φ k * ((n : ℂ)⁻¹) ^ k) =
        ζ (n : ℂ)⁻¹ - ∑ k ∈ Finset.Icc 1 (N + 1),
          KSPSRiccati.spectralCoefficient φ k * ((n : ℂ)⁻¹) ^ k := by ring
    rw [e]
    refine htay.trans (le_of_eq ?_)
    rw [norm_inv, Complex.norm_intCast, inv_pow]
    ring
  have hG : indexWeight n ^ N *
      ‖physicalFourier (toPotPair φ).1 (-n) + physicalFourier (toPotPair φ).2 n‖ ≤
      ‖physicalFourier (iteratedDerivative N φ.1) (-n)‖ +
        ‖physicalFourier (iteratedDerivative N φ.2) n‖ := by
    have := norm_add_le (physicalFourier (toPotPair φ).1 (-n)) (physicalFourier (toPotPair φ).2 n)
    have h8 := mul_le_mul_of_nonneg_left this (pow_nonneg hw0.le N)
    rw [mul_add] at h8
    linarith
  have hwν : indexWeight n ≤ 2 * |(n : ℝ)| := KSPS015W.w_le_two n hn1R
  have hL0 : 0 ≤ Lsum φ := Finset.sum_nonneg (fun k _ => by positivity)
  have hfin := final_pure N (indexWeight n) |(n : ℝ)| (Lsum φ) CT
    (‖physicalFourier (iteratedDerivative N φ.1) (-n)‖ + ‖physicalFourier (iteratedDerivative N φ.2) n‖)
    (psiU N φ n) (mu φ n - ls)
    (physicalFourier (toPotPair φ).1 (-n) + physicalFourier (toPotPair φ).2 n) r2
    (KSPSRiccati.phasePolynomial φ (N + 1) (mu φ n)⁻¹ - KSPSRiccati.phasePolynomial φ (N + 1) ls⁻¹)
    (ls - spectralPolynomial φ n)
    hw1 hn1R hwν hL0 hL hCT hDeq hΔp hT0 hG hr2
  have e : mu φ n - spectralPolynomial φ n -
      (physicalFourier (toPotPair φ).1 (-n) + physicalFourier (toPotPair φ).2 n) / 2 =
      r2 - (KSPSRiccati.phasePolynomial φ (N + 1) (mu φ n)⁻¹ -
        KSPSRiccati.phasePolynomial φ (N + 1) ls⁻¹) + (ls - spectralPolynomial φ n) := by
    linear_combination hDeq
  rw [e]
  unfold boundU
  exact hfin


/-! ### Finite-sum algebra -/

theorem sq4_le (a b c d : ℝ) : (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c),
    sq_nonneg (b - d), sq_nonneg (c - d)]

theorem sq3_le (a b c : ℝ) : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]

theorem sq_add2_le (a b : ℝ) : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  nlinarith [sq_nonneg (a - b)]

theorem sum_sq_le_sq_sum (F : Finset ℤ) (x : ℤ → ℝ) (h0 : ∀ n ∈ F, 0 ≤ x n) :
    ∑ n ∈ F, x n ^ 2 ≤ (∑ n ∈ F, x n) ^ 2 := by
  rw [sq (∑ n ∈ F, x n), Finset.sum_mul]
  refine Finset.sum_le_sum (fun n hn => ?_)
  rw [sq]
  exact mul_le_mul_of_nonneg_left (Finset.single_le_sum h0 hn) (h0 n hn)

theorem sum_part4 (F : Finset ℤ) (x τ E v : ℤ → ℝ) (α β γ δ T C S : ℝ)
    (hx0 : ∀ n ∈ F, 0 ≤ x n)
    (hx : ∀ n ∈ F, x n ≤ α * τ n + β * τ n ^ 2 + γ * E n + δ * v n)
    (hτ : ∑ n ∈ F, τ n ^ 2 ≤ T) (hE : ∑ n ∈ F, E n ^ 2 ≤ C) (hv : ∑ n ∈ F, v n ^ 2 ≤ S) :
    ∑ n ∈ F, x n ^ 2 ≤ 4 * (α ^ 2 * T + β ^ 2 * T ^ 2 + γ ^ 2 * C + δ ^ 2 * S) := by
  have hτ4 : ∑ n ∈ F, (τ n ^ 2) ^ 2 ≤ T ^ 2 :=
    (sum_sq_le_sq_sum F (fun n => τ n ^ 2) (fun n _ => sq_nonneg _)).trans
      (pow_le_pow_left₀ (Finset.sum_nonneg (fun n _ => sq_nonneg _)) hτ 2)
  have hkey : ∀ n ∈ F, x n ^ 2 ≤
      4 * α ^ 2 * τ n ^ 2 + 4 * β ^ 2 * (τ n ^ 2) ^ 2 + 4 * γ ^ 2 * E n ^ 2 + 4 * δ ^ 2 * v n ^ 2 := by
    intro n hn
    refine (pow_le_pow_left₀ (hx0 n hn) (hx n hn) 2).trans ?_
    refine (sq4_le _ _ _ _).trans (le_of_eq ?_)
    ring
  refine (Finset.sum_le_sum hkey).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  have a1 := mul_le_mul_of_nonneg_left hτ (by positivity : (0 : ℝ) ≤ 4 * α ^ 2)
  have a2 := mul_le_mul_of_nonneg_left hτ4 (by positivity : (0 : ℝ) ≤ 4 * β ^ 2)
  have a3 := mul_le_mul_of_nonneg_left hE (by positivity : (0 : ℝ) ≤ 4 * γ ^ 2)
  have a4 := mul_le_mul_of_nonneg_left hv (by positivity : (0 : ℝ) ≤ 4 * δ ^ 2)
  linarith

theorem le_abs_of_ceil (x : ℝ) (n : ℤ) (h : ((⌈x⌉₊ : ℕ) : ℤ) ≤ |n|) : x ≤ |(n : ℝ)| := by
  have h1 : (((⌈x⌉₊ : ℕ) : ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast h
  rw [Int.cast_abs] at h1
  push_cast at h1
  exact (Nat.le_ceil x).trans h1

theorem w_le_of_natAbs (n : ℤ) (M : ℕ) (hn : n.natAbs ≤ M) : indexWeight n ≤ 1 + M := by
  unfold indexWeight
  rw [Real.sqrt_le_left (by positivity)]
  have h1 : |(n : ℝ)| ≤ M := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs]; exact_mod_cast hn
  have h2 := sq_abs (n : ℝ)
  have h3 : |(n : ℝ)| ^ 2 ≤ (M : ℝ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  have h4 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have h5 : (n : ℝ) ^ 2 ≤ (M : ℝ) ^ 2 := by rw [← h2]; exact h3
  have h6 : (1 + (M : ℝ)) ^ 2 = 1 + 2 * (M : ℝ) + (M : ℝ) ^ 2 := by ring
  rw [h6]
  linarith

/-! ### The per-index bound on one uniform tail -/

theorem bound_alg (Sb S0 E f1 f2 I v L Ls CTc : ℝ) (hSb0 : 0 ≤ Sb) (hSb : Sb ≤ S0) (hE : 0 ≤ E)
    (hf1 : 0 ≤ f1) (hf2 : 0 ≤ f2) (hI0 : 0 ≤ I) (hI : I ≤ L) (hv : 0 ≤ v) (hLs0 : 0 ≤ Ls) (hLs : Ls ≤ L) :
    (4 * Sb + 4 * Sb ^ 2) * (E + f1 + f2 + 2 * I * v) + 4 * (E + f1 + f2 + 2 * I * v) ^ 2 + E / 2 +
        Ls * (4 * (f1 + f2) + 2 * ((4 * Sb + 4 * Sb ^ 2) * (E + f1 + f2 + 2 * I * v) +
          4 * (E + f1 + f2 + 2 * I * v) ^ 2 + E / 2)) + CTc * v ≤
      ((1 + 2 * L) * (4 * S0 + 4 * S0 ^ 2) + 4 * L) * (E + (f1 + f2) + 2 * L * v) +
        ((1 + 2 * L) * 4) * (E + (f1 + f2) + 2 * L * v) ^ 2 + ((1 + 2 * L) / 2) * E + CTc * v := by
  have hL : 0 ≤ L := hLs0.trans hLs
  have hS0 : 0 ≤ S0 := hSb0.trans hSb
  have ht0 : 0 ≤ E + f1 + f2 + 2 * I * v := by positivity
  have hIv : I * v ≤ L * v := mul_le_mul_of_nonneg_right hI hv
  have htt : E + f1 + f2 + 2 * I * v ≤ E + (f1 + f2) + 2 * L * v := by linarith
  have hft : f1 + f2 ≤ E + (f1 + f2) + 2 * L * v := by
    have : 0 ≤ L * v := mul_nonneg hL hv
    linarith
  have hC : 4 * Sb + 4 * Sb ^ 2 ≤ 4 * S0 + 4 * S0 ^ 2 := by
    have : Sb ^ 2 ≤ S0 ^ 2 := pow_le_pow_left₀ hSb0 hSb 2
    linarith
  have hC0 : 0 ≤ 4 * Sb + 4 * Sb ^ 2 := by positivity
  set t : ℝ := E + f1 + f2 + 2 * I * v with htdef
  set t' : ℝ := E + (f1 + f2) + 2 * L * v with ht'def
  have h1 : (4 * Sb + 4 * Sb ^ 2) * t ≤ (4 * S0 + 4 * S0 ^ 2) * t' := mul_le_mul hC htt ht0 (by positivity)
  have h2 : t ^ 2 ≤ t' ^ 2 := pow_le_pow_left₀ ht0 htt 2
  set Ψ : ℝ := (4 * S0 + 4 * S0 ^ 2) * t' + 4 * t' ^ 2 + E / 2 with hΨ
  have hp : (4 * Sb + 4 * Sb ^ 2) * t + 4 * t ^ 2 + E / 2 ≤ Ψ := by rw [hΨ]; linarith
  have hp0 : 0 ≤ (4 * Sb + 4 * Sb ^ 2) * t + 4 * t ^ 2 + E / 2 := by positivity
  have h3 : Ls * (4 * (f1 + f2) + 2 * ((4 * Sb + 4 * Sb ^ 2) * t + 4 * t ^ 2 + E / 2)) ≤
      L * (4 * t' + 2 * Ψ) := mul_le_mul hLs (by linarith) (by positivity) hL
  have e : ((1 + 2 * L) * (4 * S0 + 4 * S0 ^ 2) + 4 * L) * t' + ((1 + 2 * L) * 4) * t' ^ 2 +
      ((1 + 2 * L) / 2) * E + CTc * v = Ψ + L * (4 * t' + 2 * Ψ) + CTc * v := by rw [hΨ]; ring
  rw [e]
  linarith

theorem idx_conditions (N : ℕ) (φ : SobolevC N) (a L T0 S0 r0 : ℝ) (hr0 : 0 < r0)
    (hJ : Jsum φ ≤ L) (hLs : Lsum φ ≤ L)
    (hT0 : NlsGge.ThirdConsultation.KSPSVolterra.threshold N (sobolevNorm N φ) ≤ T0)
    (hS0 : KSPS016W.Sb φ ≤ S0) (n : ℤ)
    (hM : ((⌈a⌉₊ + ⌈T0⌉₊ + ⌈2 * S0⌉₊ + 1 + ⌈2 * (a + L)⌉₊ + ⌈2 * L⌉₊ + ⌈1 / r0⌉₊ : ℕ) : ℤ) ≤ |n|) :
    ((⌈a⌉₊ + ⌈NlsGge.ThirdConsultation.KSPSVolterra.threshold N (sobolevNorm N φ)⌉₊ + 1 : ℕ) : ℤ) ≤ |n| ∧
    ((⌈a⌉₊ + ⌈2 * KSPS016W.Sb φ⌉₊ + 1 : ℕ) : ℤ) ≤ |n| ∧ (1 : ℤ) ≤ |n| ∧
    2 * (a + Jsum φ) ≤ indexWeight n ∧ 2 * Lsum φ ≤ |(n : ℝ)| ^ 2 ∧ ‖((n : ℂ))⁻¹‖ ≤ r0 := by
  have hM' := hM
  push_cast at hM'
  have c1 : ⌈NlsGge.ThirdConsultation.KSPSVolterra.threshold N (sobolevNorm N φ)⌉₊ ≤ ⌈T0⌉₊ := Nat.ceil_mono hT0
  have c2 : ⌈2 * KSPS016W.Sb φ⌉₊ ≤ ⌈2 * S0⌉₊ := Nat.ceil_mono (by linarith)
  have g3 : (1 : ℤ) ≤ |n| := by omega
  have hab : (1 : ℝ) ≤ |(n : ℝ)| := by
    have : ((1 : ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast g3
    rw [Int.cast_abs] at this
    simpa using this
  have h4 := le_abs_of_ceil (2 * (a + L)) n (by omega)
  have h6 := le_abs_of_ceil (2 * L) n (by omega)
  have h7 := le_abs_of_ceil (1 / r0) n (by omega)
  refine ⟨by push_cast; omega, by push_cast; omega, g3, ?_, ?_, ?_⟩
  · have := KSPS021W.abs_le_w n
    linarith
  · have h8 : |(n : ℝ)| ≤ |(n : ℝ)| ^ 2 := by
      rw [sq]; exact le_mul_of_one_le_left (abs_nonneg _) hab
    linarith
  · rw [norm_inv, Complex.norm_intCast]
    rw [one_div] at h7
    exact inv_le_of_inv_le₀ hr0 h7

theorem per_index (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N) (a : ℝ) (ha : 0 ≤ a)
    (hxi : ∀ n : ℤ, ‖mu φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n)
    (L : ℝ) (hJ : Jsum φ ≤ L) (hLs : Lsum φ ≤ L)
    (hI : ‖integralRiccatiLeft φ (N + 1)‖ ≤ L) (T0 : ℝ)
    (hT0 : NlsGge.ThirdConsultation.KSPSVolterra.threshold N (sobolevNorm N φ) ≤ T0)
    (S0 : ℝ) (hS0 : KSPS016W.Sb φ ≤ S0) (r0 : ℝ) (hr0 : 0 < r0) (CT : ℝ) (hCT : 0 ≤ CT)
    (ζ : ℂ → ℂ) (hζ : ∀ y : ℂ, ‖y‖ ≤ r0 →
        (Real.pi : ℂ) + y * ζ y ≠ 0 ∧
        ζ y + NlsGge.ThirdConsultation.KSPSRiccati.phasePolynomial φ (N + 1)
          (y / ((Real.pi : ℂ) + y * ζ y)) = 0 ∧
        ‖ζ y‖ ≤ 1 ∧
        ‖ζ y - ∑ k ∈ Finset.Icc 1 (N + 1),
            NlsGge.ThirdConsultation.KSPSRiccati.spectralCoefficient φ k * y ^ k‖ ≤
          CT * ‖y‖ ^ (N + 2))
    (n : ℤ) (hM : ((⌈a⌉₊ + ⌈T0⌉₊ + ⌈2 * S0⌉₊ + 1 + ⌈2 * (a + L)⌉₊ + ⌈2 * L⌉₊ + ⌈1 / r0⌉₊ : ℕ) : ℤ) ≤ |n|) :
    indexWeight n ^ (N + 1) *
        ‖mu φ n - spectralPolynomial φ n -
          (physicalFourier (toPotPair φ).1 (-n) + physicalFourier (toPotPair φ).2 n) / 2‖ ≤
      ((1 + 2 * L) * (4 * S0 + 4 * S0 ^ 2) + 4 * L) *
          (indexWeight n ^ (N + 1) * ‖KSPSWKB.dirichletError N φ (mu φ) n‖ +
            (‖physicalFourier (iteratedDerivative N φ.1) (-n)‖ + ‖physicalFourier (iteratedDerivative N φ.2) n‖) +
            2 * L * (1 / indexWeight n)) +
        ((1 + 2 * L) * 4) *
          (indexWeight n ^ (N + 1) * ‖KSPSWKB.dirichletError N φ (mu φ) n‖ +
            (‖physicalFourier (iteratedDerivative N φ.1) (-n)‖ + ‖physicalFourier (iteratedDerivative N φ.2) n‖) +
            2 * L * (1 / indexWeight n)) ^ 2 +
        ((1 + 2 * L) / 2) * (indexWeight n ^ (N + 1) * ‖KSPSWKB.dirichletError N φ (mu φ) n‖) +
        (CT * 2 ^ (N + 2)) * (1 / indexWeight n) := by
  obtain ⟨g1, g2, g3, g4, hLn, hy⟩ := idx_conditions N φ a L T0 S0 r0 hr0 hJ hLs hT0 hS0 n hM
  obtain ⟨hne, heq, hsmall, htay⟩ := hζ _ hy
  have ht := tail023_U N hN φ a ha hxi ζ CT hCT n g1 g2 g3 g4 hLn hne heq hsmall htay
  refine ht.trans ?_
  have hw1 := KSPS015W.one_le_w n
  have hLs0 : 0 ≤ Lsum φ := Finset.sum_nonneg (fun k _ => by positivity)
  unfold boundU psiU tau
  exact bound_alg (KSPS016W.Sb φ) S0 _ _ _ _ _ L (Lsum φ) (CT * 2 ^ (N + 2)) (KSPS016W.Sb_nonneg φ) hS0
    (mul_nonneg (pow_nonneg (by linarith) _) (norm_nonneg _)) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hI
    (div_nonneg zero_le_one (by linarith)) hLs0 hLs

/-! ### The ball-uniform KSPS-023 estimate (core: proved uniform inputs as hypotheses) -/

theorem dirichlet_uniform_of (N : ℕ) (hN : 1 ≤ N) (B₀ : ℝ) (hB₀ : 0 ≤ B₀)
    (hloc0 : ∃ a : ℝ, 0 ≤ a ∧ ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      ∀ n : ℤ, ‖mu φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n)
    (hconst0 : ∃ L : ℝ, 0 ≤ L ∧ ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      Jsum φ ≤ L ∧ NlsGge.ThirdConsultation.KSPS023W.Lsum φ ≤ L ∧ ‖integralRiccatiLeft φ (N + 1)‖ ≤ L)
    (hgerm0 : ∃ r0 : ℝ, 0 < r0 ∧ ∃ CT : ℝ, 0 ≤ CT ∧
      ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ → ∃ ζ : ℂ → ℂ, ∀ y : ℂ, ‖y‖ ≤ r0 →
        (Real.pi : ℂ) + y * ζ y ≠ 0 ∧
        ζ y + NlsGge.ThirdConsultation.KSPSRiccati.phasePolynomial φ (N + 1)
          (y / ((Real.pi : ℂ) + y * ζ y)) = 0 ∧
        ‖ζ y‖ ≤ 1 ∧
        ‖ζ y - ∑ k ∈ Finset.Icc 1 (N + 1),
            NlsGge.ThirdConsultation.KSPSRiccati.spectralCoefficient φ k * y ^ k‖ ≤
          CT * ‖y‖ ^ (N + 2))
    (hsp0 : ∃ D : ℝ, 0 ≤ D ∧ ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ → ∀ n : ℤ,
      ‖spectralPolynomial φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ D)
    (T0 : ℝ) (hthr : ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      NlsGge.ThirdConsultation.KSPSVolterra.threshold N (sobolevNorm N φ) ≤ T0)
    (S0 : ℝ) (hSb : ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ → NlsGge.ThirdConsultation.KSPS016W.Sb φ ≤ S0)
    (P : ℝ) (hfour : ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ → ∀ F : Finset ℤ, (∀ n ∈ F, (1 : ℤ) ≤ |n|) →
      ∑ n ∈ F, ‖physicalFourier (iteratedDerivative N φ.1) (-n)‖ ^ 2 ≤ P ∧
      ∑ n ∈ F, ‖physicalFourier (iteratedDerivative N φ.2) n‖ ^ 2 ≤ P)
    (hD16 : ∃ (N0 : ℕ) (C : ℝ), ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      ∀ F : Finset ℤ, (∀ n ∈ F, (N0 : ℤ) ≤ |n|) →
        ∑ n ∈ F, (indexWeight n ^ (N + 1) *
          ‖NlsGge.ThirdConsultation.KSPSWKB.dirichletError N φ (mu φ) n‖) ^ 2 ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
        WeightedL2Error ((N + 1 : ℕ) : ℝ)
          (fun n => mu φ n - spectralPolynomial φ n -
            (physicalFourier (toPotPair φ).1 (-n) + physicalFourier (toPotPair φ).2 n) / 2) ∧
        ∀ F : Finset ℤ,
          (∑ n ∈ F,
            (indexWeight n ^ (N + 1) *
              ‖mu φ n - spectralPolynomial φ n -
                (physicalFourier (toPotPair φ).1 (-n) + physicalFourier (toPotPair φ).2 n) / 2‖) ^ 2) ≤ C ^ 2 := by
  obtain ⟨a, ha, hxa⟩ := hloc0
  obtain ⟨L, hL, hLb⟩ := hconst0
  obtain ⟨r0, hr0, CT, hCT, hgerm⟩ := hgerm0
  obtain ⟨D, hD, hspoly⟩ := hsp0
  obtain ⟨N0, CD, hDb⟩ := hD16
  set S : ℝ := ∑' n : ℤ, (1 / indexWeight n) ^ 2 with hSdef
  have hS0 : 0 ≤ S := tsum_nonneg (fun n => sq_nonneg _)
  set S1 : ℝ := max S0 0 with hS1
  have hS10 : 0 ≤ S1 := le_max_right _ _
  set M : ℕ := (⌈a⌉₊ + ⌈T0⌉₊ + ⌈2 * S1⌉₊ + 1 + ⌈2 * (a + L)⌉₊ + ⌈2 * L⌉₊ + ⌈1 / r0⌉₊) + N0 with hM
  set α : ℝ := (1 + 2 * L) * (4 * S1 + 4 * S1 ^ 2) + 4 * L with hα
  set β : ℝ := (1 + 2 * L) * 4 with hβ
  set γ : ℝ := (1 + 2 * L) / 2 with hγ
  set δ : ℝ := CT * 2 ^ (N + 2) with hδ
  set T : ℝ := 3 * (|CD| + 4 * |P| + 4 * L ^ 2 * S) with hT
  set K : ℝ := (1 + (M : ℝ)) ^ (N + 1) * (a + D + B₀) with hK
  set Ctot : ℝ := 4 * (α ^ 2 * T + β ^ 2 * T ^ 2 + γ ^ 2 * |CD| + δ ^ 2 * S) +
    ((Finset.Icc (-(M : ℤ)) M).card : ℝ) * K ^ 2 with hCtot
  have hCtot0 : 0 ≤ Ctot := by positivity
  refine ⟨Real.sqrt Ctot, Real.sqrt_nonneg _, fun φ hφ => ?_⟩
  obtain ⟨hJ, hLs, hI⟩ := hLb φ hφ
  obtain ⟨ζ, hζ⟩ := hgerm φ hφ
  have hSφ : NlsGge.ThirdConsultation.KSPS016W.Sb φ ≤ S1 := (hSb φ hφ).trans (le_max_left _ _)
  set x : ℤ → ℝ := fun n => indexWeight n ^ (N + 1) *
    ‖mu φ n - spectralPolynomial φ n -
      (physicalFourier (toPotPair φ).1 (-n) + physicalFourier (toPotPair φ).2 n) / 2‖ with hx
  have hx0 : ∀ n, 0 ≤ x n := fun n =>
    mul_nonneg (pow_nonneg (le_trans zero_le_one (KSPS015W.one_le_w n)) _) (norm_nonneg _)
  have hs0 : 0 ≤ sobolevNorm N φ := by unfold sobolevNorm; exact Real.sqrt_nonneg _
  -- low labels
  have hlow : ∀ n : ℤ, ¬ ((M : ℤ) ≤ |n|) → x n ≤ K := by
    intro n hn
    have hnM : n.natAbs ≤ M := by
      have h1 : |n| < (M : ℤ) := lt_of_not_ge hn
      have h2 := Int.natCast_natAbs n
      omega
    have hw1 := KSPS015W.one_le_w n
    have hw0 : 0 < indexWeight n := by linarith
    have hwM : indexWeight n ≤ 1 + M := w_le_of_natAbs n M hnM
    have hmu : ‖mu φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a := (hxa φ hφ n).trans (div_le_self ha hw1)
    have hW := NlsGge.ThirdConsultation.KSPSU4.weighted_fourier_le N φ {n}
    simp only [Finset.sum_singleton] at hW
    have hfa : ∀ y : ℝ, 0 ≤ y → (indexWeight n ^ N * y) ^ 2 ≤ sobolevNorm N φ ^ 2 → y ≤ B₀ := by
      intro y hy h
      have h1 : indexWeight n ^ N * y ≤ sobolevNorm N φ := (abs_le_of_sq_le_sq' h hs0).2
      have h2 : y ≤ indexWeight n ^ N * y := le_mul_of_one_le_left hy (one_le_pow₀ hw1)
      exact (h2.trans h1).trans hφ
    have ha1 : ‖physicalFourier (toPotPair φ).1 (-n)‖ ≤ B₀ :=
      hfa _ (norm_nonneg _) (le_trans (le_add_of_nonneg_right (sq_nonneg _)) hW)
    have ha2 : ‖physicalFourier (toPotPair φ).2 n‖ ≤ B₀ :=
      hfa _ (norm_nonneg _) (le_trans (le_add_of_nonneg_left (sq_nonneg _)) hW)
    have hG : ‖(physicalFourier (toPotPair φ).1 (-n) + physicalFourier (toPotPair φ).2 n) / 2‖ ≤ B₀ := by
      rw [norm_div, Complex.norm_ofNat]
      have := norm_add_le (physicalFourier (toPotPair φ).1 (-n)) (physicalFourier (toPotPair φ).2 n)
      linarith
    have hdiff : ‖mu φ n - spectralPolynomial φ n -
        (physicalFourier (toPotPair φ).1 (-n) + physicalFourier (toPotPair φ).2 n) / 2‖ ≤ a + D + B₀ := by
      have e : mu φ n - spectralPolynomial φ n -
          (physicalFourier (toPotPair φ).1 (-n) + physicalFourier (toPotPair φ).2 n) / 2 =
          (mu φ n - (n : ℂ) * (Real.pi : ℂ)) - (spectralPolynomial φ n - (n : ℂ) * (Real.pi : ℂ)) -
            (physicalFourier (toPotPair φ).1 (-n) + physicalFourier (toPotPair φ).2 n) / 2 := by ring
      rw [e]
      have h1 := norm_sub_le ((mu φ n - (n : ℂ) * (Real.pi : ℂ)) - (spectralPolynomial φ n - (n : ℂ) * (Real.pi : ℂ)))
        ((physicalFourier (toPotPair φ).1 (-n) + physicalFourier (toPotPair φ).2 n) / 2)
      have h2 := norm_sub_le (mu φ n - (n : ℂ) * (Real.pi : ℂ)) (spectralPolynomial φ n - (n : ℂ) * (Real.pi : ℂ))
      have h3 := hspoly φ hφ n
      linarith
    have hwp : indexWeight n ^ (N + 1) ≤ (1 + (M : ℝ)) ^ (N + 1) := pow_le_pow_left₀ hw0.le hwM _
    exact mul_le_mul hwp hdiff (norm_nonneg _) (by positivity)
  -- finite sums
  have hsum : ∀ F : Finset ℤ, ∑ n ∈ F, x n ^ 2 ≤ Ctot := by
    intro F
    rw [← Finset.sum_filter_add_sum_filter_not F (fun n : ℤ => (M : ℤ) ≤ |n|)]
    set Ft := F.filter (fun n : ℤ => (M : ℤ) ≤ |n|) with hFt
    set Fl := F.filter (fun n : ℤ => ¬ ((M : ℤ) ≤ |n|)) with hFl
    have hFtM : ∀ n ∈ Ft, (M : ℤ) ≤ |n| := fun n hn => (Finset.mem_filter.1 hn).2
    have hF1 : ∀ n ∈ Ft, (1 : ℤ) ≤ |n| := fun n hn => by have := hFtM n hn; omega
    have hE : ∑ n ∈ Ft, (indexWeight n ^ (N + 1) *
        ‖NlsGge.ThirdConsultation.KSPSWKB.dirichletError N φ (mu φ) n‖) ^ 2 ≤ |CD| :=
      (hDb φ hφ Ft (fun n hn => by have := hFtM n hn; omega)).trans (le_abs_self _)
    obtain ⟨hP1, hP2⟩ := hfour φ hφ Ft hF1
    have hv : ∑ n ∈ Ft, (1 / indexWeight n) ^ 2 ≤ S :=
      KSPS016W.sq_summable_inv_w.sum_le_tsum Ft (fun n _ => sq_nonneg _)
    have hτ : ∑ n ∈ Ft, (indexWeight n ^ (N + 1) *
          ‖NlsGge.ThirdConsultation.KSPSWKB.dirichletError N φ (mu φ) n‖ +
        (‖physicalFourier (iteratedDerivative N φ.1) (-n)‖ + ‖physicalFourier (iteratedDerivative N φ.2) n‖) +
        2 * L * (1 / indexWeight n)) ^ 2 ≤ T := by
      have hp : ∀ n ∈ Ft, (indexWeight n ^ (N + 1) *
            ‖NlsGge.ThirdConsultation.KSPSWKB.dirichletError N φ (mu φ) n‖ +
          (‖physicalFourier (iteratedDerivative N φ.1) (-n)‖ + ‖physicalFourier (iteratedDerivative N φ.2) n‖) +
          2 * L * (1 / indexWeight n)) ^ 2 ≤
          3 * (indexWeight n ^ (N + 1) * ‖NlsGge.ThirdConsultation.KSPSWKB.dirichletError N φ (mu φ) n‖) ^ 2 +
          6 * ‖physicalFourier (iteratedDerivative N φ.1) (-n)‖ ^ 2 +
          6 * ‖physicalFourier (iteratedDerivative N φ.2) n‖ ^ 2 +
          12 * L ^ 2 * (1 / indexWeight n) ^ 2 := by
        intro n _
        refine (sq3_le _ _ _).trans ?_
        have h1 := sq_add2_le ‖physicalFourier (iteratedDerivative N φ.1) (-n)‖
          ‖physicalFourier (iteratedDerivative N φ.2) n‖
        have h2 : (2 * L * (1 / indexWeight n)) ^ 2 = 4 * L ^ 2 * (1 / indexWeight n) ^ 2 := by ring
        linarith
      refine (Finset.sum_le_sum hp).trans ?_
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
      have hP0 : P ≤ |P| := le_abs_self _
      have := mul_le_mul_of_nonneg_left hv (by positivity : (0 : ℝ) ≤ 12 * L ^ 2)
      rw [hT]
      linarith
    have hTail : ∑ n ∈ Ft, x n ^ 2 ≤ 4 * (α ^ 2 * T + β ^ 2 * T ^ 2 + γ ^ 2 * |CD| + δ ^ 2 * S) :=
      sum_part4 Ft x
        (fun n => indexWeight n ^ (N + 1) * ‖NlsGge.ThirdConsultation.KSPSWKB.dirichletError N φ (mu φ) n‖ +
          (‖physicalFourier (iteratedDerivative N φ.1) (-n)‖ + ‖physicalFourier (iteratedDerivative N φ.2) n‖) +
          2 * L * (1 / indexWeight n))
        (fun n => indexWeight n ^ (N + 1) * ‖NlsGge.ThirdConsultation.KSPSWKB.dirichletError N φ (mu φ) n‖)
        (fun n => 1 / indexWeight n) α β γ δ T |CD| S (fun n _ => hx0 n)
        (fun n hn => per_index N hN φ a ha (hxa φ hφ) L hJ hLs hI T0 (hthr φ hφ) S1 hSφ r0 hr0 CT hCT ζ hζ n
          (by have := hFtM n hn; push_cast at this ⊢; omega))
        hτ hE hv
    have hLow : ∑ n ∈ Fl, x n ^ 2 ≤ ((Finset.Icc (-(M : ℤ)) M).card : ℝ) * K ^ 2 := by
      have hsub : Fl ⊆ Finset.Icc (-(M : ℤ)) M := by
        intro n hn
        have h := (Finset.mem_filter.1 hn).2
        rw [Finset.mem_Icc]
        constructor <;> cases abs_cases n <;> omega
      have hp : ∀ n ∈ Fl, x n ^ 2 ≤ K ^ 2 := fun n hn =>
        pow_le_pow_left₀ (hx0 n) (hlow n (Finset.mem_filter.1 hn).2) 2
      refine (Finset.sum_le_sum hp).trans ?_
      rw [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub) (sq_nonneg _)
    rw [hCtot]
    linarith
  refine ⟨?_, fun F => ?_⟩
  · rw [KSPS021W.wl2_iff]
    exact summable_of_sum_le (fun n => sq_nonneg _) hsum
  · rw [Real.sq_sqrt hCtot0]
    exact hsum F


/-! ### Pro r15 `midpoint_dirichlet_difference_uniform` from the two uniform expansions (pure assembly) -/

theorem midpoint_dirichlet_difference_of (N : ℕ) (B₀ : ℝ)
    (h25 : ∃ C : ℝ, 0 ≤ C ∧
      ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
        WeightedL2Error ((N + 1 : ℕ) : ℝ)
          (fun n => NlsGge.ThirdConsultation.KSPS.midpoint φ n - spectralPolynomial φ n) ∧
        ∀ F : Finset ℤ,
          (∑ n ∈ F,
            (indexWeight n ^ (N + 1) *
              ‖NlsGge.ThirdConsultation.KSPS.midpoint φ n - spectralPolynomial φ n‖)^2) ≤ C^2)
    (h23 : ∃ C : ℝ, 0 ≤ C ∧
      ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
        WeightedL2Error ((N + 1 : ℕ) : ℝ)
          (fun n => mu φ n - spectralPolynomial φ n -
            (physicalFourier (toPotPair φ).1 (-n) + physicalFourier (toPotPair φ).2 n) / 2) ∧
        ∀ F : Finset ℤ,
          (∑ n ∈ F,
            (indexWeight n ^ (N + 1) *
              ‖mu φ n - spectralPolynomial φ n -
                (physicalFourier (toPotPair φ).1 (-n) + physicalFourier (toPotPair φ).2 n) / 2‖) ^ 2) ≤ C ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
        WeightedL2Error ((N + 1 : ℕ) : ℝ)
          (fun n => NlsGge.ThirdConsultation.KSPS.midpoint φ n - mu φ n +
            (physicalFourier (toPotPair φ).1 (-n) +
             physicalFourier (toPotPair φ).2 n) / 2) ∧
        ∀ F : Finset ℤ,
          (∑ n ∈ F,
            (indexWeight n ^ (N + 1) *
              ‖NlsGge.ThirdConsultation.KSPS.midpoint φ n - mu φ n +
                (physicalFourier (toPotPair φ).1 (-n) +
                 physicalFourier (toPotPair φ).2 n) / 2‖)^2) ≤ C^2 := by
  obtain ⟨C1, -, h1⟩ := h25
  obtain ⟨C2, -, h2⟩ := h23
  have hC0 : 0 ≤ 2 * (C1 ^ 2 + C2 ^ 2) := by positivity
  refine ⟨Real.sqrt (2 * (C1 ^ 2 + C2 ^ 2)), Real.sqrt_nonneg _, fun φ hφ => ?_⟩
  obtain ⟨-, s1⟩ := h1 φ hφ
  obtain ⟨-, s2⟩ := h2 φ hφ
  have hpt : ∀ n : ℤ, (indexWeight n ^ (N + 1) *
      ‖NlsGge.ThirdConsultation.KSPS.midpoint φ n - mu φ n +
        (physicalFourier (toPotPair φ).1 (-n) + physicalFourier (toPotPair φ).2 n) / 2‖) ^ 2 ≤
      2 * ((indexWeight n ^ (N + 1) *
          ‖NlsGge.ThirdConsultation.KSPS.midpoint φ n - spectralPolynomial φ n‖) ^ 2 +
        (indexWeight n ^ (N + 1) *
          ‖mu φ n - spectralPolynomial φ n -
            (physicalFourier (toPotPair φ).1 (-n) + physicalFourier (toPotPair φ).2 n) / 2‖) ^ 2) := by
    intro n
    have hw0 : 0 ≤ indexWeight n ^ (N + 1) :=
      pow_nonneg (le_trans zero_le_one (KSPS015W.one_le_w n)) _
    have e : NlsGge.ThirdConsultation.KSPS.midpoint φ n - mu φ n +
        (physicalFourier (toPotPair φ).1 (-n) + physicalFourier (toPotPair φ).2 n) / 2 =
        (NlsGge.ThirdConsultation.KSPS.midpoint φ n - spectralPolynomial φ n) -
          (mu φ n - spectralPolynomial φ n -
            (physicalFourier (toPotPair φ).1 (-n) + physicalFourier (toPotPair φ).2 n) / 2) := by ring
    rw [e]
    have h := mul_le_mul_of_nonneg_left (norm_sub_le
      (NlsGge.ThirdConsultation.KSPS.midpoint φ n - spectralPolynomial φ n)
      (mu φ n - spectralPolynomial φ n -
        (physicalFourier (toPotPair φ).1 (-n) + physicalFourier (toPotPair φ).2 n) / 2)) hw0
    rw [mul_add] at h
    exact (pow_le_pow_left₀ (mul_nonneg hw0 (norm_nonneg _)) h 2).trans (sq_add2_le _ _)
  have hsum : ∀ F : Finset ℤ, ∑ n ∈ F, (indexWeight n ^ (N + 1) *
      ‖NlsGge.ThirdConsultation.KSPS.midpoint φ n - mu φ n +
        (physicalFourier (toPotPair φ).1 (-n) + physicalFourier (toPotPair φ).2 n) / 2‖) ^ 2 ≤
      2 * (C1 ^ 2 + C2 ^ 2) := by
    intro F
    refine (Finset.sum_le_sum (fun n _ => hpt n)).trans ?_
    rw [← Finset.mul_sum, Finset.sum_add_distrib]
    have := s1 F
    have := s2 F
    linarith
  refine ⟨?_, fun F => ?_⟩
  · rw [KSPS021W.wl2_iff]
    exact summable_of_sum_le (fun n => sq_nonneg _) hsum
  · rw [Real.sq_sqrt hC0]
    exact hsum F

end
end NlsGge.ThirdConsultation.KSPS023U
