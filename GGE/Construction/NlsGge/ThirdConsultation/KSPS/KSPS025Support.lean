import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS024Support
import NlsGge.ThirdConsultation.KSPS.KSPS025Host
import NlsGge.ThirdConsultation.KSPS.KSPS026Support2
import NlsGge.ThirdConsultation.KSPS.KSPS026Support3

                                                                                                                  
                                                                                                                        
                                                                                                                
                                                                                                                         
                                                                                                 
                                                                                                                     
                                                                                                                 
                                                                                                             
                                                                                                                            
                                                                                                                      
                                                                                        
                                                                                                                 
                                                                            
                                                                                                                     
                                                                                                                     
set_option autoImplicit false
open MeasureTheory Filter
open scoped BigOperators Topology

namespace NlsGge.ThirdConsultation.KSPS025W
noncomputable section
open NlsGge.Pilot NlsGge.GK38
open NlsGge.ThirdConsultation.KSPS NlsGge.ThirdConsultation.KSPS021W NlsGge.ThirdConsultation.KSPS023W
open NlsGge.ThirdConsultation.KSPS024W

/-! ### Pure lemmas -/

theorem quad_shift (α β r00 r01 r10 r11 u : ℂ)
    (hq : (-1 + α * β + r00 - β * r10) * (u + 1) ^ 2 +
        (1 + (1 - r00) * (1 - r11) - α * β - (α - r10) * (β - r01)) * (u + 1) +
        (-1 + α * β + r11 - α * r01) = 0) :
    (-1 + α * β + r00 - β * r10) * u ^ 2 +
        (r00 - r11 + (r00 * r11 - r01 * r10) - β * r10 + α * r01) * u +
        (r00 * r11 - r01 * r10) = 0 := by
  linear_combination hq

theorem quad_norm (q0 b c u : ℂ) (h : q0 * u ^ 2 + b * u + c = 0) :
    ‖q0‖ * ‖u‖ ^ 2 ≤ ‖b‖ * ‖u‖ + ‖c‖ := by
  have e : q0 * u ^ 2 = -(b * u + c) := by linear_combination h
  have h5 : ‖q0 * u ^ 2‖ = ‖q0‖ * ‖u‖ ^ 2 := by rw [norm_mul, norm_pow]
  rw [← h5, e, norm_neg]
  calc ‖b * u + c‖ ≤ ‖b * u‖ + ‖c‖ := norm_add_le _ _
    _ = ‖b‖ * ‖u‖ + ‖c‖ := by rw [norm_mul]

theorem root_real (x q B C R : ℝ) (hx : 0 ≤ x) (hR : 0 ≤ R) (hq : 1 / 2 ≤ q)
    (h : q * x ^ 2 ≤ B * x + C) (hB : B ≤ 2 * R) (hC : C ≤ 2 * (R * R)) : x ≤ 5 * R := by
  have h7 : 1 / 2 * x ^ 2 ≤ q * x ^ 2 := mul_le_mul_of_nonneg_right hq (sq_nonneg _)
  have h8 : B * x ≤ 2 * R * x := mul_le_mul_of_nonneg_right hB hx
  have h6 : 1 / 2 * x ^ 2 ≤ 2 * R * x + 2 * (R * R) := by linarith
  by_contra hcon
  push_neg at hcon
  nlinarith [mul_le_mul_of_nonneg_left hcon.le hx]

theorem quad_root_bound (α β r00 r01 r10 r11 u : ℂ) (R : ℝ)
    (hR : ‖r00‖ + ‖r01‖ + ‖r10‖ + ‖r11‖ ≤ R) (hR4 : R ≤ 1 / 4)
    (hα : ‖α‖ ≤ 1 / 4) (hβ : ‖β‖ ≤ 1 / 4)
    (hq : (-1 + α * β + r00 - β * r10) * (u + 1) ^ 2 +
        (1 + (1 - r00) * (1 - r11) - α * β - (α - r10) * (β - r01)) * (u + 1) +
        (-1 + α * β + r11 - α * r01) = 0) :
    ‖u‖ ≤ 5 * R := by
  have h := quad_norm _ _ _ u (quad_shift α β r00 r01 r10 r11 u hq)
  have h00 := norm_nonneg r00
  have h01 := norm_nonneg r01
  have h10 := norm_nonneg r10
  have h11 := norm_nonneg r11
  have hR0 : 0 ≤ R := by linarith
  have hab : ‖α * β‖ ≤ 1 / 16 := by
    rw [norm_mul]; nlinarith [norm_nonneg α, norm_nonneg β]
  have hbr : ‖β * r10‖ ≤ ‖r10‖ / 4 := by
    rw [norm_mul]; nlinarith [norm_nonneg β]
  have har : ‖α * r01‖ ≤ ‖r01‖ / 4 := by
    rw [norm_mul]; nlinarith [norm_nonneg α]
  have hp1 : ‖r00 * r11‖ ≤ R * R := by
    rw [norm_mul]; exact mul_le_mul (by linarith) (by linarith) h11 hR0
  have hp2 : ‖r01 * r10‖ ≤ R * R := by
    rw [norm_mul]; exact mul_le_mul (by linarith) (by linarith) h10 hR0
  have hcb : ‖r00 * r11 - r01 * r10‖ ≤ 2 * (R * R) :=
    (norm_sub_le _ _).trans (by linarith)
  have hRR : R * R ≤ R / 4 := by nlinarith
  have hbb : ‖r00 - r11 + (r00 * r11 - r01 * r10) - β * r10 + α * r01‖ ≤ 2 * R := by
    have t1 := norm_add_le (r00 - r11 + (r00 * r11 - r01 * r10) - β * r10) (α * r01)
    have t2 := norm_sub_le (r00 - r11 + (r00 * r11 - r01 * r10)) (β * r10)
    have t3 := norm_add_le (r00 - r11) (r00 * r11 - r01 * r10)
    have t4 := norm_sub_le r00 r11
    linarith
  have hq0b : 1 / 2 ≤ ‖-1 + α * β + r00 - β * r10‖ := by
    have h1 : ‖α * β + r00 - β * r10‖ ≤ 1 / 16 + ‖r00‖ + ‖r10‖ / 4 := by
      have := norm_sub_le (α * β + r00) (β * r10)
      have := norm_add_le (α * β) r00
      linarith
    have h3 : (-1 : ℂ) = (-1 + α * β + r00 - β * r10) - (α * β + r00 - β * r10) := by ring
    have h4 := norm_sub_le (-1 + α * β + r00 - β * r10) (α * β + r00 - β * r10)
    rw [← h3, norm_neg, norm_one] at h4
    linarith
  exact root_real _ _ _ _ R (norm_nonneg u) hR0 hq0b h hbb hcb

theorem exp_I_int_mul_pi (n : ℤ) :
    Complex.exp (Complex.I * ((n : ℂ) * (Real.pi : ℂ))) = (-1 : ℂ) ^ n := by
  rw [mul_comm, Complex.exp_mul_I, cos_int_mul_pi_c n, Complex.sin_int_mul_pi n]
  ring

theorem eta_eq (θ : ℂ) (n : ℤ) :
    (-1 : ℂ) ^ n * Complex.exp (Complex.I * θ) =
      Complex.exp (Complex.I * (θ - (n : ℂ) * (Real.pi : ℂ))) := by
  have e : Complex.I * θ = Complex.I * (θ - (n : ℂ) * (Real.pi : ℂ)) +
      Complex.I * ((n : ℂ) * (Real.pi : ℂ)) := by ring
  rw [e, Complex.exp_add, exp_I_int_mul_pi]
  have := neg_one_zpow_mul_self n
  linear_combination Complex.exp (Complex.I * (θ - (n : ℂ) * (Real.pi : ℂ))) * this

theorem eps_le_two_exp (ε : ℂ) (hε : ‖ε‖ ≤ 1 / 2) :
    ‖ε‖ ≤ 2 * ‖Complex.exp (Complex.I * ε) - 1‖ := by
  have hn : ‖Complex.I * ε‖ = ‖ε‖ := by rw [norm_mul, Complex.norm_I, one_mul]
  have h := Complex.norm_exp_sub_one_sub_id_le (x := Complex.I * ε) (by rw [hn]; linarith)
  rw [hn] at h
  have h2 : ‖Complex.I * ε‖ ≤ ‖Complex.exp (Complex.I * ε) - 1‖ +
      ‖Complex.exp (Complex.I * ε) - 1 - Complex.I * ε‖ := by
    have := norm_sub_le (Complex.exp (Complex.I * ε) - 1)
      (Complex.exp (Complex.I * ε) - 1 - Complex.I * ε)
    rwa [sub_sub_cancel] at this
  rw [hn] at h2
  have h3 : ‖ε‖ ^ 2 ≤ ‖ε‖ / 2 := by nlinarith [norm_nonneg ε]
  linarith

theorem wkbPhase_eq_poly {N : ℕ} (φ : SobolevC N) (μ : ℂ) :
    NlsGge.ThirdConsultation.KSPS.wkbPhase φ μ = μ + KSPSRiccati.phasePolynomial φ N μ⁻¹ := by
  rw [KSPS015W.wkbPhase_eq]
  unfold KSPSRiccati.phasePolynomial
  have hterm : ∀ k : ℕ, ((2 * Complex.I) ^ k)⁻¹ * integralRiccatiLeft φ k * μ⁻¹ ^ k =
      ((2 * Complex.I * μ) ^ k)⁻¹ * integralRiccatiLeft φ k := by
    intro k
    simp only [mul_pow, mul_inv, inv_pow]
    ring
  simp only [hterm]

/-- theta_N(x) - theta_N(y) = (x - y)(1 + O(1/n^2)) on the localization discs. -/
theorem gap_le_phase_diff {N : ℕ} (φ : SobolevC N) (x y : ℂ) (ν : ℝ) (hν : 0 < ν)
    (hx : ν ≤ ‖x‖) (hy : ν ≤ ‖y‖) (hν1 : 1 ≤ ν) (hL : 2 * Lp φ ≤ ν ^ 2) :
    ‖x - y‖ ≤ 2 * ‖NlsGge.ThirdConsultation.KSPS.wkbPhase φ x -
      NlsGge.ThirdConsultation.KSPS.wkbPhase φ y‖ := by
  have hx0 : x ≠ 0 := by intro h0; rw [h0, norm_zero] at hx; linarith
  have hy0 : y ≠ 0 := by intro h0; rw [h0, norm_zero] at hy; linarith
  have hxi : ‖x⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ (by linarith)
  have hyi : ‖y⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ (by linarith)
  have hinv : ‖x⁻¹ - y⁻¹‖ ≤ ‖x - y‖ / ν ^ 2 := by
    rw [inv_sub_inv hx0 hy0, norm_div, norm_mul, norm_sub_rev]
    apply div_le_div_of_nonneg_left (norm_nonneg _) (pow_pos hν 2)
    rw [pow_two]
    exact mul_le_mul hx hy hν.le (norm_nonneg _)
  have hlip := phasePoly_lip φ N _ _ hxi hyi
  have hLp0 := Lp_nonneg φ
  have hP : ‖KSPSRiccati.phasePolynomial φ N x⁻¹ - KSPSRiccati.phasePolynomial φ N y⁻¹‖ ≤
      ‖x - y‖ / 2 := by
    refine hlip.trans ?_
    have h1 : (∑ k ∈ Finset.Icc 1 N, (k : ℝ) * ‖integralRiccatiLeft φ k‖) = Lp φ := rfl
    rw [h1]
    calc Lp φ * ‖x⁻¹ - y⁻¹‖ ≤ Lp φ * (‖x - y‖ / ν ^ 2) := mul_le_mul_of_nonneg_left hinv hLp0
      _ ≤ ‖x - y‖ / 2 := by
          rw [mul_div_assoc', div_le_div_iff₀ (pow_pos hν 2) (by norm_num)]
          nlinarith [norm_nonneg (x - y)]
  rw [wkbPhase_eq_poly, wkbPhase_eq_poly]
  have e : x + KSPSRiccati.phasePolynomial φ N x⁻¹ - (y + KSPSRiccati.phasePolynomial φ N y⁻¹) =
      (x - y) + (KSPSRiccati.phasePolynomial φ N x⁻¹ - KSPSRiccati.phasePolynomial φ N y⁻¹) := by ring
  rw [e]
  have h2 := norm_sub_le (x - y + (KSPSRiccati.phasePolynomial φ N x⁻¹ -
    KSPSRiccati.phasePolynomial φ N y⁻¹))
    (KSPSRiccati.phasePolynomial φ N x⁻¹ - KSPSRiccati.phasePolynomial φ N y⁻¹)
  rw [add_sub_cancel_right] at h2
  linarith

/-! ### Bounding sequences (literal abbreviations) -/

def Eent (N : ℕ) (φ : SobolevC N) (upper : Bool) (n : ℤ) : ℝ :=
  ‖KSPSWKB.endpointEntryError N φ upper 0 0 n‖ + ‖KSPSWKB.endpointEntryError N φ upper 0 1 n‖ +
    ‖KSPSWKB.endpointEntryError N φ upper 1 0 n‖ + ‖KSPSWKB.endpointEntryError N φ upper 1 1 n‖

def tP (N : ℕ) (φ : SobolevC N) (n : ℤ) : ℝ :=
  indexWeight n ^ (N + 1) * (Eent N φ true n + Eent N φ false n) +
    ‖physicalFourier (iteratedDerivative N φ.1) (-n)‖ +
    ‖physicalFourier (iteratedDerivative N φ.2) n‖ +
    2 * ‖integralRiccatiLeft φ (N + 1)‖ * (1 / indexWeight n)

theorem Eent_nonneg (N : ℕ) (φ : SobolevC N) (upper : Bool) (n : ℤ) : 0 ≤ Eent N φ upper n := by
  unfold Eent; positivity

/-! ### One endpoint -/

theorem side_bound (N : ℕ) (φ : SobolevC N) (a : ℝ) (ha : 0 ≤ a) (upper : Bool) (xi : ℤ → ℂ)
    (hxe : ∀ n, (if upper then periodicPlus φ n else periodicMinus φ n) = xi n)
    (hxi : ∀ n : ℤ, ‖xi n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n) (n : ℤ)
    (h1 : ((⌈a⌉₊ + ⌈KSPSVolterra.threshold N (sobolevNorm N φ)⌉₊ + 1 : ℕ) : ℤ) ≤ |n|)
    (h2 : ((⌈a⌉₊ + ⌈2 * KSPS016W.Sb φ⌉₊ + 1 : ℕ) : ℤ) ≤ |n|)
    (h4 : 2 * (a + Jsum φ) ≤ indexWeight n)
    (h5 : tP N φ n ≤ 1 / 4) (hz : xi n ≠ 0)
    (hq : KSPSWKB.endpointQuadraticABC N φ n ⟨xi n, hz⟩ 0 *
          ((-1 : ℂ) ^ n * Complex.exp (Complex.I * NlsGge.ThirdConsultation.KSPS.wkbPhase φ (xi n))) ^ 2 +
        KSPSWKB.endpointQuadraticABC N φ n ⟨xi n, hz⟩ 1 *
          ((-1 : ℂ) ^ n * Complex.exp (Complex.I * NlsGge.ThirdConsultation.KSPS.wkbPhase φ (xi n))) +
        KSPSWKB.endpointQuadraticABC N φ n ⟨xi n, hz⟩ 2 = 0) :
    indexWeight n ^ N * ‖NlsGge.ThirdConsultation.KSPS.wkbPhase φ (xi n) - (n : ℂ) * (Real.pi : ℂ)‖ ≤
      10 * tP N φ n := by
  obtain ⟨hX1, hXT, hwX⟩ := KSPS015W.tail_facts a _ ha xi hxi n h1
  obtain ⟨-, hXS, -⟩ := KSPS015W.tail_facts a _ ha xi hxi n h2
  have hX0 : 0 < ‖xi n‖ := by linarith
  have hthr : WKBThreshold N (sobolevNorm N φ) (xi n) := ⟨hX0, hXT⟩
  have hw1 := KSPS015W.one_le_w n
  have hw0 : 0 < indexWeight n := by linarith
  obtain ⟨-, -, hα, hβ⟩ := KSPS016W.dinv_facts φ (xi n) (indexWeight n) hX1 hthr hw0 hwX
  have hS0 := KSPS016W.Sb_nonneg φ
  have hq4 : KSPS016W.Sb φ / (2 * ‖xi n‖) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hn1R : (1 : ℝ) ≤ |(n : ℝ)| := (KSPS016W.tail_nat a _ n h1).1
  obtain ⟨-, -, hF1, hF2⟩ := KSPS016W.fourier_facts φ n hn1R
  set r := KSPSWKB.scaledEndpointCorrection N φ n ⟨xi n, hz⟩ with hrdef
  -- the entries r_ij versus the leading matrix
  have hE : ∀ i j : Fin 2, KSPSWKB.endpointEntryError N φ upper i j n =
      r i j - (!![integralRiccatiLeft φ (N + 1) / (2 * Complex.I * xi n) ^ (N + 1),
            Complex.I * physicalFourier (toPotPair φ).1 (-n);
            -Complex.I * physicalFourier (toPotPair φ).2 n,
            -integralRiccatiLeft φ (N + 1) / (2 * Complex.I * xi n) ^ (N + 1)] :
              Matrix (Fin 2) (Fin 2) ℂ) i j :=
    fun i j => NlsGge.ThirdConsultation.KSPS026W.entryError_eq φ upper xi hxe i j n hz
  have hY : ‖integralRiccatiLeft φ (N + 1) / (2 * Complex.I * xi n) ^ (N + 1)‖ =
      ‖integralRiccatiLeft φ (N + 1)‖ / (2 * ‖xi n‖) ^ (N + 1) := by
    rw [norm_div, norm_pow, norm_mul, norm_mul, Complex.norm_I, Complex.norm_ofNat, mul_one]
  have hent : ∀ (i j : Fin 2) (lead : ℂ),
      KSPSWKB.endpointEntryError N φ upper i j n = r i j - lead →
      ‖r i j‖ ≤ ‖lead‖ + ‖KSPSWKB.endpointEntryError N φ upper i j n‖ := by
    intro i j lead h
    have e : r i j = lead + KSPSWKB.endpointEntryError N φ upper i j n := by rw [h]; ring
    rw [e]; exact norm_add_le _ _
  have e00 := hent 0 0 (integralRiccatiLeft φ (N + 1) / (2 * Complex.I * xi n) ^ (N + 1)) (hE 0 0)
  have e01 := hent 0 1 (Complex.I * physicalFourier (toPotPair φ).1 (-n)) (hE 0 1)
  have e10 := hent 1 0 (-Complex.I * physicalFourier (toPotPair φ).2 n) (hE 1 0)
  have e11 := hent 1 1 (-integralRiccatiLeft φ (N + 1) / (2 * Complex.I * xi n) ^ (N + 1)) (hE 1 1)
  rw [hY] at e00
  rw [neg_div, norm_neg, hY] at e11
  rw [norm_mul, Complex.norm_I, one_mul] at e01
  rw [norm_mul, norm_neg, Complex.norm_I, one_mul] at e10
  set R : ℝ := ‖r 0 0‖ + ‖r 0 1‖ + ‖r 1 0‖ + ‖r 1 1‖ with hRdef
  have hEu : Eent N φ upper n ≤ Eent N φ true n + Eent N φ false n := by
    have := Eent_nonneg N φ true n
    have := Eent_nonneg N φ false n
    cases upper <;> linarith
  have hRs : R ≤ Eent N φ upper n +
      (‖physicalFourier (toPotPair φ).1 (-n)‖ + ‖physicalFourier (toPotPair φ).2 n‖) +
      2 * ‖integralRiccatiLeft φ (N + 1)‖ / (2 * ‖xi n‖) ^ (N + 1) := by
    have h2c : 2 * ‖integralRiccatiLeft φ (N + 1)‖ / (2 * ‖xi n‖) ^ (N + 1) =
        ‖integralRiccatiLeft φ (N + 1)‖ / (2 * ‖xi n‖) ^ (N + 1) +
          ‖integralRiccatiLeft φ (N + 1)‖ / (2 * ‖xi n‖) ^ (N + 1) := by ring
    rw [hRdef, h2c]; unfold Eent; linarith
  have hRw : indexWeight n ^ N * R ≤ tP N φ n := by
    have h8 := tau_pure N (indexWeight n) ‖xi n‖ (Eent N φ upper n) _ _ _ _ ‖integralRiccatiLeft φ (N + 1)‖ R
      hw1 hwX (Eent_nonneg N φ upper n) (norm_nonneg _) hF1 hF2 hRs
    have h9 : indexWeight n ^ (N + 1) * Eent N φ upper n ≤
        indexWeight n ^ (N + 1) * (Eent N φ true n + Eent N φ false n) :=
      mul_le_mul_of_nonneg_left hEu (pow_nonneg hw0.le _)
    unfold tP
    linarith
  have hR0 : 0 ≤ R := by rw [hRdef]; positivity
  have hwN : 1 ≤ indexWeight n ^ N := one_le_pow₀ hw1
  have hR4 : R ≤ 1 / 4 := by
    have := le_mul_of_one_le_left hR0 hwN
    linarith
  -- the root bound for u = eta - 1
  set θ : ℂ := NlsGge.ThirdConsultation.KSPS.wkbPhase φ (xi n) with hθ
  set ε : ℂ := θ - (n : ℂ) * (Real.pi : ℂ) with hεdef
  have heta : (-1 : ℂ) ^ n * Complex.exp (Complex.I * θ) = Complex.exp (Complex.I * ε) := eta_eq θ n
  rw [heta] at hq
  have hq' : (-1 + KSPSWKB.alpha φ (xi n) 0 * KSPSWKB.beta φ (xi n) 0 + r 0 0 -
        KSPSWKB.beta φ (xi n) 0 * r 1 0) * ((Complex.exp (Complex.I * ε) - 1) + 1) ^ 2 +
      (1 + (1 - r 0 0) * (1 - r 1 1) - KSPSWKB.alpha φ (xi n) 0 * KSPSWKB.beta φ (xi n) 0 -
        (KSPSWKB.alpha φ (xi n) 0 - r 1 0) * (KSPSWKB.beta φ (xi n) 0 - r 0 1)) *
          ((Complex.exp (Complex.I * ε) - 1) + 1) +
      (-1 + KSPSWKB.alpha φ (xi n) 0 * KSPSWKB.beta φ (xi n) 0 + r 1 1 -
        KSPSWKB.alpha φ (xi n) 0 * r 0 1) = 0 := by
    rw [sub_add_cancel]
    exact hq
  have hu := quad_root_bound _ _ _ _ _ _ _ R le_rfl hR4 (hα.trans hq4) (hβ.trans hq4) hq'
  -- eps is small
  have hε : ‖ε‖ ≤ 1 / 2 := by
    have := phase_small φ (xi n) n (indexWeight n) a hw0 hX1 hwX (hxi n)
    have h7 : (a + Jsum φ) / indexWeight n ≤ 1 / 2 := by
      rw [div_le_iff₀ hw0]
      linarith
    unfold Jsum at h7
    rw [hεdef, hθ]
    linarith
  have hεu := eps_le_two_exp ε hε
  have h10 : ‖ε‖ ≤ 10 * R := by linarith
  calc indexWeight n ^ N * ‖ε‖ ≤ indexWeight n ^ N * (10 * R) :=
        mul_le_mul_of_nonneg_left h10 (pow_nonneg hw0.le N)
    _ = 10 * (indexWeight n ^ N * R) := by ring
    _ ≤ 10 * tP N φ n := by linarith

/-! ### The tail estimate at one index -/

theorem gap_bound (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N) (a : ℝ) (ha : 0 ≤ a)
    (hxp : ∀ n : ℤ, ‖periodicPlus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n)
    (hxm : ∀ n : ℤ, ‖periodicMinus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n)
    (hplus hminus : ℤ → ℂ) (n : ℤ)
    (h1 : ((⌈a⌉₊ + ⌈KSPSVolterra.threshold N (sobolevNorm N φ)⌉₊ + 1 : ℕ) : ℤ) ≤ |n|)
    (h2 : ((⌈a⌉₊ + ⌈2 * KSPS016W.Sb φ⌉₊ + 1 : ℕ) : ℤ) ≤ |n|)
    (h4 : 2 * (a + Jsum φ) ≤ indexWeight n)
    (h5 : tP N φ n ≤ 1 / 4)
    (hL : 2 * Lp φ ≤ |(n : ℝ)| ^ 2)
    (hqf : KSPSWKB.endpointQuadraticFormula N φ n hplus hminus) :
    indexWeight n ^ N * ‖periodicPlus φ n - periodicMinus φ n‖ ≤ 40 * tP N φ n := by
  obtain ⟨hp, hm, hqp, hqm⟩ := hqf
  obtain ⟨-, hqp2, -⟩ := hqp
  obtain ⟨-, hqm2, -⟩ := hqm
  have hsp := side_bound N φ a ha true (periodicPlus φ) (fun _ => rfl) hxp n h1 h2 h4 h5 hp hqp2
  have hsm := side_bound N φ a ha false (periodicMinus φ) (fun _ => rfl) hxm n h1 h2 h4 h5 hm hqm2
  obtain ⟨hn1R, hνa⟩ := KSPS016W.tail_nat a _ n h1
  have hw1 := KSPS015W.one_le_w n
  have hw0 : 0 < indexWeight n := by linarith
  have hν0 : 0 < |(n : ℝ)| := by linarith
  have hnpi : ‖(n : ℂ) * (Real.pi : ℂ)‖ = Real.pi * |(n : ℝ)| := by
    rw [norm_mul, Complex.norm_intCast, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]; ring
  have hpi := Real.pi_gt_three
  have hloc : ∀ z : ℂ, ‖z - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n → |(n : ℝ)| ≤ ‖z‖ := by
    intro z hz
    have h7 := norm_sub_norm_le ((n : ℂ) * (Real.pi : ℂ)) z
    rw [norm_sub_rev, hnpi] at h7
    have h8 : a / indexWeight n ≤ a := div_le_self ha hw1
    have h10 : 3 * |(n : ℝ)| ≤ Real.pi * |(n : ℝ)| := mul_le_mul_of_nonneg_right hpi.le (abs_nonneg _)
    linarith
  have hγ := gap_le_phase_diff φ (periodicPlus φ n) (periodicMinus φ n) |(n : ℝ)| hν0
    (hloc _ (hxp n)) (hloc _ (hxm n)) hn1R hL
  have hθ : ‖NlsGge.ThirdConsultation.KSPS.wkbPhase φ (periodicPlus φ n) -
      NlsGge.ThirdConsultation.KSPS.wkbPhase φ (periodicMinus φ n)‖ ≤
      ‖NlsGge.ThirdConsultation.KSPS.wkbPhase φ (periodicPlus φ n) - (n : ℂ) * (Real.pi : ℂ)‖ +
      ‖NlsGge.ThirdConsultation.KSPS.wkbPhase φ (periodicMinus φ n) - (n : ℂ) * (Real.pi : ℂ)‖ := by
    have e : NlsGge.ThirdConsultation.KSPS.wkbPhase φ (periodicPlus φ n) -
        NlsGge.ThirdConsultation.KSPS.wkbPhase φ (periodicMinus φ n) =
        (NlsGge.ThirdConsultation.KSPS.wkbPhase φ (periodicPlus φ n) - (n : ℂ) * (Real.pi : ℂ)) -
        (NlsGge.ThirdConsultation.KSPS.wkbPhase φ (periodicMinus φ n) - (n : ℂ) * (Real.pi : ℂ)) := by ring
    rw [e]; exact norm_sub_le _ _
  have hwN0 : 0 ≤ indexWeight n ^ N := pow_nonneg hw0.le N
  have h6 := mul_le_mul_of_nonneg_left (hγ.trans (mul_le_mul_of_nonneg_left hθ (by norm_num))) hwN0
  nlinarith

theorem tail025 (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N) (a : ℝ) (ha : 0 ≤ a)
    (hxp : ∀ n : ℤ, ‖periodicPlus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n)
    (hxm : ∀ n : ℤ, ‖periodicMinus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n)
    (hplus hminus : ℤ → ℂ) (n : ℤ) (A : ℂ) (CA : ℝ) (hA : ‖A‖ ≤ CA)
    (hid : criticalEigenvalue φ n - (periodicPlus φ n + periodicMinus φ n) / 2 =
      (periodicPlus φ n - periodicMinus φ n) ^ 2 * A)
    (h1 : ((⌈a⌉₊ + ⌈KSPSVolterra.threshold N (sobolevNorm N φ)⌉₊ + 1 : ℕ) : ℤ) ≤ |n|)
    (h2 : ((⌈a⌉₊ + ⌈2 * KSPS016W.Sb φ⌉₊ + 1 : ℕ) : ℤ) ≤ |n|)
    (h4 : 2 * (a + Jsum φ) ≤ indexWeight n)
    (h5 : tP N φ n ≤ 1 / 4)
    (hL : 2 * Lp φ ≤ |(n : ℝ)| ^ 2)
    (hqf : KSPSWKB.endpointQuadraticFormula N φ n hplus hminus) :
    indexWeight n ^ (N + 1) * ‖NlsGge.ThirdConsultation.KSPS.midpoint φ n - criticalEigenvalue φ n‖ ≤
      1600 * CA * tP N φ n := by
  have hg := gap_bound N hN φ a ha hxp hxm hplus hminus n h1 h2 h4 h5 hL hqf
  have hw1 := KSPS015W.one_le_w n
  have hw0 : 0 < indexWeight n := by linarith
  have hwN0 : 0 ≤ indexWeight n ^ N := pow_nonneg hw0.le N
  set g : ℝ := indexWeight n ^ N * ‖periodicPlus φ n - periodicMinus φ n‖ with hgdef
  have hg0 : 0 ≤ g := mul_nonneg hwN0 (norm_nonneg _)
  have htP0 : 0 ≤ tP N φ n := by linarith
  have hmid : NlsGge.ThirdConsultation.KSPS.midpoint φ n - criticalEigenvalue φ n = -((periodicPlus φ n - periodicMinus φ n) ^ 2 * A) := by
    unfold NlsGge.ThirdConsultation.KSPS.midpoint
    linear_combination (-1 : ℂ) * hid
  rw [hmid, norm_neg, norm_mul, norm_pow]
  have hA0 : 0 ≤ ‖A‖ := norm_nonneg A
  have hw2 : indexWeight n ^ (N + 1) ≤ indexWeight n ^ (2 * N) := pow_le_pow_right₀ hw1 (by omega)
  have hk : indexWeight n ^ (N + 1) * ‖periodicPlus φ n - periodicMinus φ n‖ ^ 2 ≤ g ^ 2 := by
    have e : g ^ 2 = indexWeight n ^ (2 * N) * ‖periodicPlus φ n - periodicMinus φ n‖ ^ 2 := by
      rw [hgdef]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_right hw2 (sq_nonneg _)
  have hg2 : g ^ 2 ≤ 1600 * tP N φ n := by
    have h7 : g ^ 2 ≤ (40 * tP N φ n) ^ 2 := pow_le_pow_left₀ hg0 hg 2
    nlinarith
  calc indexWeight n ^ (N + 1) * (‖periodicPlus φ n - periodicMinus φ n‖ ^ 2 * ‖A‖)
      = (indexWeight n ^ (N + 1) * ‖periodicPlus φ n - periodicMinus φ n‖ ^ 2) * ‖A‖ := by ring
    _ ≤ (1600 * tP N φ n) * CA :=
        mul_le_mul (hk.trans hg2) hA (norm_nonneg _) (by linarith)
    _ = 1600 * CA * tP N φ n := by ring

theorem tP_sq_summable (N : ℕ) (φ : SobolevC N)
    (hent : ∀ (upper : Bool) (i j : Fin 2),
      WeightedL2Error ((N + 1 : ℕ) : ℝ) (KSPSWKB.endpointEntryError N φ upper i j)) :
    Summable (fun n : ℤ => tP N φ n ^ 2) := by
  have hE : ∀ (b : Bool) (i j : Fin 2), Summable (fun n : ℤ =>
      (indexWeight n ^ (N + 1) * ‖KSPSWKB.endpointEntryError N φ b i j n‖) ^ 2) :=
    fun b i j => (wl2_iff N _).1 (hent b i j)
  have hF1 : Summable (fun n : ℤ => ‖physicalFourier (iteratedDerivative N φ.1) (-n)‖ ^ 2) :=
    (hasSum_physicalFourier_sq (iteratedDerivative N φ.1)).summable.comp_injective neg_injective
  have hF2 : Summable (fun n : ℤ => ‖physicalFourier (iteratedDerivative N φ.2) n‖ ^ 2) :=
    (hasSum_physicalFourier_sq _).summable
  have hI : Summable (fun n : ℤ => (2 * ‖integralRiccatiLeft φ (N + 1)‖ * (1 / indexWeight n)) ^ 2) :=
    KSPS015W.sq_summable_mul_left _ KSPS016W.sq_summable_inv_w
  have h8 := KSPS015W.sq_summable_add (KSPS015W.sq_summable_add (KSPS015W.sq_summable_add
    (KSPS015W.sq_summable_add (KSPS015W.sq_summable_add (KSPS015W.sq_summable_add
      (KSPS015W.sq_summable_add (KSPS015W.sq_summable_add (KSPS015W.sq_summable_add
        (hE true 0 0) (hE true 0 1)) (hE true 1 0)) (hE true 1 1)) (hE false 0 0)) (hE false 0 1))
      (hE false 1 0)) (hE false 1 1)) (KSPS015W.sq_summable_add hF1 hF2)) hI
  refine h8.congr (fun n => ?_)
  unfold tP Eent
  ring

/-- Weighted gap sequence (all complex potentials; no square-root branch, no KSPS-025/027/028 input). -/
theorem gap_weighted_of
    (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N)
    (h20 : ∀ B : ℝ, 0 < B →
      ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ φ : SobolevC 1, sobolevNorm 1 φ ≤ B →
        ∀ n : ℤ, N ≤ n.natAbs →
          max ‖periodicPlus φ n-(n:ℂ)*Real.pi‖
              ‖periodicMinus φ n-(n:ℂ)*Real.pi‖ ≤
            C/(n.natAbs:ℝ))
    (h26 : EndpointQuadraticWKB N φ) :
    WeightedL2Error (N : ℝ) (fun n => periodicPlus φ n - periodicMinus φ n) := by
  obtain ⟨a, ha, hloc⟩ := NlsGge.ThirdConsultation.KSPS026W.periodic_localization_of hN φ h20
  obtain ⟨hent, hplus, hminus, -, -, hevq⟩ := h26
  rw [Filter.cocompact_eq_cofinite] at hevq
  have htP := tP_sq_summable N φ hent
  unfold WeightedL2Error
  have key : ∀ n : ℤ, indexWeight n ^ (2 * (N : ℝ)) * ‖periodicPlus φ n - periodicMinus φ n‖ ^ 2 =
      (indexWeight n ^ N * ‖periodicPlus φ n - periodicMinus φ n‖) ^ 2 := by
    intro n
    rw [show (2 * (N : ℝ)) = ((2 * N : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    ring
  simp_rw [key]
  refine Summable.of_norm_bounded_eventually (KSPS015W.sq_summable_mul_left 40 htP) ?_
  have e1 := KSPS015W.eventually_natAbs
    (⌈a⌉₊ + ⌈KSPSVolterra.threshold N (sobolevNorm N φ)⌉₊ + 1)
  have e2 := KSPS015W.eventually_natAbs (⌈a⌉₊ + ⌈2 * KSPS016W.Sb φ⌉₊ + 1)
  have e3 := KSPS015W.eventually_natAbs 1
  have e4 := eventually_w_ge (2 * (a + Jsum φ))
  have e5 := eventually_le_of_sq (tP N φ) htP (1 / 4) (by norm_num)
  have e6 := KSPS015W.eventually_natAbs ⌈2 * Lp φ⌉₊
  filter_upwards [e1, e2, e3, e4, e5, e6, hevq] with n g1 g2 g3 g4 g5 g6 g8
  have hL : 2 * Lp φ ≤ |(n : ℝ)| ^ 2 := by
    have h7 : ((⌈2 * Lp φ⌉₊ : ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast g6
    rw [Int.cast_abs] at h7
    push_cast at h7
    have h8 := Nat.le_ceil (2 * Lp φ)
    have h9 : (1 : ℝ) ≤ |(n : ℝ)| := by
      have : ((1 : ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast g3
      rw [Int.cast_abs] at this
      simpa using this
    nlinarith
  have hg := gap_bound N hN φ a ha (fun m => (hloc m).1) (fun m => (hloc m).2) hplus hminus n
    g1 g2 g4 g5 hL g8
  have hw0 : 0 ≤ indexWeight n ^ N := pow_nonneg (le_trans zero_le_one (KSPS015W.one_le_w n)) _
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (mul_nonneg hw0 (norm_nonneg _)) hg 2

/-! ### The weighted estimate (conditional on the landed KSPS-020/026, G1-054 heads and the KSPS-024 head) -/

theorem midpoint_spectral_expansion_of
    (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N)
    (h20 : ∀ B : ℝ, 0 < B →
      ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ φ : SobolevC 1, sobolevNorm 1 φ ≤ B →
        ∀ n : ℤ, N ≤ n.natAbs →
          max ‖periodicPlus φ n-(n:ℂ)*Real.pi‖
              ‖periodicMinus φ n-(n:ℂ)*Real.pi‖ ≤
            C/(n.natAbs:ℝ))
    (h26 : EndpointQuadraticWKB N φ)
    (h54 : ∀ φ0 : PotPair, ∃ N : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ V ∈ nhds φ0, ∀ φ ∈ V, ∃ a : ℤ → ℂ,
      (∀ n : ℤ, (N : ℤ) ≤ |n| →
        lamDot φ n - (lamPlus φ n + lamMinus φ n) / 2 = (lamPlus φ n - lamMinus φ n) ^ 2 * a n) ∧
      (∀ F : Finset ℤ, (∀ n ∈ F, (N : ℤ) ≤ |n|) → ∑ n ∈ F, ‖a n‖ ^ 2 ≤ C))
    (h24 : WeightedL2Error (N+1)
      (fun n => criticalEigenvalue φ n - spectralPolynomial φ n)) :
    WeightedL2Error (N+1)
      (fun n => NlsGge.ThirdConsultation.KSPS.midpoint φ n - spectralPolynomial φ n) := by
  obtain ⟨a, ha, hloc⟩ := NlsGge.ThirdConsultation.KSPS026W.periodic_localization_of hN φ h20
  obtain ⟨N54, C54, hC54, V, hV, hV'⟩ := h54 (toPotPair φ)
  obtain ⟨A, hAid, hAsum⟩ := hV' (toPotPair φ) (mem_of_mem_nhds hV)
  have hAb : ∀ n : ℤ, (N54 : ℤ) ≤ |n| → ‖A n‖ ≤ 1 + C54 := by
    intro n hn
    have h := hAsum {n} (fun m hm => by rw [Finset.mem_singleton.1 hm]; exact hn)
    rw [Finset.sum_singleton] at h
    nlinarith [sq_nonneg (‖A n‖ - 1)]
  obtain ⟨hent, hplus, hminus, -, -, hevq⟩ := h26
  rw [Filter.cocompact_eq_cofinite] at hevq
  have hs : ((N : ℝ) + 1) = ((N + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [hs] at h24 ⊢
  rw [wl2_iff] at h24
  have htP := tP_sq_summable N φ hent
  have hb : Summable (fun n : ℤ => (1600 * (1 + C54) * tP N φ n +
      indexWeight n ^ (N + 1) * ‖criticalEigenvalue φ n - spectralPolynomial φ n‖) ^ 2) :=
    KSPS015W.sq_summable_add (KSPS015W.sq_summable_mul_left _ htP) h24
  refine wl2_of_eventually N _ _ hb ?_
  have e1 := KSPS015W.eventually_natAbs
    (⌈a⌉₊ + ⌈KSPSVolterra.threshold N (sobolevNorm N φ)⌉₊ + 1)
  have e2 := KSPS015W.eventually_natAbs (⌈a⌉₊ + ⌈2 * KSPS016W.Sb φ⌉₊ + 1)
  have e3 := KSPS015W.eventually_natAbs 1
  have e4 := eventually_w_ge (2 * (a + Jsum φ))
  have e5 := eventually_le_of_sq (tP N φ) htP (1 / 4) (by norm_num)
  have e6 := KSPS015W.eventually_natAbs ⌈2 * Lp φ⌉₊
  have e7 := KSPS015W.eventually_natAbs N54
  filter_upwards [e1, e2, e3, e4, e5, e6, e7, hevq] with n g1 g2 g3 g4 g5 g6 g7 g8
  have hL : 2 * Lp φ ≤ |(n : ℝ)| ^ 2 := by
    have h7 : ((⌈2 * Lp φ⌉₊ : ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast g6
    rw [Int.cast_abs] at h7
    push_cast at h7
    have h8 := Nat.le_ceil (2 * Lp φ)
    have h9 : (1 : ℝ) ≤ |(n : ℝ)| := by
      have : ((1 : ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast g3
      rw [Int.cast_abs] at this
      simpa using this
    nlinarith
  have hid : criticalEigenvalue φ n - (periodicPlus φ n + periodicMinus φ n) / 2 =
      (periodicPlus φ n - periodicMinus φ n) ^ 2 * A n := hAid n g7
  have ht := tail025 N hN φ a ha (fun m => (hloc m).1) (fun m => (hloc m).2) hplus hminus n (A n)
    (1 + C54) (hAb n g7) hid g1 g2 g4 g5 hL g8
  have e : NlsGge.ThirdConsultation.KSPS.midpoint φ n - spectralPolynomial φ n =
      (NlsGge.ThirdConsultation.KSPS.midpoint φ n - criticalEigenvalue φ n) +
        (criticalEigenvalue φ n - spectralPolynomial φ n) := by ring
  rw [e]
  have hw0 : 0 ≤ indexWeight n ^ (N + 1) :=
    pow_nonneg (le_trans zero_le_one (KSPS015W.one_le_w n)) _
  have h9 := mul_le_mul_of_nonneg_left (norm_add_le
    (NlsGge.ThirdConsultation.KSPS.midpoint φ n - criticalEigenvalue φ n)
    (criticalEigenvalue φ n - spectralPolynomial φ n)) hw0
  rw [mul_add] at h9
  linarith

end
end NlsGge.ThirdConsultation.KSPS025W
