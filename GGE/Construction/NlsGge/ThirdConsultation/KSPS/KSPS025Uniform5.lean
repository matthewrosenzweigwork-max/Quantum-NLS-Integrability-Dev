import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS025Support
import NlsGge.ThirdConsultation.KSPS.KSPSUniformU3

                                                                                 
                                                                                                             
                                                                                                                  
                                                                                                              
                                                                                                        
                                                                                                                  
                                                                                                                    
                                                                                                           
                                                                                                                      
                                                                                                                       
set_option autoImplicit false
open MeasureTheory Filter
open scoped BigOperators Topology

namespace NlsGge.ThirdConsultation.KSPS025U5
noncomputable section
open NlsGge.Pilot NlsGge.GK38
open NlsGge.ThirdConsultation.KSPS NlsGge.ThirdConsultation.KSPS021W NlsGge.ThirdConsultation.KSPS023W
open NlsGge.ThirdConsultation.KSPS024W NlsGge.ThirdConsultation.KSPS025W

/-! ### (1) Ball bounds of the cutoff constants -/

theorem ecb_mono (N : ℕ) (B' B : ℝ) (h : B' ≤ B) (k : ℕ) (hk : k ∈ Finset.Icc 1 N) :
    NlsGge.ThirdConsultation.KSPSVolterra.endpointCoefficientBound N B' k ≤
      NlsGge.ThirdConsultation.KSPSVolterra.endpointCoefficientBound N B k := by
  have hk' := Finset.mem_Icc.mp hk
  unfold NlsGge.ThirdConsultation.KSPSVolterra.endpointCoefficientBound
  refine csSup_le_csSup (NlsGge.ThirdConsultation.KSPSWKB.endpoint_coefficient_set_bounded N k hk' B)
    ⟨0, Or.inl rfl⟩ ?_
  rintro r (hr | ⟨φ, b, hφ, rfl⟩)
  · exact Or.inl hr
  · exact Or.inr ⟨φ, b, hφ.trans (max_le_max h le_rfl), rfl⟩

/-- The ball value of the threshold sum `Sb`. -/
def SbB (N : ℕ) (B : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 N, NlsGge.ThirdConsultation.KSPSVolterra.endpointCoefficientBound N B k

theorem SbB_nonneg (N : ℕ) (B : ℝ) : 0 ≤ SbB N B :=
  Finset.sum_nonneg (fun k hk => NlsGge.ThirdConsultation.KSPSWKB.endpointCoefficientBound_nonneg N B k hk)

theorem Sb_le (N : ℕ) (B : ℝ) (φ : SobolevC N) (hφ : sobolevNorm N φ ≤ B) :
    NlsGge.ThirdConsultation.KSPS016W.Sb φ ≤ SbB N B := by
  unfold NlsGge.ThirdConsultation.KSPS016W.Sb SbB
  exact Finset.sum_le_sum (fun k hk => ecb_mono N _ _ hφ k hk)

theorem threshold_le (N : ℕ) (B : ℝ) (φ : SobolevC N) (hφ : sobolevNorm N φ ≤ B) :
    NlsGge.ThirdConsultation.KSPSVolterra.threshold N (sobolevNorm N φ) ≤
      NlsGge.ThirdConsultation.KSPSVolterra.threshold N B := by
  unfold NlsGge.ThirdConsultation.KSPSVolterra.threshold
  have := Finset.sum_le_sum (fun k hk => ecb_mono N _ _ hφ k hk)
  linarith

/-- One constant bounding `Jsum`, `Lp`, `Lsum` and `‖integralRiccatiLeft φ (N+1)‖` on the ball. -/
theorem riccati_consts_uniform (N : ℕ) (hN : 1 ≤ N) (B₀ : ℝ) (hB₀ : 0 ≤ B₀) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      Jsum φ ≤ L ∧ NlsGge.ThirdConsultation.KSPS024W.Lp φ ≤ L ∧ NlsGge.ThirdConsultation.KSPS023W.Lsum φ ≤ L ∧
        ‖integralRiccatiLeft φ (N + 1)‖ ≤ L := by
  obtain ⟨C, hC, hb⟩ := NlsGge.ThirdConsultation.KSPSU3.integralRiccatiLeft_uniform N hN B₀ hB₀
  refine ⟨((N : ℝ) + 2) * ((N : ℝ) + 1) * C, by positivity, fun φ hφ => ?_⟩
  have hk : ∀ k ∈ Finset.Icc 1 (N + 1), ‖integralRiccatiLeft φ k‖ ≤ C := fun k hk =>
    hb φ hφ k (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2
  have hkk : ∀ k ∈ Finset.Icc 1 (N + 1), (k : ℝ) * ‖integralRiccatiLeft φ k‖ ≤ ((N : ℝ) + 1) * C := by
    intro k hk'
    have h1 : (k : ℝ) ≤ (N : ℝ) + 1 := by exact_mod_cast (Finset.mem_Icc.mp hk').2
    exact mul_le_mul h1 (hk k hk') (norm_nonneg _) (by positivity)
  have hsub : Finset.Icc 1 N ⊆ Finset.Icc 1 (N + 1) := Finset.Icc_subset_Icc le_rfl (Nat.le_succ N)
  have hcard : ((Finset.Icc 1 (N + 1)).card : ℝ) = (N : ℝ) + 1 := by
    rw [Nat.card_Icc]; push_cast; ring
  have hLs : NlsGge.ThirdConsultation.KSPS023W.Lsum φ ≤ ((N : ℝ) + 1) * (((N : ℝ) + 1) * C) := by
    unfold NlsGge.ThirdConsultation.KSPS023W.Lsum
    refine (Finset.sum_le_sum hkk).trans (le_of_eq ?_)
    rw [Finset.sum_const, nsmul_eq_mul, hcard]
  have hLp : NlsGge.ThirdConsultation.KSPS024W.Lp φ ≤ NlsGge.ThirdConsultation.KSPS023W.Lsum φ := by
    unfold NlsGge.ThirdConsultation.KSPS024W.Lp NlsGge.ThirdConsultation.KSPS023W.Lsum
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => by positivity)
  have hJ : Jsum φ ≤ ((N : ℝ) + 1) * C := by
    unfold Jsum
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => norm_nonneg _)).trans ?_
    refine (Finset.sum_le_sum hk).trans (le_of_eq ?_)
    rw [Finset.sum_const, nsmul_eq_mul, hcard]
  have hIN := hk (N + 1) (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)
  have hC1 : C ≤ ((N : ℝ) + 1) * C := le_mul_of_one_le_left hC (by linarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)])
  have hNC : ((N : ℝ) + 1) * C ≤ ((N : ℝ) + 2) * ((N : ℝ) + 1) * C := by
    have h0 : 0 ≤ ((N : ℝ) + 1) * C := by positivity
    nlinarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)]
  have hLL : ((N : ℝ) + 1) * (((N : ℝ) + 1) * C) ≤ ((N : ℝ) + 2) * ((N : ℝ) + 1) * C := by
    have h0 : 0 ≤ ((N : ℝ) + 1) * C := by positivity
    nlinarith
  exact ⟨hJ.trans hNC, hLp.trans (hLs.trans hLL), hLs.trans hLL, hIN.trans (hC1.trans hNC)⟩

/-! ### (2) The KSPS-025 tail algebra without the cutoff `tP ≤ 1/4` -/

theorem side_bound_U (N : ℕ) (φ : SobolevC N) (a : ℝ) (ha : 0 ≤ a) (upper : Bool) (xi : ℤ → ℂ)
    (hxe : ∀ n, (if upper then periodicPlus φ n else periodicMinus φ n) = xi n)
    (hxi : ∀ n : ℤ, ‖xi n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n) (n : ℤ)
    (h1 : ((⌈a⌉₊ + ⌈KSPSVolterra.threshold N (sobolevNorm N φ)⌉₊ + 1 : ℕ) : ℤ) ≤ |n|)
    (h2 : ((⌈a⌉₊ + ⌈2 * KSPS016W.Sb φ⌉₊ + 1 : ℕ) : ℤ) ≤ |n|)
    (h4 : 2 * (a + Jsum φ) ≤ indexWeight n)
    (hz : xi n ≠ 0)
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
  set θ : ℂ := NlsGge.ThirdConsultation.KSPS.wkbPhase φ (xi n) with hθ
  set ε : ℂ := θ - (n : ℂ) * (Real.pi : ℂ) with hεdef
  -- eps is small (no cutoff needed)
  have hε : ‖ε‖ ≤ 1 / 2 := by
    have := phase_small φ (xi n) n (indexWeight n) a hw0 hX1 hwX (hxi n)
    have h7 : (a + Jsum φ) / indexWeight n ≤ 1 / 2 := by
      rw [div_le_iff₀ hw0]
      linarith
    unfold Jsum at h7
    rw [hεdef, hθ]
    linarith
  have h10 : ‖ε‖ ≤ 10 * R := by
    by_cases hR4 : R ≤ 1 / 4
    · have heta : (-1 : ℂ) ^ n * Complex.exp (Complex.I * θ) = Complex.exp (Complex.I * ε) := eta_eq θ n
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
      have hεu := eps_le_two_exp ε hε
      linarith
    · push_neg at hR4
      linarith
  have hwN0 : 0 ≤ indexWeight n ^ N := pow_nonneg hw0.le N
  calc indexWeight n ^ N * ‖ε‖ ≤ indexWeight n ^ N * (10 * R) :=
        mul_le_mul_of_nonneg_left h10 hwN0
    _ = 10 * (indexWeight n ^ N * R) := by ring
    _ ≤ 10 * tP N φ n := by linarith

theorem gap_bound_U (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N) (a : ℝ) (ha : 0 ≤ a)
    (hxp : ∀ n : ℤ, ‖periodicPlus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n)
    (hxm : ∀ n : ℤ, ‖periodicMinus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n)
    (hplus hminus : ℤ → ℂ) (n : ℤ)
    (h1 : ((⌈a⌉₊ + ⌈KSPSVolterra.threshold N (sobolevNorm N φ)⌉₊ + 1 : ℕ) : ℤ) ≤ |n|)
    (h2 : ((⌈a⌉₊ + ⌈2 * KSPS016W.Sb φ⌉₊ + 1 : ℕ) : ℤ) ≤ |n|)
    (h4 : 2 * (a + Jsum φ) ≤ indexWeight n)
    (hL : 2 * NlsGge.ThirdConsultation.KSPS024W.Lp φ ≤ |(n : ℝ)| ^ 2)
    (hqf : KSPSWKB.endpointQuadraticFormula N φ n hplus hminus) :
    indexWeight n ^ N * ‖periodicPlus φ n - periodicMinus φ n‖ ≤ 40 * tP N φ n := by
  obtain ⟨hp, hm, hqp, hqm⟩ := hqf
  obtain ⟨-, hqp2, -⟩ := hqp
  obtain ⟨-, hqm2, -⟩ := hqm
  have hsp := side_bound_U N φ a ha true (periodicPlus φ) (fun _ => rfl) hxp n h1 h2 h4 hp hqp2
  have hsm := side_bound_U N φ a ha false (periodicMinus φ) (fun _ => rfl) hxm n h1 h2 h4 hm hqm2
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

theorem tail025_U (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N) (a : ℝ) (ha : 0 ≤ a)
    (hxp : ∀ n : ℤ, ‖periodicPlus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n)
    (hxm : ∀ n : ℤ, ‖periodicMinus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n)
    (hplus hminus : ℤ → ℂ) (n : ℤ) (A : ℂ) (CA : ℝ) (hA : ‖A‖ ≤ CA)
    (hid : criticalEigenvalue φ n - (periodicPlus φ n + periodicMinus φ n) / 2 =
      (periodicPlus φ n - periodicMinus φ n) ^ 2 * A)
    (h1 : ((⌈a⌉₊ + ⌈KSPSVolterra.threshold N (sobolevNorm N φ)⌉₊ + 1 : ℕ) : ℤ) ≤ |n|)
    (h2 : ((⌈a⌉₊ + ⌈2 * KSPS016W.Sb φ⌉₊ + 1 : ℕ) : ℤ) ≤ |n|)
    (h4 : 2 * (a + Jsum φ) ≤ indexWeight n)
    (hL : 2 * NlsGge.ThirdConsultation.KSPS024W.Lp φ ≤ |(n : ℝ)| ^ 2)
    (hqf : KSPSWKB.endpointQuadraticFormula N φ n hplus hminus) :
    indexWeight n ^ (N + 1) * ‖NlsGge.ThirdConsultation.KSPS.midpoint φ n - criticalEigenvalue φ n‖ ≤
      CA * (40 * tP N φ n) ^ 2 := by
  have hg := gap_bound_U N hN φ a ha hxp hxm hplus hminus n h1 h2 h4 hL hqf
  have hw1 := KSPS015W.one_le_w n
  have hw0 : 0 < indexWeight n := by linarith
  have hwN0 : 0 ≤ indexWeight n ^ N := pow_nonneg hw0.le N
  set g : ℝ := indexWeight n ^ N * ‖periodicPlus φ n - periodicMinus φ n‖ with hgdef
  have hg0 : 0 ≤ g := mul_nonneg hwN0 (norm_nonneg _)
  have hmid : NlsGge.ThirdConsultation.KSPS.midpoint φ n - criticalEigenvalue φ n =
      -((periodicPlus φ n - periodicMinus φ n) ^ 2 * A) := by
    unfold NlsGge.ThirdConsultation.KSPS.midpoint
    linear_combination (-1 : ℂ) * hid
  rw [hmid, norm_neg, norm_mul, norm_pow]
  have hw2 : indexWeight n ^ (N + 1) ≤ indexWeight n ^ (2 * N) := pow_le_pow_right₀ hw1 (by omega)
  have hk : indexWeight n ^ (N + 1) * ‖periodicPlus φ n - periodicMinus φ n‖ ^ 2 ≤ g ^ 2 := by
    have e : g ^ 2 = indexWeight n ^ (2 * N) * ‖periodicPlus φ n - periodicMinus φ n‖ ^ 2 := by
      rw [hgdef]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_right hw2 (sq_nonneg _)
  have hg2 : g ^ 2 ≤ (40 * tP N φ n) ^ 2 := pow_le_pow_left₀ hg0 hg 2
  have hCA : 0 ≤ CA := (norm_nonneg A).trans hA
  calc indexWeight n ^ (N + 1) * (‖periodicPlus φ n - periodicMinus φ n‖ ^ 2 * ‖A‖)
      = (indexWeight n ^ (N + 1) * ‖periodicPlus φ n - periodicMinus φ n‖ ^ 2) * ‖A‖ := by ring
    _ ≤ (40 * tP N φ n) ^ 2 * CA :=
        mul_le_mul (hk.trans hg2) hA (norm_nonneg _) (sq_nonneg _)
    _ = CA * (40 * tP N φ n) ^ 2 := by ring

end
end NlsGge.ThirdConsultation.KSPS025U5
