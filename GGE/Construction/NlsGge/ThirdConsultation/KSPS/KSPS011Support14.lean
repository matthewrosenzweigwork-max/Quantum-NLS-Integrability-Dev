import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS011Support4
import NlsGge.ThirdConsultation.KSPS.KSPS011Support5
import NlsGge.ThirdConsultation.KSPS.KSPS011Support8
import NlsGge.ThirdConsultation.KSPS.KSPS011Support10
import NlsGge.ThirdConsultation.KSPS.KSPS011Support11
import NlsGge.ThirdConsultation.KSPS.KSPS011Support12
import NlsGge.ThirdConsultation.KSPS.KSPS011Support13

                                                                                                                                                                  
                                                                                           
                                                                                                                         
                                                                                                                             
                                                                                                                       
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open NlsGge.Pilot NlsGge.GK38 NlsGge.ThirdConsultation.KSPS

namespace NlsGge.ThirdConsultation.KSPSWKB

theorem norm_xi_lower (a : ℝ) (xi : ℤ → ℂ)
    (hxi : ∀ n : ℤ, ‖xi n - (n : ℂ) * Real.pi‖ ≤ a / indexWeight n) (n : ℤ) :
    Real.pi * |(n : ℝ)| - a ≤ ‖xi n‖ ∧ |(xi n).im| ≤ a := by
  have h1 := hxi n
  have hw := one_le_indexWeight n
  have ha : 0 ≤ a := by
    have : 0 ≤ a / indexWeight n := (norm_nonneg _).trans h1
    exact (div_nonneg_iff.1 this).elim (fun h => h.1) (fun h => by linarith [h.2])
  have h2 : a / indexWeight n ≤ a := div_le_self ha hw
  have h3 : ‖(n : ℂ) * (Real.pi : ℂ)‖ = Real.pi * |(n : ℝ)| := by
    rw [norm_mul, Complex.norm_intCast, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]; ring
  constructor
  · have := norm_sub_norm_le ((n : ℂ) * (Real.pi : ℂ)) (xi n)
    rw [norm_sub_rev, h3] at this
    linarith
  · have : (xi n).im = (xi n - (n : ℂ) * Real.pi).im := by simp
    rw [this]
    exact (Complex.abs_im_le_norm _).trans (h1.trans h2)

theorem indexWeight_le_two_mul (n : ℤ) (hn : 1 ≤ |(n : ℝ)|) : indexWeight n ≤ 2 * |(n : ℝ)| := by
  unfold indexWeight
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have : (n : ℝ) ^ 2 = |(n : ℝ)| ^ 2 := (sq_abs _).symm
  rw [this]; nlinarith

theorem endpoint_remainder_square_summable {N : ℕ} (hN : 1 ≤ N) (φ : SobolevC N) (b : Bool)
    (a : ℝ) (ha : 0 ≤ a) (xi : ℤ → ℂ)
    (hxi : ∀ n : ℤ, ‖xi n - (n : ℂ) * Real.pi‖ ≤ a / indexWeight n) :
    SquareSummable (fun n : ℤ => (indexWeight n : ℂ) *
      ((if hz : xi n = 0 then 0 else
          sourceRemainderVector φ b ⟨xi n, hz⟩ 1 (if b then 0 else 1)) -
        (if b then -Complex.I else Complex.I) * (-1 : ℂ) ^ n *
          (if b then (-1 : ℂ) ^ (N + 1) else -1) *
          physicalFourier (iteratedDerivative N (if b then φ.1 else φ.2))
            ((if b then (-1 : ℤ) else 1) * n))) := by
  obtain ⟨φ', hφ'⟩ := NlsGge.ThirdConsultation.KSPS011Support4.exists_toPair_eq hN φ
  set σ : ℤ := if b then -1 else 1 with hσdef
  have hσ : σ = 1 ∨ σ = -1 := by cases b <;> simp [hσdef]
  have hσc : (if b then (-1 : ℂ) else 1) = (σ : ℂ) := by cases b <;> simp [hσdef]
  set κ : ℂ := if b then -Complex.I else Complex.I with hκdef
  have hκ : ‖κ‖ = 1 := by cases b <;> simp [hκdef]
  set s : ℂ := if b then (-1 : ℂ) ^ (N + 1) else -1 with hsdef
  set D : PhysicalL2 := iteratedDerivative N (if b then φ.1 else φ.2) with hDdef
  set c : PhysicalL2 := NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b (N + 1) with hcdef
  -- the continuous multiplier q and its bound Q
  set q : ℝ → ℂ := fun t => NlsGge.ThirdConsultation.KSPSVolterra.integratedQuadratic φ' t 0 0 with hqdef
  have hqc : ContinuousOn q (Icc (0 : ℝ) 1) := by
    simp only [hqdef, integratedQuadratic_apply00]
    exact NlsGge.ThirdConsultation.KSPSSupport.h150_prim_continuousOn
      (NlsGge.ThirdConsultation.KSPSVolterra.toPair φ').1 (NlsGge.ThirdConsultation.KSPSVolterra.toPair φ').2
  obtain ⟨Q, hQ⟩ := isCompact_Icc.exists_bound_of_continuousOn hqc
  have hQ0 : 0 ≤ Q := (norm_nonneg _).trans (hQ 0 ⟨le_rfl, zero_le_one⟩)
  -- constants
  obtain ⟨C8, L8, hC8, hL8, h8⟩ :=
    sourceRemainder_endpoint_expansion hN φ φ' hφ' a ha
  obtain ⟨K, hK0, hK⟩ := forcing_osc_expansion hN φ b a L8 hL8
  obtain ⟨M1, hM1, hM1b⟩ := a1_osc_bound hN φ b a
  set ea : ℝ := Real.exp a with headef
  have hea : 0 < ea := Real.exp_pos a
  set B1 : ℝ := ea * K with hB1def
  set M2 : ℝ := ea * (M1 / 2 + K) with hM2def
  set M3 : ℝ := ea * Q * (M1 / 2 + K) with hM3def
  have hB1 : 0 ≤ B1 := by positivity
  have hM2 : 0 ≤ M2 := by positivity
  have hM3 : 0 ≤ M3 := by positivity
  set Kc : ℝ := 2 * C8 + 2 * B1 + (Q * M2 + M3) with hKcdef
  set N0 : ℕ := ⌈a + L8 + 1⌉₊ with hN0def
  -- the dominating real square summable sequence
  have hcmem : MemLp (coverRep38 c) 2 NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure :=
    NlsGge.ThirdConsultation.KSPSSupport.coverRep38_memLp_Icc c
  have ha1mem := NlsGge.ThirdConsultation.KSPSSupport.h150_a1_memLp φ b
  have hqcmem : MemLp (fun t => q t * coverRep38 c t) 2
      NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure :=
    NlsGge.ThirdConsultation.KSPSSupport.h150_memLp_mul_bdd _ _ hcmem hqc
  have S1 : RealSqSummable (fun n : ℤ => 1 / |(n : ℝ)|) := realSqSummable_inv_abs
  have S2 : RealSqSummable (fun n : ℤ => indexWeight n *
      ‖endpointOsc ((σ : ℂ) * xi n) (coverRep38 c) - (-1 : ℂ) ^ n * physicalFourier c (σ * n)‖) := by
    unfold RealSqSummable
    refine (osc_pert_seq (u := c) a ha xi hxi σ hσ).congr (fun n => ?_)
    rw [mul_pow]
  have S3 : RealSqSummable (fun n : ℤ => indexWeight n *
      ‖physicalFourier c (σ * n) - s * physicalFourier D (σ * n)‖) := by
    unfold RealSqSummable
    refine (coef_top_fourier hN φ b σ hσ).congr (fun n => ?_)
    rw [mul_pow]
  have S4 : RealSqSummable (fun n : ℤ => ‖endpointOsc ((σ : ℂ) * xi n)
      (NlsGge.ThirdConsultation.KSPSRiccati.a1 φ b)‖) := osc_sq_seq ha1mem a ha xi hxi σ hσ
  have S5 : RealSqSummable (fun n : ℤ => ‖endpointOsc ((σ : ℂ) * xi n) (coverRep38 c)‖) :=
    osc_sq_seq hcmem a ha xi hxi σ hσ
  have S6 : RealSqSummable (fun n : ℤ => ‖endpointOsc ((σ : ℂ) * xi n)
      (fun t => q t * coverRep38 c t)‖) := osc_sq_seq hqcmem a ha xi hxi σ hσ
  have Stot := (((((S1.mul_left Kc).add S2).add S3).add S4).add (S5.mul_left Q)).add S6
  refine squareSummable_of_bound _ _ Stot 1 N0 (fun n hn => ?_) (fun n => ?_)
  swap
  · beta_reduce
    have hKc : 0 ≤ Kc := by rw [hKcdef]; have := mul_nonneg hQ0 hM2; linarith
    have hn1 := indexWeight_pos n
    refine add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (mul_nonneg hKc ?_) ?_) ?_) ?_)
      (mul_nonneg hQ0 ?_)) ?_
    · positivity
    · exact mul_nonneg hn1.le (norm_nonneg _)
    · exact mul_nonneg hn1.le (norm_nonneg _)
    all_goals exact norm_nonneg _
  -- pointwise bound for |n| >= N0
  have hN0 : a + L8 + 1 ≤ (N0 : ℝ) := Nat.le_ceil _
  have hnabs : a + L8 + 1 ≤ |(n : ℝ)| := by
    have h1 : ((N0 : ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ) := Int.cast_le.2 hn
    rw [Int.cast_abs] at h1
    simp only [Int.cast_natCast] at h1
    linarith
  have hm1 : 1 ≤ |(n : ℝ)| := by linarith
  have hm0 : 0 ≤ |(n : ℝ)| := abs_nonneg _
  obtain ⟨hlow, himxi⟩ := norm_xi_lower a xi hxi n
  have hπ : 3 ≤ Real.pi := Real.pi_gt_three.le
  have hΛm : |(n : ℝ)| + L8 + 1 ≤ ‖xi n‖ := by
    nlinarith [mul_nonneg (sub_nonneg.2 hπ) hm0]
  have hΛ1 : 1 ≤ ‖xi n‖ := by linarith
  have hΛpos : 0 < ‖xi n‖ := by linarith
  have hz : xi n ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hΛ1; linarith
  have hwm : indexWeight n ≤ 2 * |(n : ℝ)| := indexWeight_le_two_mul n hm1
  obtain ⟨f, hf⟩ := exists_forcing_potPair φ b ⟨xi n, hz⟩
  have hv := h8 b ⟨xi n, hz⟩ (by show L8 ≤ ‖xi n‖; linarith) (by show |(xi n).im| ≤ a; exact himxi) f hf
  have hcomp := comp_formula φ φ' b ⟨xi n, hz⟩ f hf
  rw [Pi.add_apply] at hcomp
  have hU : ‖sourceRemainderVector φ b ⟨xi n, hz⟩ 1 (if b then 0 else 1) -
      (NlsGge.ThirdConsultation.KSPSVolterra.forcingLeading φ' (xi n) f 1 +
        NlsGge.ThirdConsultation.KSPSVolterra.forcingFirstCorrection φ' (xi n) f 1)
          (if b then 0 else 1)‖ ≤ C8 / ‖xi n‖ ^ 2 := by
    refine le_trans ?_ hv
    have : (sourceRemainderVector φ b ⟨xi n, hz⟩ 1 -
        NlsGge.ThirdConsultation.KSPSVolterra.forcingLeading φ' (xi n) f 1 -
        NlsGge.ThirdConsultation.KSPSVolterra.forcingFirstCorrection φ' (xi n) f 1) (if b then 0 else 1) =
        sourceRemainderVector φ b ⟨xi n, hz⟩ 1 (if b then 0 else 1) -
        (NlsGge.ThirdConsultation.KSPSVolterra.forcingLeading φ' (xi n) f 1 +
          NlsGge.ThirdConsultation.KSPSVolterra.forcingFirstCorrection φ' (xi n) f 1)
            (if b then 0 else 1) := by
      simp only [Pi.sub_apply, Pi.add_apply, sub_sub]
    rw [← this]
    exact norm_le_pi_norm _ _
  -- the oscillatory quantities
  have hImμ : |(((σ : ℂ) * xi n)).im| ≤ a := by
    rcases hσ with h | h <;> rw [h] <;> simpa using himxi
  have hcont1 : ContinuousOn (fun _ : ℝ => (1 : ℂ)) (Icc (0 : ℝ) 1) := continuousOn_const
  have hE1 := hK (xi n) (by linarith) ((σ : ℂ) * xi n) hImμ (fun _ => 1) 1 hcont1
    (fun t _ => by simp)
  have hE2 := hK (xi n) (by linarith) ((σ : ℂ) * xi n) hImμ q Q hqc hQ
  have hA1 := hM1b ((σ : ℂ) * xi n) hImμ (fun _ => 1) 1 (fun t _ => by simp)
  have hA2 := hM1b ((σ : ℂ) * xi n) hImμ q Q hQ
  simp only [one_mul] at hE1 hA1
  have hk1 : ‖(2 * Complex.I * xi n)⁻¹‖ = 1 / (2 * ‖xi n‖) := by
    rw [norm_inv, norm_mul, norm_mul]; simp
  have hEa : ‖endpointOsc ((σ : ℂ) * xi n) (NlsGge.ThirdConsultation.KSPSRiccati.forcing φ b (xi n)) -
      endpointOsc ((σ : ℂ) * xi n) (coverRep38 c) -
      (2 * Complex.I * xi n)⁻¹ * endpointOsc ((σ : ℂ) * xi n)
        (NlsGge.ThirdConsultation.KSPSRiccati.a1 φ b)‖ ≤ B1 / ‖xi n‖ ^ 2 := by
    simpa [hB1def, headef] using hE1
  have hEq : ‖endpointOsc ((σ : ℂ) * xi n) (fun t => q t * NlsGge.ThirdConsultation.KSPSRiccati.forcing φ b (xi n) t) -
      endpointOsc ((σ : ℂ) * xi n) (fun t => q t * coverRep38 c t) -
      (2 * Complex.I * xi n)⁻¹ * endpointOsc ((σ : ℂ) * xi n)
        (fun t => q t * NlsGge.ThirdConsultation.KSPSRiccati.a1 φ b t)‖ ≤ ea * Q * K / ‖xi n‖ ^ 2 := hE2
  have hAa : ‖endpointOsc ((σ : ℂ) * xi n) (NlsGge.ThirdConsultation.KSPSRiccati.a1 φ b)‖ ≤ ea * M1 := by
    simpa [headef] using hA1
  have hAq : ‖endpointOsc ((σ : ℂ) * xi n) (fun t => q t * NlsGge.ThirdConsultation.KSPSRiccati.a1 φ b t)‖ ≤
      ea * Q * M1 := hA2
  set μ : ℂ := (σ : ℂ) * xi n with hμ
  set k1 : ℂ := (2 * Complex.I * xi n)⁻¹ with hk1def
  set Of := endpointOsc μ (NlsGge.ThirdConsultation.KSPSRiccati.forcing φ b (xi n)) with hOf
  set Oc := endpointOsc μ (coverRep38 c) with hOc
  set Oa := endpointOsc μ (NlsGge.ThirdConsultation.KSPSRiccati.a1 φ b) with hOa
  set Oqf := endpointOsc μ (fun t => q t * NlsGge.ThirdConsultation.KSPSRiccati.forcing φ b (xi n) t) with hOqf
  set Oqc := endpointOsc μ (fun t => q t * coverRep38 c t) with hOqc
  set Oqa := endpointOsc μ (fun t => q t * NlsGge.ThirdConsultation.KSPSRiccati.a1 φ b t) with hOqa
  have hΛ2 : ‖xi n‖ ≤ ‖xi n‖ ^ 2 := by nlinarith
  have hdOf : ‖Of - Oc‖ ≤ M2 / ‖xi n‖ := by
    have e : Of - Oc = (Of - Oc - k1 * Oa) + k1 * Oa := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖Of - Oc - k1 * Oa‖ ≤ B1 / ‖xi n‖ := hEa.trans
      (div_le_div_of_nonneg_left hB1 hΛpos hΛ2)
    have h2 : ‖k1 * Oa‖ ≤ (ea * M1 / 2) / ‖xi n‖ := by
      rw [norm_mul, hk1]
      calc 1 / (2 * ‖xi n‖) * ‖Oa‖ ≤ 1 / (2 * ‖xi n‖) * (ea * M1) := by gcongr
        _ = (ea * M1 / 2) / ‖xi n‖ := by field_simp
    have h3 : M2 / ‖xi n‖ = B1 / ‖xi n‖ + (ea * M1 / 2) / ‖xi n‖ := by
      rw [hM2def, hB1def]; field_simp; ring
    linarith
  have hdOq : ‖Oqf - Oqc‖ ≤ M3 / ‖xi n‖ := by
    have e : Oqf - Oqc = (Oqf - Oqc - k1 * Oqa) + k1 * Oqa := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖Oqf - Oqc - k1 * Oqa‖ ≤ ea * Q * K / ‖xi n‖ := hEq.trans
      (div_le_div_of_nonneg_left (by positivity) hΛpos hΛ2)
    have h2 : ‖k1 * Oqa‖ ≤ (ea * Q * M1 / 2) / ‖xi n‖ := by
      rw [norm_mul, hk1]
      calc 1 / (2 * ‖xi n‖) * ‖Oqa‖ ≤ 1 / (2 * ‖xi n‖) * (ea * Q * M1) := by gcongr
        _ = (ea * Q * M1 / 2) / ‖xi n‖ := by field_simp
    have h3 : M3 / ‖xi n‖ = ea * Q * K / ‖xi n‖ + (ea * Q * M1 / 2) / ‖xi n‖ := by
      rw [hM3def]; field_simp; ring
    linarith
  -- the final algebraic identity
  have hcomp' : (NlsGge.ThirdConsultation.KSPSVolterra.forcingLeading φ' (xi n) f 1 +
        NlsGge.ThirdConsultation.KSPSVolterra.forcingFirstCorrection φ' (xi n) f 1) (if b then 0 else 1) =
      κ * Of + (2 * xi n)⁻¹ * (q 1 * Of - Oqf) := by
    have h := hcomp
    rw [hσc] at h
    exact h
  have hpb := endpoint_pointwise_bound (indexWeight n) ‖xi n‖ |(n : ℝ)| C8 B1 M2 M3 Q (indexWeight_pos n).le hΛpos hm1
    (by linarith) hwm hC8 hB1 hM2 hM3 hQ0 (xi n) κ ((-1 : ℂ) ^ n) k1
    (Oc - (-1 : ℂ) ^ n * physicalFourier c (σ * n))
    (physicalFourier c (σ * n) - s * physicalFourier D (σ * n)) Oa Oc Oqc
    (Of - Oc - k1 * Oa)
    (sourceRemainderVector φ b ⟨xi n, hz⟩ 1 (if b then 0 else 1) -
      (NlsGge.ThirdConsultation.KSPSVolterra.forcingLeading φ' (xi n) f 1 +
        NlsGge.ThirdConsultation.KSPSVolterra.forcingFirstCorrection φ' (xi n) f 1) (if b then 0 else 1))
    (q 1) (Of - Oc) (Oqf - Oqc) rfl hκ (by simp) (hk1 ▸ le_rfl) hU hEa (hQ 1 ⟨zero_le_one, le_rfl⟩)
    hdOf hdOq
  have hid : sourceRemainderVector φ b ⟨xi n, hz⟩ 1 (if b then 0 else 1) -
        κ * (-1 : ℂ) ^ n * s * physicalFourier D (σ * n) =
      (sourceRemainderVector φ b ⟨xi n, hz⟩ 1 (if b then 0 else 1) -
        (NlsGge.ThirdConsultation.KSPSVolterra.forcingLeading φ' (xi n) f 1 +
          NlsGge.ThirdConsultation.KSPSVolterra.forcingFirstCorrection φ' (xi n) f 1) (if b then 0 else 1)) +
      κ * (k1 * Oa) + κ * (Of - Oc - k1 * Oa) +
      κ * ((Oc - (-1 : ℂ) ^ n * physicalFourier c (σ * n)) + (-1 : ℂ) ^ n *
        (physicalFourier c (σ * n) - s * physicalFourier D (σ * n))) +
      (2 * xi n)⁻¹ * (q 1 * Oc - Oqc) + (2 * xi n)⁻¹ * (q 1 * (Of - Oc) - (Oqf - Oqc)) := by
    rw [hcomp']; ring
  beta_reduce
  rw [dif_neg hz, norm_mul, Complex.norm_real, Real.norm_of_nonneg (indexWeight_pos n).le, hid]
  refine hpb.trans (le_of_eq ?_)
  rw [hKcdef, mul_one_div, one_mul]

end NlsGge.ThirdConsultation.KSPSWKB
