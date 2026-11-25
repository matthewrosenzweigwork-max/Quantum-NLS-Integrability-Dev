import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS011Support14
import NlsGge.ThirdConsultation.KSPS.KSPS011Quant2

                                                                                 
                                                                                                  
                                                                                                                     
                                                                                                                         
                                                   
                                                                                                                        
                                                                                                                 
                                                                                                                     
                                                                                                                  
                                                                                              
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open NlsGge.Pilot NlsGge.GK38 NlsGge.ThirdConsultation.KSPS

namespace NlsGge.ThirdConsultation.KSPSWKB

theorem sourceRemainder_endpoint_expansion_U {N : ℕ} (hN : 1 ≤ N) (KB B : ℝ) (hKB : 0 ≤ KB) (hB : 0 ≤ B)
    (a : ℝ) (ha : 0 ≤ a) :
    ∃ C L : ℝ, 0 ≤ C ∧ 0 < L ∧ ∀ φ : NlsGge.ThirdConsultation.KSPS.SobolevC N, ‖φ.1‖ + ‖φ.2‖ ≤ KB →
      ∀ φ' : NlsGge.ThirdConsultation.KSPS.SobolevC 1, NlsGge.ThirdConsultation.KSPS.sobolevNorm 1 φ' ≤ B →
      NlsGge.ThirdConsultation.KSPSVolterra.toPair φ' = NlsGge.ThirdConsultation.KSPS.toPotPair φ →
      ∀ (b : Bool) (lam : {z : ℂ // z ≠ 0}), L ≤ ‖lam.1‖ → |lam.1.im| ≤ a →
      ∀ f : PotPair,
        (∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)),
          ![potRepFst38 f t, potRepSnd38 f t] = sourceForcingVector φ b lam t) →
        ‖sourceRemainderVector φ b lam 1 -
            NlsGge.ThirdConsultation.KSPSVolterra.forcingLeading φ' lam.1 f 1 -
            NlsGge.ThirdConsultation.KSPSVolterra.forcingFirstCorrection φ' lam.1 f 1‖ ≤
          C / ‖lam.1‖ ^ 2 := by
  obtain ⟨C0, L, hC0, hL, h7⟩ := NlsGge.ThirdConsultation.KSPS.forced_solution_expansion a B ha hB
  obtain ⟨K, hK0, hK⟩ := NlsGge.ThirdConsultation.KSPSQ2.sourceForcing_vectorL2Norm_U hN KB hKB L a hL ha
  refine ⟨C0 * K, L, by positivity, hL, fun φ hS φ' hφB hφ b lam hlam hIm f hf => ?_⟩
  have hF := sourceRemainderVector_forcedZS φ φ' hφ b lam f hf
  have h := h7 φ' hφB f lam.1 hlam hIm _ hF 1 ⟨zero_le_one, le_rfl⟩
  refine h.trans ?_
  rw [mul_div_assoc, mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hC0
  exact div_le_div_of_nonneg_right (hK φ hS b lam hlam hIm f hf) (by positivity)

theorem endpoint_remainder_pointwise_U {N : ℕ} (hN : 1 ≤ N) (KB B : ℝ) (hKB : 0 ≤ KB) (hB : 0 ≤ B)
    (b : Bool) (a : ℝ) (ha : 0 ≤ a) :
    ∃ (N0 : ℕ) (Kc Q : ℝ), 0 ≤ Kc ∧ 0 ≤ Q ∧
    ∀ φ : SobolevC N, ‖φ.1‖ + ‖φ.2‖ ≤ KB →
    ∀ φ' : SobolevC 1, sobolevNorm 1 φ' ≤ B →
      NlsGge.ThirdConsultation.KSPSVolterra.toPair φ' = NlsGge.ThirdConsultation.KSPS.toPotPair φ →
    (∀ t ∈ Icc (0 : ℝ) 1, ‖NlsGge.ThirdConsultation.KSPSVolterra.integratedQuadratic φ' t 0 0‖ ≤ Q) ∧
    ∀ (xi : ℤ → ℂ), (∀ n : ℤ, ‖xi n - (n : ℂ) * Real.pi‖ ≤ a / indexWeight n) →
    ∀ n : ℤ, (N0 : ℤ) ≤ |n| →
    ‖(indexWeight n : ℂ) *
      ((if hz : xi n = 0 then 0 else
          sourceRemainderVector φ b ⟨xi n, hz⟩ 1 (if b then 0 else 1)) -
        (if b then -Complex.I else Complex.I) * (-1 : ℂ) ^ n *
          (if b then (-1 : ℂ) ^ (N + 1) else -1) *
          physicalFourier (iteratedDerivative N (if b then φ.1 else φ.2))
            ((if b then (-1 : ℤ) else 1) * n))‖ ≤
      Kc * (1 / |(n : ℝ)|) +
      indexWeight n * ‖endpointOsc (((if b then (-1 : ℤ) else 1 : ℤ) : ℂ) * xi n)
          (coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b (N + 1))) -
        (-1 : ℂ) ^ n * physicalFourier (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b (N + 1))
          ((if b then (-1 : ℤ) else 1) * n)‖ +
      indexWeight n * ‖physicalFourier (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b (N + 1))
          ((if b then (-1 : ℤ) else 1) * n) -
        (if b then (-1 : ℂ) ^ (N + 1) else -1) *
          physicalFourier (iteratedDerivative N (if b then φ.1 else φ.2)) ((if b then (-1 : ℤ) else 1) * n)‖ +
      ‖endpointOsc (((if b then (-1 : ℤ) else 1 : ℤ) : ℂ) * xi n) (NlsGge.ThirdConsultation.KSPSRiccati.a1 φ b)‖ +
      Q * ‖endpointOsc (((if b then (-1 : ℤ) else 1 : ℤ) : ℂ) * xi n)
          (coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b (N + 1)))‖ +
      ‖endpointOsc (((if b then (-1 : ℤ) else 1 : ℤ) : ℂ) * xi n)
          (fun t => NlsGge.ThirdConsultation.KSPSVolterra.integratedQuadratic φ' t 0 0 *
            coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b (N + 1)) t)‖ := by
  obtain ⟨C8, L8, hC8, hL8, h8⟩ := sourceRemainder_endpoint_expansion_U hN KB B hKB hB a ha
  obtain ⟨K, hK0, hK⟩ := NlsGge.ThirdConsultation.KSPSQ2.forcing_osc_U hN KB hKB b a L8 hL8
  obtain ⟨M1, hM1, hM1b⟩ := NlsGge.ThirdConsultation.KSPSQ2.a1_osc_U hN KB hKB b a
  set Q : ℝ := KB ^ 2 with hQdef
  have hQ0 : 0 ≤ Q := sq_nonneg _
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
  have hKc : 0 ≤ Kc := by rw [hKcdef]; have := mul_nonneg hQ0 hM2; linarith
  refine ⟨N0, Kc, Q, hKc, hQ0, fun φ hS φ' hφ'B hφ' => ?_⟩
  set σ : ℤ := if b then -1 else 1 with hσdef
  have hσ : σ = 1 ∨ σ = -1 := by cases b <;> simp [hσdef]
  have hσc : (if b then (-1 : ℂ) else 1) = (σ : ℂ) := by cases b <;> simp [hσdef]
  set κ : ℂ := if b then -Complex.I else Complex.I with hκdef
  have hκ : ‖κ‖ = 1 := by cases b <;> simp [hκdef]
  set s : ℂ := if b then (-1 : ℂ) ^ (N + 1) else -1 with hsdef
  set D : PhysicalL2 := iteratedDerivative N (if b then φ.1 else φ.2) with hDdef
  set c : PhysicalL2 := NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b (N + 1) with hcdef
  set q : ℝ → ℂ := fun t => NlsGge.ThirdConsultation.KSPSVolterra.integratedQuadratic φ' t 0 0 with hqdef
  have hqc : ContinuousOn q (Icc (0 : ℝ) 1) := by
    simp only [hqdef, integratedQuadratic_apply00]
    exact NlsGge.ThirdConsultation.KSPSSupport.h150_prim_continuousOn
      (NlsGge.ThirdConsultation.KSPSVolterra.toPair φ').1 (NlsGge.ThirdConsultation.KSPSVolterra.toPair φ').2
  have hQ : ∀ t ∈ Icc (0 : ℝ) 1, ‖q t‖ ≤ Q := by
    intro t ht
    simp only [hqdef, integratedQuadratic_apply00]
    have h := NlsGge.ThirdConsultation.KSPSSupport.h161_prefix_le
      (NlsGge.ThirdConsultation.KSPSVolterra.toPair φ').1 (NlsGge.ThirdConsultation.KSPSVolterra.toPair φ').2 ht
    have e1 : ‖(NlsGge.ThirdConsultation.KSPSVolterra.toPair φ').1‖ ≤ KB := by
      rw [hφ']
      exact (NlsGge.ThirdConsultation.KSPSSupport.h161_embed_norm_le N φ.1).trans
        (by linarith [norm_nonneg φ.2])
    have e2 : ‖(NlsGge.ThirdConsultation.KSPSVolterra.toPair φ').2‖ ≤ KB := by
      rw [hφ']
      exact (NlsGge.ThirdConsultation.KSPSSupport.h161_embed_norm_le N φ.2).trans
        (by linarith [norm_nonneg φ.1])
    have e1s := pow_le_pow_left₀ (norm_nonneg _) e1 2
    have e2s := pow_le_pow_left₀ (norm_nonneg _) e2 2
    unfold potRepFst38 potRepSnd38
    rw [hQdef]
    linarith
  refine ⟨hQ, fun xi hxi n hn => ?_⟩
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
  have hv := h8 φ hS φ' hφ'B hφ' b ⟨xi n, hz⟩ (by show L8 ≤ ‖xi n‖; linarith) (by show |(xi n).im| ≤ a; exact himxi) f hf
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
  have hE1 := hK φ hS (xi n) (by linarith) ((σ : ℂ) * xi n) hImμ (fun _ => 1) 1 hcont1
    (fun t _ => by simp)
  have hE2 := hK φ hS (xi n) (by linarith) ((σ : ℂ) * xi n) hImμ q Q hqc hQ
  have hA1 := hM1b φ hS ((σ : ℂ) * xi n) hImμ (fun _ => 1) 1 (fun t _ => by simp)
  have hA2 := hM1b φ hS ((σ : ℂ) * xi n) hImμ q Q hQ
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
  rw [dif_neg hz, norm_mul, Complex.norm_real, Real.norm_of_nonneg (indexWeight_pos n).le, hid]
  refine hpb.trans (le_of_eq ?_)
  rw [hKcdef, mul_one_div]

end NlsGge.ThirdConsultation.KSPSWKB
