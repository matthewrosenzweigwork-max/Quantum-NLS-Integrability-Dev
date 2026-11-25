import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS012Support10
import NlsGge.ThirdConsultation.KSPS.KSPS011Quant2

                                                                                 
                                                                                                  
                                                                                                                 
                                                           
                                                                              
                                                                                                                    
                                        
                                                                                                               
                                                                                                                         
                                                                                                                     
                                                        
                          
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Atomic.Common NlsGge.GK38
open NlsGge.Schur NlsGge.Analysis NlsGge.GKDefinitionDesign NlsGge.ThirdConsultation.KSPS

namespace NlsGge.ThirdConsultation.KSPS012Q3
open NlsGge.ThirdConsultation.KSPSWKB

theorem q_bound_U (u : PhysicalSobolev38 ((1 : ℕ) : ℝ)) (a : ℝ) (ha : 0 ≤ a) (Bu : ℝ) (hu : ‖u‖ ≤ Bu) :
    ∀ μ : ℂ, μ ≠ 0 → |μ.im| ≤ a → ∀ t ∈ Icc (0 : ℝ) 1,
      ‖∫ s in t..1, Complex.exp (2 * Complex.I * μ * (s : ℂ)) *
        coverRep38 (physicalSobolevEmbed 1 u) s‖ ≤
        Real.exp (2 * a) * ((2 * ‖iotaCLM‖ + ‖derivCLM‖) * Bu) / ‖μ‖ := by
  set K1 : ℝ := (2 * ‖iotaCLM‖ + ‖derivCLM‖) * ‖u‖ with hK1
  intro μ hμ him t ht
  have hν : (2 * Complex.I * μ) ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) hμ
  have hre : |(2 * Complex.I * μ).re| ≤ 2 * a := by
    have : (2 * Complex.I * μ).re = -(2 * μ.im) := by simp [Complex.mul_re]
    rw [this, abs_neg, abs_mul, abs_two]
    exact mul_le_mul_of_nonneg_left him (by norm_num)
  have hνn : ‖2 * Complex.I * μ‖ = 2 * ‖μ‖ := by
    rw [norm_mul, norm_mul, Complex.norm_I]; simp
  have hfc : Continuous fun s : ℝ => Complex.exp (2 * Complex.I * μ * (s : ℂ)) := by fun_prop
  have hf1 : IntervalIntegrable (fun s : ℝ => Complex.exp (2 * Complex.I * μ * (s : ℂ)) *
      coverRep38 (physicalSobolevEmbed 1 u) s) volume 0 1 :=
    (intervalIntegrable_coverRep38_one _).continuousOn_mul hfc.continuousOn
  have hsub : Set.uIcc (0 : ℝ) t ⊆ Set.uIcc (0 : ℝ) 1 := by
    rw [uIcc_of_le ht.1, uIcc_of_le zero_le_one]; exact Icc_subset_Icc le_rfl ht.2
  have hI : ∫ s in t..1, Complex.exp (2 * Complex.I * μ * (s : ℂ)) *
        coverRep38 (physicalSobolevEmbed 1 u) s =
      (∫ s in (0 : ℝ)..1, Complex.exp (2 * Complex.I * μ * (s : ℂ)) *
        coverRep38 (physicalSobolevEmbed 1 u) s) -
      ∫ s in (0 : ℝ)..t, Complex.exp (2 * Complex.I * μ * (s : ℂ)) *
        coverRep38 (physicalSobolevEmbed 1 u) s :=
    (intervalIntegral.integral_interval_sub_left hf1 (hf1.mono_set hsub)).symm
  have h1 := NlsGge.ThirdConsultation.KSPS007Support6.osc_bound u hν hre (t := 1) ⟨zero_le_one, le_rfl⟩
  have h2 := NlsGge.ThirdConsultation.KSPS007Support6.osc_bound u hν hre ht
  rw [hI]
  refine (norm_sub_le _ _).trans ?_
  have hμpos : 0 < ‖μ‖ := norm_pos_iff.mpr hμ
  have e1 : Real.exp (2 * a) * ((2 * ‖iotaCLM‖ + ‖derivCLM‖) * ‖u‖) / ‖2 * Complex.I * μ‖ =
      Real.exp (2 * a) * K1 / (2 * ‖μ‖) := by rw [hνn, hK1]
  rw [e1] at h1 h2
  have hKB : K1 ≤ (2 * ‖iotaCLM‖ + ‖derivCLM‖) * Bu :=
    mul_le_mul_of_nonneg_left hu (by positivity)
  have hmono : Real.exp (2 * a) * K1 / ‖μ‖ ≤
      Real.exp (2 * a) * ((2 * ‖iotaCLM‖ + ‖derivCLM‖) * Bu) / ‖μ‖ :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hKB (Real.exp_pos _).le) hμpos.le
  calc _ ≤ Real.exp (2 * a) * K1 / (2 * ‖μ‖) + Real.exp (2 * a) * K1 / (2 * ‖μ‖) := add_le_add h1 h2
    _ = Real.exp (2 * a) * K1 / ‖μ‖ := by field_simp; ring
    _ ≤ _ := hmono

theorem F_to_c_bound_U {N : ℕ} (hN : 1 ≤ N) (KB : ℝ) (hKB : 0 ≤ KB) (b : Bool)
    (Bu : ℝ) (hBu : 0 ≤ Bu) (a : ℝ) (ha : 0 ≤ a) (L8 : ℝ) (hL8 : 0 < L8) :
    ∃ C1 : ℝ, 0 ≤ C1 ∧ ∀ φ : SobolevC N, ‖φ.1‖ + ‖φ.2‖ ≤ KB →
      ∀ u : PhysicalSobolev38 ((1 : ℕ) : ℝ), ‖u‖ ≤ Bu →
      ∀ (lam μ : ℂ), 1 ≤ ‖lam‖ → L8 ≤ ‖lam‖ → ‖μ‖ = ‖lam‖ → |μ.im| ≤ a →
      ‖-Complex.exp (-(2 * Complex.I * μ)) * endpointOsc μ (fun t =>
          (∫ s in t..1, Complex.exp (2 * Complex.I * μ * (s : ℂ)) *
            coverRep38 (physicalSobolevEmbed 1 u) s) *
          NlsGge.ThirdConsultation.KSPSRiccati.forcing φ b lam t) -
        -Complex.exp (-(2 * Complex.I * μ)) * endpointOsc μ (fun t =>
          (∫ s in t..1, Complex.exp (2 * Complex.I * μ * (s : ℂ)) *
            coverRep38 (physicalSobolevEmbed 1 u) s) *
          coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b (N + 1)) t)‖ ≤
        C1 / ‖lam‖ ^ 2 := by
  obtain ⟨K, hK0, hK⟩ := NlsGge.ThirdConsultation.KSPSQ2.forcing_osc_U hN KB hKB b a L8 hL8
  obtain ⟨M1, hM10, hM1b⟩ := NlsGge.ThirdConsultation.KSPSQ2.a1_osc_U hN KB hKB b a
  set Q0 : ℝ := Real.exp (2 * a) * ((2 * ‖iotaCLM‖ + ‖derivCLM‖) * Bu) with hQ0def
  have hQ0 : 0 ≤ Q0 := by rw [hQ0def]; positivity
  set ea : ℝ := Real.exp a with hea
  have hea0 : 0 < ea := Real.exp_pos a
  refine ⟨Real.exp (2 * a) * (ea * Q0 * M1 / 2 + ea * Q0 * K), by positivity, ?_⟩
  intro φ hφ u hu lam μ hl1 hlL hμlam him
  have hQ := q_bound_U u a ha Bu hu
  have hlpos : 0 < ‖lam‖ := by linarith
  have hμ0 : μ ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hμlam; linarith
  -- the multiplier q
  set q : ℝ → ℂ := fun t => ∫ s in t..1, Complex.exp (2 * Complex.I * μ * (s : ℂ)) *
      coverRep38 (physicalSobolevEmbed 1 u) s with hqdef
  have hqc : ContinuousOn q (Icc (0 : ℝ) 1) :=
    NlsGge.ThirdConsultation.KSPS012Support5.Dd_continuousOn (intervalIntegrable_coverRep38_one _) μ
  have hqb : ∀ t ∈ Icc (0 : ℝ) 1, ‖q t‖ ≤ Q0 / ‖lam‖ := by
    intro t ht
    have := hQ μ hμ0 him t ht
    rw [hμlam] at this
    exact this
  have hQnn : 0 ≤ Q0 / ‖lam‖ := by positivity
  have hE := hK φ hφ lam hlL μ him q (Q0 / ‖lam‖) hqc hqb
  have hA := hM1b φ hφ μ him q (Q0 / ‖lam‖) hqb
  set Of := endpointOsc μ (fun t => q t * NlsGge.ThirdConsultation.KSPSRiccati.forcing φ b lam t) with hOf
  set Oc := endpointOsc μ (fun t => q t * coverRep38
    (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b (N + 1)) t) with hOc
  set Oa := endpointOsc μ (fun t => q t * NlsGge.ThirdConsultation.KSPSRiccati.a1 φ b t) with hOa
  have hk1 : ‖(2 * Complex.I * lam)⁻¹‖ = 1 / (2 * ‖lam‖) := by
    rw [norm_inv, norm_mul, norm_mul]; simp
  have hdiff : ‖Of - Oc‖ ≤ ea * (Q0 / ‖lam‖) * K / ‖lam‖ ^ 2 + 1 / (2 * ‖lam‖) * (ea * (Q0 / ‖lam‖) * M1) := by
    have e : Of - Oc = (Of - Oc - (2 * Complex.I * lam)⁻¹ * Oa) + (2 * Complex.I * lam)⁻¹ * Oa := by ring
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add hE ?_)
    rw [norm_mul, hk1]
    exact mul_le_mul_of_nonneg_left hA (by positivity)
  have hexp : ‖-Complex.exp (-(2 * Complex.I * μ))‖ ≤ Real.exp (2 * a) := by
    rw [norm_neg, Complex.norm_exp]
    refine Real.exp_le_exp.2 ?_
    have : (-(2 * Complex.I * μ)).re = 2 * μ.im := by simp [Complex.mul_re]
    rw [this]
    have := (le_abs_self μ.im).trans him
    linarith
  rw [← mul_sub, norm_mul]
  have hl2 : ‖lam‖ ≤ ‖lam‖ ^ 2 := by nlinarith
  calc ‖-Complex.exp (-(2 * Complex.I * μ))‖ * ‖Of - Oc‖
      ≤ Real.exp (2 * a) * (ea * (Q0 / ‖lam‖) * K / ‖lam‖ ^ 2 +
          1 / (2 * ‖lam‖) * (ea * (Q0 / ‖lam‖) * M1)) :=
        mul_le_mul hexp hdiff (norm_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (2 * a) * (ea * Q0 * K / ‖lam‖ ^ 3 + ea * Q0 * M1 / 2 / ‖lam‖ ^ 2) := by
        field_simp
    _ ≤ Real.exp (2 * a) * (ea * Q0 * K / ‖lam‖ ^ 2 + ea * Q0 * M1 / 2 / ‖lam‖ ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        have : ea * Q0 * K / ‖lam‖ ^ 3 ≤ ea * Q0 * K / ‖lam‖ ^ 2 := by
          refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
          nlinarith [pow_pos hlpos 2]
        linarith
    _ = Real.exp (2 * a) * (ea * Q0 * M1 / 2 + ea * Q0 * K) / ‖lam‖ ^ 2 := by
        field_simp
        ring

theorem diag_approx_false_U_of {N : ℕ} (hN : 1 ≤ N) (KB B : ℝ) (hKB : 0 ≤ KB) (hB : 0 ≤ B)
    (a : ℝ) (ha : 0 ≤ a)
    (C8 L8 : ℝ) (hC8 : 0 ≤ C8) (hL8 : 0 < L8)
    (h8U : ∀ φ : NlsGge.ThirdConsultation.KSPS.SobolevC N, ‖φ.1‖ + ‖φ.2‖ ≤ KB →
      ∀ φ' : NlsGge.ThirdConsultation.KSPS.SobolevC 1, NlsGge.ThirdConsultation.KSPS.sobolevNorm 1 φ' ≤ B →
      NlsGge.ThirdConsultation.KSPSVolterra.toPair φ' = NlsGge.ThirdConsultation.KSPS.toPotPair φ →
      ∀ (b : Bool) (lam : {z : ℂ // z ≠ 0}), L8 ≤ ‖lam.1‖ → |lam.1.im| ≤ a →
      ∀ f : PotPair,
        (∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)),
          ![potRepFst38 f t, potRepSnd38 f t] = sourceForcingVector φ b lam t) →
        ‖sourceRemainderVector φ b lam 1 -
            NlsGge.ThirdConsultation.KSPSVolterra.forcingLeading φ' lam.1 f 1 -
            NlsGge.ThirdConsultation.KSPSVolterra.forcingFirstCorrection φ' lam.1 f 1‖ ≤
          C8 / ‖lam.1‖ ^ 2) :
    ∃ C L : ℝ, 0 ≤ C ∧ 1 ≤ L ∧ ∀ φ : SobolevC N, ‖φ.1‖ + ‖φ.2‖ ≤ KB →
      ∀ φ' : SobolevC 1, sobolevNorm 1 φ' ≤ B →
      NlsGge.ThirdConsultation.KSPSVolterra.toPair φ' = toPotPair φ →
      ∀ lam : {z : ℂ // z ≠ 0}, L ≤ ‖lam.1‖ → |lam.1.im| ≤ a →
      ‖sourceRemainderVector φ false lam 1 0 -
        (-Complex.exp (-(2 * Complex.I * lam.1)) * endpointOsc lam.1 (fun t =>
          (∫ s in t..1, Complex.exp (2 * Complex.I * lam.1 * (s : ℂ)) *
            coverRep38 (physicalSobolevEmbed 1 φ'.1) s) *
          coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ false (N + 1)) t))‖ ≤
        C / ‖lam.1‖ ^ 2 := by
  obtain ⟨C1, hC1, hFU⟩ := F_to_c_bound_U hN KB hKB false B hB a ha L8 hL8
  refine ⟨C8 + C1, max L8 1, by positivity, le_max_right _ _, fun φ hφ φ' hφ'B hφ' lam hL him => ?_⟩
  have h8 := h8U φ hφ φ' hφ'B hφ'
  have hF := hFU φ hφ φ'.1 ((NlsGge.ThirdConsultation.KSPS007Support6.norm_fst_le_s φ').trans hφ'B)
  have hL8' : L8 ≤ ‖lam.1‖ := (le_max_left _ _).trans hL
  have hl1 : 1 ≤ ‖lam.1‖ := (le_max_right _ _).trans hL
  obtain ⟨f, hf⟩ := exists_forcing_potPair φ false lam
  have hv := h8 false lam hL8' him f hf
  have hU : ‖sourceRemainderVector φ false lam 1 0 -
      (NlsGge.ThirdConsultation.KSPSVolterra.forcingLeading φ' lam.1 f 1 +
        NlsGge.ThirdConsultation.KSPSVolterra.forcingFirstCorrection φ' lam.1 f 1) 0‖ ≤
      C8 / ‖lam.1‖ ^ 2 := by
    refine le_trans ?_ hv
    have : (sourceRemainderVector φ false lam 1 -
        NlsGge.ThirdConsultation.KSPSVolterra.forcingLeading φ' lam.1 f 1 -
        NlsGge.ThirdConsultation.KSPSVolterra.forcingFirstCorrection φ' lam.1 f 1) 0 =
        sourceRemainderVector φ false lam 1 0 -
        (NlsGge.ThirdConsultation.KSPSVolterra.forcingLeading φ' lam.1 f 1 +
          NlsGge.ThirdConsultation.KSPSVolterra.forcingFirstCorrection φ' lam.1 f 1) 0 := by
      simp only [Pi.sub_apply, Pi.add_apply, sub_sub]
    rw [← this]
    exact norm_le_pi_norm _ _
  have hcomp := lower_diag_component φ' lam.1 lam.2 f
    (NlsGge.ThirdConsultation.KSPSRiccati.forcing φ false lam.1)
    (forcing_intervalIntegrable φ false lam.1) (by
      refine hf.mono (fun t ht => ?_)
      rw [ht]
      simp [sourceForcingVector])
  have hX := hF lam.1 lam.1 hl1 hL8' rfl him
  have hXF : ‖(NlsGge.ThirdConsultation.KSPSVolterra.forcingLeading φ' lam.1 f 1 +
        NlsGge.ThirdConsultation.KSPSVolterra.forcingFirstCorrection φ' lam.1 f 1) 0 -
      (-Complex.exp (-(2 * Complex.I * lam.1)) * endpointOsc lam.1 (fun t =>
          (∫ s in t..1, Complex.exp (2 * Complex.I * lam.1 * (s : ℂ)) *
            coverRep38 (physicalSobolevEmbed 1 φ'.1) s) *
          coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ false (N + 1)) t))‖ ≤
      C1 / ‖lam.1‖ ^ 2 := by
    rw [hcomp]
    exact hX
  have e : sourceRemainderVector φ false lam 1 0 -
      (-Complex.exp (-(2 * Complex.I * lam.1)) * endpointOsc lam.1 (fun t =>
          (∫ s in t..1, Complex.exp (2 * Complex.I * lam.1 * (s : ℂ)) *
            coverRep38 (physicalSobolevEmbed 1 φ'.1) s) *
          coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ false (N + 1)) t)) =
      (sourceRemainderVector φ false lam 1 0 -
        (NlsGge.ThirdConsultation.KSPSVolterra.forcingLeading φ' lam.1 f 1 +
          NlsGge.ThirdConsultation.KSPSVolterra.forcingFirstCorrection φ' lam.1 f 1) 0) +
      ((NlsGge.ThirdConsultation.KSPSVolterra.forcingLeading φ' lam.1 f 1 +
        NlsGge.ThirdConsultation.KSPSVolterra.forcingFirstCorrection φ' lam.1 f 1) 0 -
      (-Complex.exp (-(2 * Complex.I * lam.1)) * endpointOsc lam.1 (fun t =>
          (∫ s in t..1, Complex.exp (2 * Complex.I * lam.1 * (s : ℂ)) *
            coverRep38 (physicalSobolevEmbed 1 φ'.1) s) *
          coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ false (N + 1)) t))) := by ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  calc _ ≤ C8 / ‖lam.1‖ ^ 2 + C1 / ‖lam.1‖ ^ 2 := add_le_add hU hXF
    _ = (C8 + C1) / ‖lam.1‖ ^ 2 := by ring

theorem diag_approx_true_U_of {N : ℕ} (hN : 1 ≤ N) (KB B : ℝ) (hKB : 0 ≤ KB) (hB : 0 ≤ B)
    (a : ℝ) (ha : 0 ≤ a)
    (C8 L8 : ℝ) (hC8 : 0 ≤ C8) (hL8 : 0 < L8)
    (h8U : ∀ φ : NlsGge.ThirdConsultation.KSPS.SobolevC N, ‖φ.1‖ + ‖φ.2‖ ≤ KB →
      ∀ φ' : NlsGge.ThirdConsultation.KSPS.SobolevC 1, NlsGge.ThirdConsultation.KSPS.sobolevNorm 1 φ' ≤ B →
      NlsGge.ThirdConsultation.KSPSVolterra.toPair φ' = NlsGge.ThirdConsultation.KSPS.toPotPair φ →
      ∀ (b : Bool) (lam : {z : ℂ // z ≠ 0}), L8 ≤ ‖lam.1‖ → |lam.1.im| ≤ a →
      ∀ f : PotPair,
        (∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)),
          ![potRepFst38 f t, potRepSnd38 f t] = sourceForcingVector φ b lam t) →
        ‖sourceRemainderVector φ b lam 1 -
            NlsGge.ThirdConsultation.KSPSVolterra.forcingLeading φ' lam.1 f 1 -
            NlsGge.ThirdConsultation.KSPSVolterra.forcingFirstCorrection φ' lam.1 f 1‖ ≤
          C8 / ‖lam.1‖ ^ 2) :
    ∃ C L : ℝ, 0 ≤ C ∧ 1 ≤ L ∧ ∀ φ : SobolevC N, ‖φ.1‖ + ‖φ.2‖ ≤ KB →
      ∀ φ' : SobolevC 1, sobolevNorm 1 φ' ≤ B →
      NlsGge.ThirdConsultation.KSPSVolterra.toPair φ' = toPotPair φ →
      ∀ lam : {z : ℂ // z ≠ 0}, L ≤ ‖lam.1‖ → |lam.1.im| ≤ a →
      ‖sourceRemainderVector φ true lam 1 1 -
        (-Complex.exp (-(2 * Complex.I * (-lam.1))) * endpointOsc (-lam.1) (fun t =>
          (∫ s in t..1, Complex.exp (2 * Complex.I * (-lam.1) * (s : ℂ)) *
            coverRep38 (physicalSobolevEmbed 1 φ'.2) s) *
          coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ true (N + 1)) t))‖ ≤
        C / ‖lam.1‖ ^ 2 := by
  obtain ⟨C1, hC1, hFU⟩ := F_to_c_bound_U hN KB hKB true B hB a ha L8 hL8
  refine ⟨C8 + C1, max L8 1, by positivity, le_max_right _ _, fun φ hφ φ' hφ'B hφ' lam hL him => ?_⟩
  have h8 := h8U φ hφ φ' hφ'B hφ'
  have hF := hFU φ hφ φ'.2 ((NlsGge.ThirdConsultation.KSPS007Support6.norm_snd_le_s φ').trans hφ'B)
  have hL8' : L8 ≤ ‖lam.1‖ := (le_max_left _ _).trans hL
  have hl1 : 1 ≤ ‖lam.1‖ := (le_max_right _ _).trans hL
  obtain ⟨f, hf⟩ := exists_forcing_potPair φ true lam
  have hv := h8 true lam hL8' him f hf
  have hU : ‖sourceRemainderVector φ true lam 1 1 -
      (NlsGge.ThirdConsultation.KSPSVolterra.forcingLeading φ' lam.1 f 1 +
        NlsGge.ThirdConsultation.KSPSVolterra.forcingFirstCorrection φ' lam.1 f 1) 1‖ ≤
      C8 / ‖lam.1‖ ^ 2 := by
    refine le_trans ?_ hv
    have : (sourceRemainderVector φ true lam 1 -
        NlsGge.ThirdConsultation.KSPSVolterra.forcingLeading φ' lam.1 f 1 -
        NlsGge.ThirdConsultation.KSPSVolterra.forcingFirstCorrection φ' lam.1 f 1) 1 =
        sourceRemainderVector φ true lam 1 1 -
        (NlsGge.ThirdConsultation.KSPSVolterra.forcingLeading φ' lam.1 f 1 +
          NlsGge.ThirdConsultation.KSPSVolterra.forcingFirstCorrection φ' lam.1 f 1) 1 := by
      simp only [Pi.sub_apply, Pi.add_apply, sub_sub]
    rw [← this]
    exact norm_le_pi_norm _ _
  have hcomp := upper_diag_component φ' lam.1 lam.2 f
    (NlsGge.ThirdConsultation.KSPSRiccati.forcing φ true lam.1)
    (forcing_intervalIntegrable φ true lam.1) (by
      refine hf.mono (fun t ht => ?_)
      rw [ht]
      simp [sourceForcingVector])
  have him' : |(-lam.1).im| ≤ a := by simpa using him
  have hX := hF lam.1 (-lam.1) hl1 hL8' (norm_neg _) him'
  have hXF : ‖(NlsGge.ThirdConsultation.KSPSVolterra.forcingLeading φ' lam.1 f 1 +
        NlsGge.ThirdConsultation.KSPSVolterra.forcingFirstCorrection φ' lam.1 f 1) 1 -
      (-Complex.exp (-(2 * Complex.I * (-lam.1))) * endpointOsc (-lam.1) (fun t =>
          (∫ s in t..1, Complex.exp (2 * Complex.I * (-lam.1) * (s : ℂ)) *
            coverRep38 (physicalSobolevEmbed 1 φ'.2) s) *
          coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ true (N + 1)) t))‖ ≤
      C1 / ‖lam.1‖ ^ 2 := by
    rw [hcomp]
    exact hX
  have e : sourceRemainderVector φ true lam 1 1 -
      (-Complex.exp (-(2 * Complex.I * (-lam.1))) * endpointOsc (-lam.1) (fun t =>
          (∫ s in t..1, Complex.exp (2 * Complex.I * (-lam.1) * (s : ℂ)) *
            coverRep38 (physicalSobolevEmbed 1 φ'.2) s) *
          coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ true (N + 1)) t)) =
      (sourceRemainderVector φ true lam 1 1 -
        (NlsGge.ThirdConsultation.KSPSVolterra.forcingLeading φ' lam.1 f 1 +
          NlsGge.ThirdConsultation.KSPSVolterra.forcingFirstCorrection φ' lam.1 f 1) 1) +
      ((NlsGge.ThirdConsultation.KSPSVolterra.forcingLeading φ' lam.1 f 1 +
        NlsGge.ThirdConsultation.KSPSVolterra.forcingFirstCorrection φ' lam.1 f 1) 1 -
      (-Complex.exp (-(2 * Complex.I * (-lam.1))) * endpointOsc (-lam.1) (fun t =>
          (∫ s in t..1, Complex.exp (2 * Complex.I * (-lam.1) * (s : ℂ)) *
            coverRep38 (physicalSobolevEmbed 1 φ'.2) s) *
          coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ true (N + 1)) t))) := by ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  calc _ ≤ C8 / ‖lam.1‖ ^ 2 + C1 / ‖lam.1‖ ^ 2 := add_le_add hU hXF
    _ = (C8 + C1) / ‖lam.1‖ ^ 2 := by ring

end NlsGge.ThirdConsultation.KSPS012Q3
