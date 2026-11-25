import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS012Support5
import NlsGge.ThirdConsultation.KSPS.KSPS011Support10
import NlsGge.ThirdConsultation.KSPS.KSPS007Support6
import NlsGge.ThirdConsultation.KSPS.IBP002Support

                                                                                                                    
                                                                                                           
                                                                                                         
                                                                                                                   
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Atomic.Common NlsGge.GK38
open NlsGge.Schur NlsGge.Analysis NlsGge.GKDefinitionDesign NlsGge.ThirdConsultation.KSPS

namespace NlsGge.ThirdConsultation.KSPSWKB

theorem q_bound (u : PhysicalSobolev38 ((1 : ℕ) : ℝ)) (a : ℝ) (ha : 0 ≤ a) :
    ∃ Q0 : ℝ, 0 ≤ Q0 ∧ ∀ μ : ℂ, μ ≠ 0 → |μ.im| ≤ a → ∀ t ∈ Icc (0 : ℝ) 1,
      ‖∫ s in t..1, Complex.exp (2 * Complex.I * μ * (s : ℂ)) *
        coverRep38 (physicalSobolevEmbed 1 u) s‖ ≤ Q0 / ‖μ‖ := by
  set K1 : ℝ := (2 * ‖iotaCLM‖ + ‖derivCLM‖) * ‖u‖ with hK1
  have hK10 : 0 ≤ K1 := by rw [hK1]; positivity
  refine ⟨Real.exp (2 * a) * K1, by positivity, fun μ hμ him t ht => ?_⟩
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
  calc _ ≤ Real.exp (2 * a) * K1 / (2 * ‖μ‖) + Real.exp (2 * a) * K1 / (2 * ‖μ‖) := add_le_add h1 h2
    _ = Real.exp (2 * a) * K1 / ‖μ‖ := by field_simp; ring

theorem F_to_c_bound {N : ℕ} (hN : 1 ≤ N) (φ : SobolevC N) (b : Bool)
    (u : PhysicalSobolev38 ((1 : ℕ) : ℝ)) (a : ℝ) (ha : 0 ≤ a) (L8 : ℝ) (hL8 : 0 < L8) :
    ∃ C1 : ℝ, 0 ≤ C1 ∧ ∀ (lam μ : ℂ), 1 ≤ ‖lam‖ → L8 ≤ ‖lam‖ → ‖μ‖ = ‖lam‖ → |μ.im| ≤ a →
      ‖-Complex.exp (-(2 * Complex.I * μ)) * endpointOsc μ (fun t =>
          (∫ s in t..1, Complex.exp (2 * Complex.I * μ * (s : ℂ)) *
            coverRep38 (physicalSobolevEmbed 1 u) s) *
          NlsGge.ThirdConsultation.KSPSRiccati.forcing φ b lam t) -
        -Complex.exp (-(2 * Complex.I * μ)) * endpointOsc μ (fun t =>
          (∫ s in t..1, Complex.exp (2 * Complex.I * μ * (s : ℂ)) *
            coverRep38 (physicalSobolevEmbed 1 u) s) *
          coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b (N + 1)) t)‖ ≤
        C1 / ‖lam‖ ^ 2 := by
  obtain ⟨K, hK0, hK⟩ := forcing_osc_expansion hN φ b a L8 hL8
  obtain ⟨M1, hM10, hM1b⟩ := a1_osc_bound hN φ b a
  obtain ⟨Q0, hQ0, hQ⟩ := q_bound u a ha
  set ea : ℝ := Real.exp a with hea
  have hea0 : 0 < ea := Real.exp_pos a
  refine ⟨Real.exp (2 * a) * (ea * Q0 * M1 / 2 + ea * Q0 * K), by positivity, ?_⟩
  intro lam μ hl1 hlL hμlam him
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
  have hE := hK lam hlL μ him q (Q0 / ‖lam‖) hqc hqb
  have hA := hM1b μ him q (Q0 / ‖lam‖) hqb
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

end NlsGge.ThirdConsultation.KSPSWKB
