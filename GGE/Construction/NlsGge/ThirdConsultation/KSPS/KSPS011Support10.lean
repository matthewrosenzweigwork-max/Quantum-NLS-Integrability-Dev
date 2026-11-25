import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS011Support7
import NlsGge.ThirdConsultation.KSPS.KSPS011Support9

                                                                                                                                                                          
                                                                                                  
                                                                                                              
                                                                                                                         
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.ThirdConsultation.KSPSWKB

theorem intervalIntegrable_of_memLp {H : ℝ → ℂ}
    (hH : MemLp H 2 NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure) :
    IntervalIntegrable H volume 0 1 := by
  haveI := isFiniteMeasure_intervalMeasure
  have h1 : Integrable H NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure :=
    hH.integrable (by norm_num)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  unfold NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure at h1
  exact (show IntegrableOn H (Icc (0 : ℝ) 1) volume from h1).mono_set Ioc_subset_Icc_self

theorem intervalIntegrable_sq_of_memLp {H : ℝ → ℂ}
    (hH : MemLp H 2 NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure) :
    IntervalIntegrable (fun t => ‖H t‖ ^ 2) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  have h := (memLp_two_iff_integrable_sq_norm hH.aestronglyMeasurable).mp hH
  unfold NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure at h
  exact (show IntegrableOn (fun t => ‖H t‖ ^ 2) (Icc (0 : ℝ) 1) volume from h).mono_set Ioc_subset_Icc_self

theorem integral_norm_le_eLpNorm {H : ℝ → ℂ}
    (hH : MemLp H 2 NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure) :
    ∫ t in (0 : ℝ)..1, ‖H t‖ ≤
      (eLpNorm H 2 NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure).toReal := by
  have hi1 : IntervalIntegrable (fun t => ‖H t‖) volume 0 1 := (intervalIntegrable_of_memLp hH).norm
  have hi2 := intervalIntegrable_sq_of_memLp hH
  have hJ := integral_sq_eq_eLpNorm hH
  set m : ℝ := ∫ t in (0 : ℝ)..1, ‖H t‖ with hm
  set s : ℝ := (eLpNorm H 2 NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure).toReal with hs
  have hs0 : 0 ≤ s := ENNReal.toReal_nonneg
  have h0 : 0 ≤ ∫ t in (0 : ℝ)..1, (‖H t‖ - m) ^ 2 :=
    intervalIntegral.integral_nonneg zero_le_one (fun t _ => sq_nonneg _)
  have h1 : ∫ t in (0 : ℝ)..1, (‖H t‖ - m) ^ 2 = (∫ t in (0 : ℝ)..1, ‖H t‖ ^ 2) - 2 * m * m + m ^ 2 := by
    have e : ∀ t : ℝ, (‖H t‖ - m) ^ 2 = (‖H t‖ ^ 2 - 2 * m * ‖H t‖) + m ^ 2 := fun t => by ring
    simp_rw [e]
    rw [intervalIntegral.integral_add (hi2.sub (hi1.const_mul (2 * m))) intervalIntegrable_const,
      intervalIntegral.integral_sub hi2 (hi1.const_mul (2 * m)), intervalIntegral.integral_const_mul]
    simp
    exact Or.inl rfl
  have hmm : m ^ 2 ≤ s ^ 2 := by
    rw [← hJ]; nlinarith
  have hm0 : 0 ≤ m := intervalIntegral.integral_nonneg zero_le_one (fun t _ => norm_nonneg _)
  exact (sq_le_sq₀ hm0 hs0).1 hmm

theorem norm_exp_osc_le {μ : ℂ} {a : ℝ} (hμ : |μ.im| ≤ a) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖Complex.exp (Complex.I * μ * ((1 - 2 * t : ℝ) : ℂ))‖ ≤ Real.exp a := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.2
  have : (Complex.I * μ * ((1 - 2 * t : ℝ) : ℂ)).re = -(μ.im * (1 - 2 * t)) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [this]
  have h1 : |1 - 2 * t| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  calc -(μ.im * (1 - 2 * t)) ≤ |μ.im * (1 - 2 * t)| := neg_le_abs _
    _ = |μ.im| * |1 - 2 * t| := abs_mul _ _
    _ ≤ |μ.im| * 1 := by gcongr
    _ ≤ a := by linarith

theorem norm_endpointOsc_mul_le {μ : ℂ} {a : ℝ} (hμ : |μ.im| ≤ a) {q H : ℝ → ℂ} {Q : ℝ}
    (hq : ∀ t ∈ Icc (0 : ℝ) 1, ‖q t‖ ≤ Q) (hH : IntervalIntegrable (fun t => ‖H t‖) volume 0 1) :
    ‖endpointOsc μ (fun t => q t * H t)‖ ≤ Real.exp a * Q * ∫ t in (0 : ℝ)..1, ‖H t‖ := by
  unfold endpointOsc
  have hb : ∫ t in (0 : ℝ)..1, Real.exp a * Q * ‖H t‖ = Real.exp a * Q * ∫ t in (0 : ℝ)..1, ‖H t‖ :=
    intervalIntegral.integral_const_mul _ _
  rw [← hb]
  refine intervalIntegral.norm_integral_le_of_norm_le zero_le_one (Filter.Eventually.of_forall (fun t ht => ?_))
    (hH.const_mul _)
  have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
  have h1 := norm_exp_osc_le hμ ht'
  have h2 := hq t ht'
  calc ‖Complex.exp (Complex.I * μ * ((1 - 2 * t : ℝ) : ℂ)) * (q t * H t)‖
      = ‖Complex.exp (Complex.I * μ * ((1 - 2 * t : ℝ) : ℂ))‖ * ‖q t‖ * ‖H t‖ := by
        rw [norm_mul, norm_mul]; ring
    _ ≤ Real.exp a * Q * ‖H t‖ := by gcongr

theorem forcing_osc_expansion {N : ℕ} (hN : 1 ≤ N) (φ : NlsGge.ThirdConsultation.KSPS.SobolevC N)
    (b : Bool) (a : ℝ) (Λ : ℝ) (hΛ : 0 < Λ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (lam : ℂ), Λ ≤ ‖lam‖ → ∀ (μ : ℂ), |μ.im| ≤ a →
      ∀ (q : ℝ → ℂ) (Q : ℝ), ContinuousOn q (Icc (0 : ℝ) 1) → (∀ t ∈ Icc (0 : ℝ) 1, ‖q t‖ ≤ Q) →
      ‖endpointOsc μ (fun t => q t * NlsGge.ThirdConsultation.KSPSRiccati.forcing φ b lam t) -
        endpointOsc μ (fun t => q t * coverRep38
          (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b (N + 1)) t) -
        (2 * Complex.I * lam)⁻¹ * endpointOsc μ (fun t => q t *
          NlsGge.ThirdConsultation.KSPSRiccati.a1 φ b t)‖ ≤ Real.exp a * Q * K / ‖lam‖ ^ 2 := by
  obtain ⟨ε, C, hε, hC, h⟩ :=
    (NlsGge.ThirdConsultation.KSPS.WKB_residual_regularity N hN φ).2.2.2.2.2.2.2 Λ hΛ
  obtain ⟨hco, ha1, ha2⟩ := h φ (by simpa using hε)
  refine ⟨C / 4, by positivity, fun lam hlam μ hμ q Q hqc hq => ?_⟩
  have hl0 : lam ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hlam; linarith
  have hne : (2 * Complex.I * lam) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) hl0
  have hae := NlsGge.ThirdConsultation.KSPSSupport.h150_forcing_ae φ b lam hl0
  obtain ⟨hA1m, hA1⟩ := ha1 b
  obtain ⟨hA2m, hA2⟩ := ha2 b lam hlam
  have hcm := NlsGge.ThirdConsultation.KSPSSupport.coverRep38_memLp_Icc
    (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b (N + 1))
  -- integrability of the three pieces
  have hqm : ∀ H : ℝ → ℂ, MemLp H 2 NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure →
      IntervalIntegrable (fun t : ℝ => Complex.exp (Complex.I * μ * ((1 - 2 * t : ℝ) : ℂ)) *
        (q t * H t)) volume 0 1 := by
    intro H hHm
    have hi := intervalIntegrable_of_memLp hHm
    have hc : ContinuousOn (fun t : ℝ => Complex.exp (Complex.I * μ * ((1 - 2 * t : ℝ) : ℂ)) * q t)
        (uIcc (0 : ℝ) 1) := by
      rw [Set.uIcc_of_le zero_le_one]
      exact (Continuous.continuousOn (by fun_prop)).mul hqc
    have := hi.continuousOn_mul hc
    exact this.congr (fun t _ => by simp only [mul_assoc])
  -- the a.e. identity under the integral
  set k1 : ℂ := (2 * Complex.I * lam)⁻¹ with hk1
  set k2 : ℂ := ((2 * Complex.I * lam) ^ 2)⁻¹ with hk2
  have hcm' : MemLp (fun x => coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b (N + 1)) x) 2
      NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure := hcm
  have hA := hqm _ hcm'
  have hB := hqm _ hA1m
  have hC2 := hqm _ hA2m
  have hae' : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Icc (0 : ℝ) 1 →
      NlsGge.ThirdConsultation.KSPSRiccati.forcing φ b lam t =
        coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b (N + 1)) t +
        k1 * NlsGge.ThirdConsultation.KSPSRiccati.a1 φ b t +
        k2 * NlsGge.ThirdConsultation.KSPSRiccati.a2 φ b lam t := by
    have := hae
    unfold NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure at this
    exact (ae_restrict_iff' measurableSet_Icc).1 this
  have hq1 : endpointOsc μ (fun t => q t * NlsGge.ThirdConsultation.KSPSRiccati.forcing φ b lam t) =
      endpointOsc μ (fun t => q t * coverRep38
          (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b (N + 1)) t) +
      k1 * endpointOsc μ (fun t => q t * NlsGge.ThirdConsultation.KSPSRiccati.a1 φ b t) +
      k2 * endpointOsc μ (fun t => q t * NlsGge.ThirdConsultation.KSPSRiccati.a2 φ b lam t) := by
    unfold endpointOsc
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add hA (hB.const_mul k1),
      ← intervalIntegral.integral_add (hA.add (hB.const_mul k1)) (hC2.const_mul k2)]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hae'] with t ht htI
    rw [Set.uIoc_of_le zero_le_one] at htI
    rw [ht ⟨htI.1.le, htI.2⟩]
    ring
  have hQ0 : 0 ≤ Q := (norm_nonneg _).trans (hq 0 ⟨le_rfl, zero_le_one⟩)
  have hI2 : ∫ t in (0 : ℝ)..1, ‖NlsGge.ThirdConsultation.KSPSRiccati.a2 φ b lam t‖ ≤ C := by
    refine (integral_norm_le_eLpNorm hA2m).trans ?_
    exact ENNReal.toReal_le_of_le_ofReal hC.le hA2
  have hosc := norm_endpointOsc_mul_le hμ hq (H := NlsGge.ThirdConsultation.KSPSRiccati.a2 φ b lam)
    (intervalIntegrable_of_memLp hA2m).norm
  have hk2n : ‖k2‖ = 1 / (4 * ‖lam‖ ^ 2) := by
    rw [hk2, norm_inv, norm_pow]
    simp only [norm_mul, Complex.norm_ofNat, Complex.norm_I, one_mul]
    rw [one_div]; congr 1; ring
  have hlp : 0 < ‖lam‖ := lt_of_lt_of_le hΛ hlam
  have hsimp : ∀ A B C : ℂ, A + B + C - A - B = C := fun A B C => by ring
  rw [hq1, hsimp, norm_mul, hk2n]
  calc 1 / (4 * ‖lam‖ ^ 2) * ‖endpointOsc μ (fun t => q t *
        NlsGge.ThirdConsultation.KSPSRiccati.a2 φ b lam t)‖
      ≤ 1 / (4 * ‖lam‖ ^ 2) * (Real.exp a * Q * C) := by
        gcongr
        exact hosc.trans (by gcongr)
    _ = Real.exp a * Q * (C / 4) / ‖lam‖ ^ 2 := by field_simp

theorem a1_osc_bound {N : ℕ} (hN : 1 ≤ N) (φ : NlsGge.ThirdConsultation.KSPS.SobolevC N) (b : Bool)
    (a : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (μ : ℂ), |μ.im| ≤ a → ∀ (q : ℝ → ℂ) (Q : ℝ),
      (∀ t ∈ Icc (0 : ℝ) 1, ‖q t‖ ≤ Q) →
      ‖endpointOsc μ (fun t => q t * NlsGge.ThirdConsultation.KSPSRiccati.a1 φ b t)‖ ≤
        Real.exp a * Q * M := by
  obtain ⟨ε, C, hε, hC, h⟩ :=
    (NlsGge.ThirdConsultation.KSPS.WKB_residual_regularity N hN φ).2.2.2.2.2.2.2 1 one_pos
  obtain ⟨_, ha1, _⟩ := h φ (by simpa using hε)
  obtain ⟨hA1m, hA1⟩ := ha1 b
  refine ⟨C, hC.le, fun μ hμ q Q hq => ?_⟩
  have hI : ∫ t in (0 : ℝ)..1, ‖NlsGge.ThirdConsultation.KSPSRiccati.a1 φ b t‖ ≤ C := by
    refine (integral_norm_le_eLpNorm hA1m).trans ?_
    exact ENNReal.toReal_le_of_le_ofReal hC.le hA1
  have hQ0 : 0 ≤ Q := (norm_nonneg _).trans (hq 0 ⟨le_rfl, zero_le_one⟩)
  refine (norm_endpointOsc_mul_le hμ hq (intervalIntegrable_of_memLp hA1m).norm).trans ?_
  gcongr

end NlsGge.ThirdConsultation.KSPSWKB
