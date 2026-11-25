import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS011Support10
import NlsGge.ThirdConsultation.KSPSSupport.A2BND01

                                                                                 
                                                                                                  
                                                                           
                                                                             
                                                           
                                                                                                                      
                                                                                                                         
                                                                                                         
                                                                                                              
                                                                             
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.ThirdConsultation.KSPSQ2
open NlsGge.ThirdConsultation.KSPSWKB

theorem residual_uniform (N : ℕ) (hN : 1 ≤ N) (K : ℝ) (hK : 0 ≤ K) (Λ : ℝ) (hΛ : 0 < Λ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ψ : NlsGge.ThirdConsultation.KSPS.SobolevC N, ‖ψ.1‖ + ‖ψ.2‖ ≤ K →
      (∀ (b : Bool) (k : ℕ), 1 ≤ k → k ≤ N + 1 →
        NlsGge.GKDefinitionDesign.physicalSobolev ((N + 1 - k : ℕ) : ℝ)
            (NlsGge.ThirdConsultation.KSPSRiccati.coefficient ψ b k) ∧
          NlsGge.GKDefinitionDesign.physicalSobolevNorm ((N + 1 - k : ℕ) : ℝ)
            (NlsGge.ThirdConsultation.KSPSRiccati.coefficient ψ b k) ≤ C) ∧
      (∀ b : Bool,
        MemLp (NlsGge.ThirdConsultation.KSPSRiccati.a1 ψ b) 2
            NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure ∧
          eLpNorm (NlsGge.ThirdConsultation.KSPSRiccati.a1 ψ b) 2
            NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure ≤ ENNReal.ofReal C) ∧
      (∀ (b : Bool) (lam : ℂ), Λ ≤ ‖lam‖ →
        MemLp (NlsGge.ThirdConsultation.KSPSRiccati.a2 ψ b lam) 2
            NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure ∧
          eLpNorm (NlsGge.ThirdConsultation.KSPSRiccati.a2 ψ b lam) 2
            NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure ≤ ENNReal.ofReal C) := by
  obtain ⟨Du, hDu, hU⟩ := NlsGge.ThirdConsultation.KSPSSupport.h161_coef_uniform N hN K hK
  obtain ⟨Ca1, hCa1, hA1⟩ := NlsGge.ThirdConsultation.KSPSSupport.h161_a1_uniform N hN K hK
  obtain ⟨Ca2, hCa2, hA2⟩ := NlsGge.ThirdConsultation.KSPSSupport.h161_a2_uniform N hN K hK Λ hΛ
  refine ⟨Du + Ca1 + Ca2 + 1, by linarith, fun ψ hS => ⟨fun b k hk1 hk2 => ?_, fun b => ?_,
    fun b lam hlam => ?_⟩⟩
  · obtain ⟨hm, hn⟩ := hU ψ hS b k hk1 hk2
    exact ⟨hm, hn.trans (by linarith)⟩
  · obtain ⟨hm, hn⟩ := hA1 ψ hS b
    exact ⟨hm, hn.trans (ENNReal.ofReal_le_ofReal (by linarith))⟩
  · obtain ⟨hm, hn⟩ := hA2 ψ hS b lam hlam
    exact ⟨hm, hn.trans (ENNReal.ofReal_le_ofReal (by linarith))⟩

theorem forcing_eLpNorm_U {N : ℕ} (hN : 1 ≤ N) (K : ℝ) (hK : 0 ≤ K)
    (Λ : ℝ) (hΛ : 0 < Λ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ φ : NlsGge.ThirdConsultation.KSPS.SobolevC N, ‖φ.1‖ + ‖φ.2‖ ≤ K → ∀ (b : Bool) (lam : ℂ), Λ ≤ ‖lam‖ →
      eLpNorm (NlsGge.ThirdConsultation.KSPSRiccati.forcing φ b lam) 2
        NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure ≤ ENNReal.ofReal M := by
  obtain ⟨C, hC, h⟩ := residual_uniform N hN K hK Λ hΛ
  refine ⟨C + C / (2 * Λ) + C / (4 * Λ ^ 2), by positivity, fun φ hφ b lam hlam => ?_⟩
  obtain ⟨hco, ha1, ha2⟩ := h φ hφ
  have hl0 : lam ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hlam; linarith
  have hae := NlsGge.ThirdConsultation.KSPSSupport.h150_forcing_ae φ b lam hl0
  obtain ⟨hA1m, hA1⟩ := ha1 b
  obtain ⟨hA2m, hA2⟩ := ha2 b lam hlam
  have hcm := NlsGge.ThirdConsultation.KSPSSupport.coverRep38_memLp_Icc
    (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b (N + 1))
  have hc : eLpNorm (fun x => coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b (N + 1)) x) 2
      NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure ≤ ENNReal.ofReal C := by
    show eLpNorm (coverRep38 _) 2 _ ≤ _
    rw [eLpNorm_coverRep38_eq]
    refine ENNReal.ofReal_le_ofReal ?_
    have := (hco b (N + 1) (by omega) le_rfl).2
    rw [Nat.sub_self, Nat.cast_zero, NlsGge.ThirdConsultation.KSPSSupport.h161_norm_eq_psn0] at this
    exact this
  have hn1 : ‖(2 * Complex.I * lam)⁻¹‖ ≤ (2 * Λ)⁻¹ := by
    rw [norm_inv]
    simp only [norm_mul, Complex.norm_ofNat, Complex.norm_I, one_mul]
    exact inv_anti₀ (by positivity) (by linarith)
  have hn2 : ‖((2 * Complex.I * lam) ^ 2)⁻¹‖ ≤ (4 * Λ ^ 2)⁻¹ := by
    rw [norm_inv, norm_pow]
    simp only [norm_mul, Complex.norm_ofNat, Complex.norm_I, one_mul]
    refine inv_anti₀ (by positivity) ?_
    nlinarith
  have m1 : MemLp (fun x => (2 * Complex.I * lam)⁻¹ * NlsGge.ThirdConsultation.KSPSRiccati.a1 φ b x) 2
      NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure := by
    exact hA1m.const_mul _
  have m2 : MemLp (fun x => ((2 * Complex.I * lam) ^ 2)⁻¹ * NlsGge.ThirdConsultation.KSPSRiccati.a2 φ b lam x) 2
      NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure := by
    exact hA2m.const_mul _
  rw [eLpNorm_congr_ae hae]
  calc _ ≤ eLpNorm (fun x => coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b (N + 1)) x +
          (2 * Complex.I * lam)⁻¹ * NlsGge.ThirdConsultation.KSPSRiccati.a1 φ b x) 2
          NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure +
        eLpNorm (fun x => ((2 * Complex.I * lam) ^ 2)⁻¹ *
          NlsGge.ThirdConsultation.KSPSRiccati.a2 φ b lam x) 2
          NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure := by
        exact eLpNorm_add_le (by norm_num)
    _ ≤ (eLpNorm (fun x => coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b (N + 1)) x) 2
          NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure +
        eLpNorm (fun x => (2 * Complex.I * lam)⁻¹ * NlsGge.ThirdConsultation.KSPSRiccati.a1 φ b x) 2
          NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure) +
        eLpNorm (fun x => ((2 * Complex.I * lam) ^ 2)⁻¹ *
          NlsGge.ThirdConsultation.KSPSRiccati.a2 φ b lam x) 2
          NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure := by
        gcongr
        exact eLpNorm_add_le (by norm_num)
    _ ≤ (ENNReal.ofReal C + ENNReal.ofReal ((2 * Λ)⁻¹) * ENNReal.ofReal C) +
        ENNReal.ofReal ((4 * Λ ^ 2)⁻¹) * ENNReal.ofReal C := by
        rw [eLpNorm_const_mul_le, eLpNorm_const_mul_le]
        exact add_le_add (add_le_add hc (mul_le_mul' (ENNReal.ofReal_le_ofReal hn1) hA1))
          (mul_le_mul' (ENNReal.ofReal_le_ofReal hn2) hA2)
    _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add hC.le (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        field_simp

theorem sourceForcing_vectorL2Norm_U {N : ℕ} (hN : 1 ≤ N) (KB : ℝ) (hKB : 0 ≤ KB)
    (Λ a : ℝ) (hΛ : 0 < Λ) (ha : 0 ≤ a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ φ : NlsGge.ThirdConsultation.KSPS.SobolevC N, ‖φ.1‖ + ‖φ.2‖ ≤ KB → ∀ (b : Bool) (lam : {z : ℂ // z ≠ 0}), Λ ≤ ‖lam.1‖ → |lam.1.im| ≤ a →
      ∀ f : PotPair,
        (∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)),
          ![potRepFst38 f t, potRepSnd38 f t] = sourceForcingVector φ b lam t) →
        NlsGge.ThirdConsultation.KSPSVolterra.vectorL2Norm f ≤ K := by
  obtain ⟨M, hM0, hM⟩ := forcing_eLpNorm_U hN KB hKB Λ hΛ
  refine ⟨2 * Real.exp a * M, by positivity, fun φ hφ b lam hlam hIm f hf => ?_⟩
  have hfm := NlsGge.ThirdConsultation.KSPSSupport.h150_forcing_memLp φ b lam.1
  have hMb : (eLpNorm (NlsGge.ThirdConsultation.KSPSRiccati.forcing φ b lam.1) 2
      NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure).toReal ≤ M :=
    ENNReal.toReal_le_of_le_ofReal hM0 (hM φ hφ b lam.1 hlam)
  have hcomp : ∀ (u : PhysicalL2) (i : Fin 2),
      (∀ t, coverRep38 u t = ![potRepFst38 f t, potRepSnd38 f t] i) → ‖u‖ ≤ Real.exp a * M := by
    intro u i hu
    refine (norm_le_of_ae_le (Real.exp_pos a).le hfm ?_).trans
      (mul_le_mul_of_nonneg_left hMb (Real.exp_pos a).le)
    have hae : ∀ᵐ t ∂NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure,
        ![potRepFst38 f t, potRepSnd38 f t] = sourceForcingVector φ b lam t := hf
    have hmem : ∀ᵐ t ∂NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure, t ∈ Icc (0 : ℝ) 1 :=
      ae_restrict_mem measurableSet_Icc
    filter_upwards [hae, hmem] with t ht1 ht2
    rw [hu t, ht1]
    exact sourceForcingVector_component_norm_le φ b lam a hIm i t ht2
  have h1 : ‖f.1‖ ≤ Real.exp a * M := hcomp f.1 0 (fun t => rfl)
  have h2 : ‖f.2‖ ≤ Real.exp a * M := hcomp f.2 1 (fun t => rfl)
  unfold NlsGge.ThirdConsultation.KSPSVolterra.vectorL2Norm
  calc Real.sqrt (‖f.1‖ ^ 2 + ‖f.2‖ ^ 2) ≤ Real.sqrt ((‖f.1‖ + ‖f.2‖) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [norm_nonneg f.1, norm_nonneg f.2])
    _ = ‖f.1‖ + ‖f.2‖ := Real.sqrt_sq (by positivity)
    _ ≤ 2 * Real.exp a * M := by linarith

theorem forcing_osc_U {N : ℕ} (hN : 1 ≤ N) (KB : ℝ) (hKB : 0 ≤ KB)
    (b : Bool) (a : ℝ) (Λ : ℝ) (hΛ : 0 < Λ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ φ : NlsGge.ThirdConsultation.KSPS.SobolevC N, ‖φ.1‖ + ‖φ.2‖ ≤ KB → ∀ (lam : ℂ), Λ ≤ ‖lam‖ → ∀ (μ : ℂ), |μ.im| ≤ a →
      ∀ (q : ℝ → ℂ) (Q : ℝ), ContinuousOn q (Icc (0 : ℝ) 1) → (∀ t ∈ Icc (0 : ℝ) 1, ‖q t‖ ≤ Q) →
      ‖endpointOsc μ (fun t => q t * NlsGge.ThirdConsultation.KSPSRiccati.forcing φ b lam t) -
        endpointOsc μ (fun t => q t * coverRep38
          (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b (N + 1)) t) -
        (2 * Complex.I * lam)⁻¹ * endpointOsc μ (fun t => q t *
          NlsGge.ThirdConsultation.KSPSRiccati.a1 φ b t)‖ ≤ Real.exp a * Q * K / ‖lam‖ ^ 2 := by
  obtain ⟨C, hC, h⟩ := residual_uniform N hN KB hKB Λ hΛ
  refine ⟨C / 4, by positivity, fun φ hφ lam hlam μ hμ q Q hqc hq => ?_⟩
  obtain ⟨hco, ha1, ha2⟩ := h φ hφ
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

theorem a1_osc_U {N : ℕ} (hN : 1 ≤ N) (KB : ℝ) (hKB : 0 ≤ KB) (b : Bool)
    (a : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ φ : NlsGge.ThirdConsultation.KSPS.SobolevC N, ‖φ.1‖ + ‖φ.2‖ ≤ KB → ∀ (μ : ℂ), |μ.im| ≤ a → ∀ (q : ℝ → ℂ) (Q : ℝ),
      (∀ t ∈ Icc (0 : ℝ) 1, ‖q t‖ ≤ Q) →
      ‖endpointOsc μ (fun t => q t * NlsGge.ThirdConsultation.KSPSRiccati.a1 φ b t)‖ ≤
        Real.exp a * Q * M := by
  obtain ⟨C, hC, h⟩ := residual_uniform N hN KB hKB 1 one_pos
  refine ⟨C, hC.le, fun φ hφ μ hμ q Q hq => ?_⟩
  obtain ⟨_, ha1, _⟩ := h φ hφ
  obtain ⟨hA1m, hA1⟩ := ha1 b
  have hI : ∫ t in (0 : ℝ)..1, ‖NlsGge.ThirdConsultation.KSPSRiccati.a1 φ b t‖ ≤ C := by
    refine (integral_norm_le_eLpNorm hA1m).trans ?_
    exact ENNReal.toReal_le_of_le_ofReal hC.le hA1
  have hQ0 : 0 ≤ Q := (norm_nonneg _).trans (hq 0 ⟨le_rfl, zero_le_one⟩)
  refine (norm_endpointOsc_mul_le hμ hq (intervalIntegrable_of_memLp hA1m).norm).trans ?_
  gcongr

end NlsGge.ThirdConsultation.KSPSQ2
