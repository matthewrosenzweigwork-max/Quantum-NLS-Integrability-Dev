import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS011Quant1
import NlsGge.ThirdConsultation.KSPS.KSPS011Quant3
import NlsGge.ThirdConsultation.KSPS.KSPS011Quant4
import NlsGge.ThirdConsultation.KSPS.KSPS011Quant5Core

/- KSPS011Q5 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/ThirdConsultation/KSPS/KSPS011Quant5.lean. Pro round-15 SUPPORT (never a packet). GLUE.
   endpoint_remainder_tail_U: the BALL-UNIFORM TAIL finite-sum bound of the KSPS-011 master sequence
     ∃ N0 C, ∀ φ (‖φ.1‖+‖φ.2‖ ≤ KB), ∀ φ' (sobolevNorm 1 φ' ≤ B, toPair φ' = toPotPair φ), ∀ ξ (|ξ_n - nπ| ≤ a/w_n),
       ∀ F ⊆ {|n| ≥ N0}, Σ_{n∈F} ‖w_n (remainder_n - leading_n)‖² ≤ C,
   from the uniform pointwise bound (KSPS011Q4) and the six finite-sum bounds:
     Σ (Kc/|n|)² ≤ Kc² Σ' 1/n²; KSPSQ1.osc_pert_coverRep_finite; KSPSQ3.coef_top_fourier_U; KSPSQ1.osc_sq_finite
     (for a1, coverRep c, q·coverRep c), with ‖c‖, ‖a1‖ ≤ Cr from KSPSQ2.residual_uniform and |q| ≤ Q.
   The tail restriction is necessary (low labels: forcing carries (2iλ)^{-k} at λ = ξ_n). No hypothesis added. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open NlsGge.Pilot NlsGge.GK38 NlsGge.ThirdConsultation.KSPS

namespace NlsGge.ThirdConsultation.KSPSWKB

theorem endpoint_remainder_tail_U {N : ℕ} (hN : 1 ≤ N) (KB B : ℝ) (hKB : 0 ≤ KB) (hB : 0 ≤ B)
    (b : Bool) (a : ℝ) (ha : 0 ≤ a) :
    ∃ (N0 : ℕ) (C : ℝ), 0 ≤ C ∧
    ∀ φ : SobolevC N, ‖φ.1‖ + ‖φ.2‖ ≤ KB →
    ∀ φ' : SobolevC 1, sobolevNorm 1 φ' ≤ B →
      NlsGge.ThirdConsultation.KSPSVolterra.toPair φ' = NlsGge.ThirdConsultation.KSPS.toPotPair φ →
    ∀ (xi : ℤ → ℂ), (∀ n : ℤ, ‖xi n - (n : ℂ) * Real.pi‖ ≤ a / indexWeight n) →
    ∀ F : Finset ℤ, (∀ n ∈ F, (N0 : ℤ) ≤ |n|) →
    ∑ n ∈ F, ‖(indexWeight n : ℂ) *
      ((if hz : xi n = 0 then 0 else
          sourceRemainderVector φ b ⟨xi n, hz⟩ 1 (if b then 0 else 1)) -
        (if b then -Complex.I else Complex.I) * (-1 : ℂ) ^ n *
          (if b then (-1 : ℂ) ^ (N + 1) else -1) *
          physicalFourier (iteratedDerivative N (if b then φ.1 else φ.2))
            ((if b then (-1 : ℤ) else 1) * n))‖ ^ 2 ≤ C := by
  obtain ⟨N0, Kc, Q, hKc, hQ0, hP⟩ := endpoint_remainder_pointwise_U hN KB B hKB hB b a ha
  obtain ⟨Cr, hCr, hR⟩ := NlsGge.ThirdConsultation.KSPSQ2.residual_uniform N hN KB hKB 1 one_pos
  obtain ⟨D3, hD3, hT3⟩ := NlsGge.ThirdConsultation.KSPSQ3.coef_top_fourier_U N hN KB hKB
  have hZs := realSqSummable_inv_abs
  unfold RealSqSummable at hZs
  set Z : ℝ := ∑' n : ℤ, (1 / |(n : ℝ)|) ^ 2 with hZdef
  have hZ0 : 0 ≤ Z := tsum_nonneg (fun n => sq_nonneg _)
  set E : ℝ := Real.exp (2 * a) with hEdef
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  refine ⟨N0, 6 * (Kc ^ 2 * Z + E * Cr ^ 2 + D3 ^ 2 + 2 * (E + 1) * Cr ^ 2 +
      Q ^ 2 * (2 * (E + 1) * Cr ^ 2) + 2 * (E + 1) * (Q ^ 2 * Cr ^ 2)), by positivity,
    fun φ hS φ' hφB hφ' xi hxi F hF => ?_⟩
  obtain ⟨hQ, hpt⟩ := hP φ hS φ' hφB hφ'
  have hσ : (if b then (-1 : ℤ) else 1) = 1 ∨ (if b then (-1 : ℤ) else 1) = -1 := by
    cases b <;> simp
  set σ : ℤ := if b then -1 else 1 with hσdef
  set c : PhysicalL2 := NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b (N + 1) with hcdef
  obtain ⟨hcoef, ha1, -⟩ := hR φ hS
  have hc : ‖c‖ ≤ Cr := by
    have h := (hcoef b (N + 1) (by omega) le_rfl).2
    rw [Nat.sub_self, Nat.cast_zero, NlsGge.ThirdConsultation.KSPSSupport.h161_norm_eq_psn0] at h
    exact h
  have hc2 : ‖c‖ ^ 2 ≤ Cr ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hc 2
  have hcI : ∫ t in (0 : ℝ)..1, ‖coverRep38 c t‖ ^ 2 = ‖c‖ ^ 2 := integral_sq_coverRep38_one c
  obtain ⟨ha1m, ha1n⟩ := ha1 b
  have ha1I : ∫ t in (0 : ℝ)..1, ‖NlsGge.ThirdConsultation.KSPSRiccati.a1 φ b t‖ ^ 2 ≤ Cr ^ 2 := by
    rw [integral_sq_eq_eLpNorm ha1m]
    exact pow_le_pow_left₀ ENNReal.toReal_nonneg (ENNReal.toReal_le_of_le_ofReal hCr.le ha1n) 2
  set q : ℝ → ℂ := fun t => NlsGge.ThirdConsultation.KSPSVolterra.integratedQuadratic φ' t 0 0 with hqdef
  have hqc : ContinuousOn q (Icc (0 : ℝ) 1) := by
    simp only [hqdef, integratedQuadratic_apply00]
    exact NlsGge.ThirdConsultation.KSPSSupport.h150_prim_continuousOn
      (NlsGge.ThirdConsultation.KSPSVolterra.toPair φ').1 (NlsGge.ThirdConsultation.KSPSVolterra.toPair φ').2
  have hcm := NlsGge.ThirdConsultation.KSPSSupport.coverRep38_memLp_Icc c
  have hqcm : MemLp (fun t => q t * coverRep38 c t) 2 NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure :=
    NlsGge.ThirdConsultation.KSPSSupport.h150_memLp_mul_bdd _ _ hcm hqc
  have hqI : ∫ t in (0 : ℝ)..1, ‖q t * coverRep38 c t‖ ^ 2 ≤ Q ^ 2 * Cr ^ 2 := by
    have hi1 := intervalIntegrable_sq_of_memLp hqcm
    have hi2 := (intervalIntegrable_coverRep38_sq_one c).const_mul (Q ^ 2)
    have hmono : ∫ t in (0 : ℝ)..1, ‖q t * coverRep38 c t‖ ^ 2 ≤
        ∫ t in (0 : ℝ)..1, Q ^ 2 * ‖coverRep38 c t‖ ^ 2 := by
      refine intervalIntegral.integral_mono_on zero_le_one hi1 hi2 (fun t ht => ?_)
      rw [norm_mul, mul_pow]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hQ t ht) 2) (sq_nonneg _)
    rw [intervalIntegral.integral_const_mul, hcI] at hmono
    exact hmono.trans (mul_le_mul_of_nonneg_left hc2 (sq_nonneg _))
  -- the six finite sums
  have s1 : ∑ n ∈ F, (Kc * (1 / |(n : ℝ)|)) ^ 2 ≤ Kc ^ 2 * Z := by
    simp_rw [mul_pow]
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left
      (NlsGge.ThirdConsultation.KSPSQ5C.sum_le_tsum_of_nonneg (fun n => sq_nonneg _) hZs F) (sq_nonneg _)
  have s2 : ∑ n ∈ F, (indexWeight n * ‖endpointOsc ((σ : ℂ) * xi n) (coverRep38 c) -
      (-1 : ℂ) ^ n * physicalFourier c (σ * n)‖) ^ 2 ≤ E * Cr ^ 2 := by
    have h := NlsGge.ThirdConsultation.KSPSQ1.osc_pert_coverRep_finite c a ha xi hxi σ hσ F
    rw [hcI] at h
    simp_rw [mul_pow]
    exact h.trans (mul_le_mul_of_nonneg_left hc2 hE0)
  have s3 : ∑ n ∈ F, (indexWeight n * ‖physicalFourier c (σ * n) -
      (if b then (-1 : ℂ) ^ (N + 1) else -1) *
        physicalFourier (iteratedDerivative N (if b then φ.1 else φ.2)) (σ * n)‖) ^ 2 ≤ D3 ^ 2 := by
    simp_rw [mul_pow]
    exact hT3 φ hS b σ hσ F
  have s4 : ∑ n ∈ F, ‖endpointOsc ((σ : ℂ) * xi n) (NlsGge.ThirdConsultation.KSPSRiccati.a1 φ b)‖ ^ 2 ≤
      2 * (E + 1) * Cr ^ 2 :=
    (NlsGge.ThirdConsultation.KSPSQ1.osc_sq_finite ha1m a ha xi hxi σ hσ F).trans
      (mul_le_mul_of_nonneg_left ha1I (by positivity))
  have s5 : ∑ n ∈ F, (Q * ‖endpointOsc ((σ : ℂ) * xi n) (coverRep38 c)‖) ^ 2 ≤
      Q ^ 2 * (2 * (E + 1) * Cr ^ 2) := by
    simp_rw [mul_pow]
    rw [← Finset.mul_sum]
    have h := NlsGge.ThirdConsultation.KSPSQ1.osc_sq_finite hcm a ha xi hxi σ hσ F
    rw [hcI] at h
    exact mul_le_mul_of_nonneg_left (h.trans (mul_le_mul_of_nonneg_left hc2 (by positivity))) (sq_nonneg _)
  have s6 : ∑ n ∈ F, ‖endpointOsc ((σ : ℂ) * xi n) (fun t => q t * coverRep38 c t)‖ ^ 2 ≤
      2 * (E + 1) * (Q ^ 2 * Cr ^ 2) :=
    (NlsGge.ThirdConsultation.KSPSQ1.osc_sq_finite hqcm a ha xi hxi σ hσ F).trans
      (mul_le_mul_of_nonneg_left hqI (by positivity))
  refine NlsGge.ThirdConsultation.KSPSQ5C.sum_sq_le_six F _ _ _ _ _ _ _ (fun n hn => ⟨norm_nonneg _,
    hpt xi hxi n (hF n hn)⟩) _ _ _ _ _ _ s1 s2 s3 s4 s5 s6

end NlsGge.ThirdConsultation.KSPSWKB
