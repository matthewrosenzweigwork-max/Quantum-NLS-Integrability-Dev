import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS011Support9
import NlsGge.ThirdConsultation.KSPS.KSPS011Support11

/- KSPS011Q1 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/ThirdConsultation/KSPS/KSPS011Quant1.lean. Pro round-15 SUPPORT (never a packet).
   Quantitative (finite-sum, explicit-constant) companions of the KSPS-011 oscillatory l2 facts
   (KSPS011Support9.endpointOsc_bessel / endpointOsc_pert_summable / endpointOsc_sq_summable and
   KSPS011Support11.osc_pert_seq / osc_sq_seq), which export Summable only. Constants come from the landed explicit
   tsum bounds Perturbed008Support.bco_sq_summable_le (Bessel, constant 1) and pert_weighted (constant exp(2a)):
     ∀ F, Σ_{n∈F} ‖osc(nπ) H‖²                         ≤ I(H)
     ∀ F, Σ_{n∈F} w_n² ‖osc(nπ+β_n) H - osc(nπ) H‖²     ≤ exp(2a) I(H)
     ∀ F, Σ_{n∈F} ‖osc(σ ξ_n) H‖²                       ≤ 2 (exp(2a) + 1) I(H)
     ∀ F, Σ_{n∈F} w_n² ‖osc(σ ξ_n) ū - (-1)^n û(σn)‖²   ≤ exp(2a) I(ū)      (ū = coverRep38 u)
   with I(H) = ∫₀¹ ‖H‖², |β_n| ≤ a / w_n, |ξ_n - nπ| ≤ a / w_n, σ = ±1. Constants depend only on a. No hypothesis added. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.ThirdConsultation.KSPSQ1
open NlsGge.ThirdConsultation.KSPSWKB

theorem sum_le_of_summable_tsum_le {f : ℤ → ℝ} (h0 : ∀ n, 0 ≤ f n) (hs : Summable f) {M : ℝ}
    (hM : ∑' n, f n ≤ M) (F : Finset ℤ) : ∑ n ∈ F, f n ≤ M :=
  (hs.sum_le_tsum F (fun n _ => h0 n)).trans hM

theorem integral_hat_sq {H : ℝ → ℂ} :
    ∫ t in (0 : ℝ)..1, ‖(Set.Icc (0 : ℝ) 1).indicator H t‖ ^ 2 = ∫ t in (0 : ℝ)..1, ‖H t‖ ^ 2 := by
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  rw [Set.uIcc_of_le zero_le_one] at ht
  simp [Set.indicator_of_mem ht]

theorem osc_bessel_finite {H : ℝ → ℂ}
    (hH : MemLp H 2 NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure) (F : Finset ℤ) :
    ∑ n ∈ F, ‖endpointOsc ((n : ℂ) * (Real.pi : ℂ)) H‖ ^ 2 ≤ ∫ t in (0 : ℝ)..1, ‖H t‖ ^ 2 := by
  have h := NlsGge.ThirdConsultation.KSPS008Support.bco_sq_summable_le
    ((Set.Icc (0 : ℝ) 1).indicator H) (memLp_hat hH).aestronglyMeasurable
    (intervalIntegrable_hat_sq hH) (x := 1) zero_le_one le_rfl 0
  have e : ∀ n : ℤ, ‖NlsGge.ThirdConsultation.KSPS008Support.bco ((Set.Icc (0 : ℝ) 1).indicator H) 1 0 n‖ ^ 2 =
      ‖endpointOsc ((n : ℂ) * (Real.pi : ℂ)) H‖ ^ 2 := by
    intro n
    rw [endpointOsc_hat]
    unfold NlsGge.ThirdConsultation.KSPS008Support.bco
    simp only [pow_zero, one_mul]
  simp_rw [e] at h
  rw [← integral_hat_sq]
  exact sum_le_of_summable_tsum_le (fun n => by positivity) h.1 h.2 F

theorem osc_pert_finite {H : ℝ → ℂ}
    (hH : MemLp H 2 NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure)
    (a : ℝ) (ha : 0 ≤ a) (β : ℤ → ℂ)
    (hβ : ∀ n : ℤ, ‖β n‖ ≤ a / NlsGge.ThirdConsultation.KSPS.indexWeight n) (F : Finset ℤ) :
    ∑ n ∈ F, NlsGge.ThirdConsultation.KSPS.indexWeight n ^ 2 *
      ‖endpointOsc ((n : ℂ) * (Real.pi : ℂ) + β n) H - endpointOsc ((n : ℂ) * (Real.pi : ℂ)) H‖ ^ 2 ≤
      Real.exp (2 * a) * ∫ t in (0 : ℝ)..1, ‖H t‖ ^ 2 := by
  have hw : ∀ n : ℤ, 1 ≤ NlsGge.ThirdConsultation.KSPS.indexWeight n :=
    NlsGge.ThirdConsultation.KSPS.one_le_indexWeight
  have hwpos : ∀ n : ℤ, 0 < NlsGge.ThirdConsultation.KSPS.indexWeight n :=
    NlsGge.ThirdConsultation.KSPS.indexWeight_pos
  have h := NlsGge.ThirdConsultation.KSPS008Support.pert_weighted
    ((Set.Icc (0 : ℝ) 1).indicator H) (memLp_hat hH).aestronglyMeasurable
    (intervalIntegrable_hat hH) (intervalIntegrable_hat_sq hH) (x := 1) zero_le_one le_rfl ha
    NlsGge.ThirdConsultation.KSPS.indexWeight hw β
    (fun n => (le_div_iff₀ (hwpos n)).mp (hβ n))
  have e : ∀ n : ℤ, NlsGge.ThirdConsultation.KSPS.indexWeight n ^ 2 * ‖∫ t in (0 : ℝ)..1,
        (Complex.exp (Complex.I * ((n : ℂ) * (Real.pi : ℂ) + β n) * ((1 - 2 * t : ℝ) : ℂ)) -
          Complex.exp (Complex.I * (n : ℂ) * (Real.pi : ℂ) * ((1 - 2 * t : ℝ) : ℂ))) *
            (Set.Icc (0 : ℝ) 1).indicator H t‖ ^ 2 =
      NlsGge.ThirdConsultation.KSPS.indexWeight n ^ 2 *
      ‖endpointOsc ((n : ℂ) * (Real.pi : ℂ) + β n) H - endpointOsc ((n : ℂ) * (Real.pi : ℂ)) H‖ ^ 2 := by
    intro n
    congr 3
    rw [endpointOsc_hat, endpointOsc_hat, ← intervalIntegral.integral_sub
      (intervalIntegrable_osc_integrand _ hH) (intervalIntegrable_osc_integrand _ hH)]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    try simp only
    rw [← sub_mul]
    congr 3
    ring
  simp_rw [e] at h
  rw [← integral_hat_sq]
  exact sum_le_of_summable_tsum_le (fun n => by positivity) h.1 h.2 F

theorem integral_sq_nonneg (H : ℝ → ℂ) : 0 ≤ ∫ t in (0 : ℝ)..1, ‖H t‖ ^ 2 :=
  intervalIntegral.integral_nonneg (by norm_num) (fun t _ => by positivity)

theorem osc_sq_finite_one {H : ℝ → ℂ}
    (hH : MemLp H 2 NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure)
    (a : ℝ) (ha : 0 ≤ a) (β : ℤ → ℂ)
    (hβ : ∀ n : ℤ, ‖β n‖ ≤ a / NlsGge.ThirdConsultation.KSPS.indexWeight n) (F : Finset ℤ) :
    ∑ n ∈ F, ‖endpointOsc ((n : ℂ) * (Real.pi : ℂ) + β n) H‖ ^ 2 ≤
      2 * (Real.exp (2 * a) + 1) * ∫ t in (0 : ℝ)..1, ‖H t‖ ^ 2 := by
  have h1 := osc_bessel_finite hH F
  have h2 := osc_pert_finite hH a ha β hβ F
  have hle : ∀ n ∈ F, ‖endpointOsc ((n : ℂ) * (Real.pi : ℂ) + β n) H‖ ^ 2 ≤
      2 * (NlsGge.ThirdConsultation.KSPS.indexWeight n ^ 2 *
        ‖endpointOsc ((n : ℂ) * (Real.pi : ℂ) + β n) H - endpointOsc ((n : ℂ) * (Real.pi : ℂ)) H‖ ^ 2) +
      2 * ‖endpointOsc ((n : ℂ) * (Real.pi : ℂ)) H‖ ^ 2 := by
    intro n _
    have hw := NlsGge.ThirdConsultation.KSPS.one_le_indexWeight n
    set A := endpointOsc ((n : ℂ) * (Real.pi : ℂ) + β n) H
    set B := endpointOsc ((n : ℂ) * (Real.pi : ℂ)) H
    have h3 : ‖A‖ ≤ ‖A - B‖ + ‖B‖ := by
      have := norm_add_le (A - B) B
      simpa using this
    have h4 : ‖A‖ ^ 2 ≤ 2 * ‖A - B‖ ^ 2 + 2 * ‖B‖ ^ 2 := by
      nlinarith [sq_nonneg (‖A - B‖ - ‖B‖), norm_nonneg A, norm_nonneg (A - B), norm_nonneg B]
    have h5 : ‖A - B‖ ^ 2 ≤ NlsGge.ThirdConsultation.KSPS.indexWeight n ^ 2 * ‖A - B‖ ^ 2 := by
      have : (1 : ℝ) ≤ NlsGge.ThirdConsultation.KSPS.indexWeight n ^ 2 := by nlinarith
      nlinarith [sq_nonneg ‖A - B‖]
    linarith
  refine (Finset.sum_le_sum hle).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hI := integral_sq_nonneg H
  nlinarith

/-- the reflected parameter used for σ = -1 -/
theorem refl_beta_bound (a : ℝ) (xi : ℤ → ℂ)
    (hxi : ∀ n : ℤ, ‖xi n - (n : ℂ) * Real.pi‖ ≤ a / NlsGge.ThirdConsultation.KSPS.indexWeight n) :
    ∀ m : ℤ, ‖-(xi (-m) - ((-m : ℤ) : ℂ) * Real.pi)‖ ≤ a / NlsGge.ThirdConsultation.KSPS.indexWeight m := by
  intro m
  rw [norm_neg]
  have := hxi (-m)
  rwa [indexWeight_neg011] at this

theorem sum_neg_reindex (F : Finset ℤ) (f : ℤ → ℝ) :
    ∑ n ∈ F, f n = ∑ m ∈ F.image (fun n => -n), f (-m) := by
  rw [Finset.sum_image (fun x _ y _ h => neg_injective h)]
  simp

theorem osc_sq_finite {H : ℝ → ℂ}
    (hH : MemLp H 2 NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure)
    (a : ℝ) (ha : 0 ≤ a) (xi : ℤ → ℂ)
    (hxi : ∀ n : ℤ, ‖xi n - (n : ℂ) * Real.pi‖ ≤ a / NlsGge.ThirdConsultation.KSPS.indexWeight n)
    (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) (F : Finset ℤ) :
    ∑ n ∈ F, ‖endpointOsc ((σ : ℂ) * xi n) H‖ ^ 2 ≤
      2 * (Real.exp (2 * a) + 1) * ∫ t in (0 : ℝ)..1, ‖H t‖ ^ 2 := by
  rcases hσ with rfl | rfl
  · have h := osc_sq_finite_one hH a ha (fun n => xi n - (n : ℂ) * Real.pi) hxi F
    refine le_trans (le_of_eq ?_) h
    refine Finset.sum_congr rfl (fun n _ => ?_)
    simp only [add_sub_cancel, Int.cast_one, one_mul]
  · have h := osc_sq_finite_one hH a ha (fun m => -(xi (-m) - ((-m : ℤ) : ℂ) * Real.pi))
      (refl_beta_bound a xi hxi) (F.image (fun n => -n))
    refine le_trans (le_of_eq ?_) h
    rw [sum_neg_reindex]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    beta_reduce
    have e : ((m : ℤ) : ℂ) * (Real.pi : ℂ) + -(xi (-m) - (((-m) : ℤ) : ℂ) * Real.pi) =
        ((-1 : ℤ) : ℂ) * xi (-m) := by push_cast; ring
    rw [e]

theorem osc_pert_coverRep_finite (u : PhysicalL2) (a : ℝ) (ha : 0 ≤ a) (xi : ℤ → ℂ)
    (hxi : ∀ n : ℤ, ‖xi n - (n : ℂ) * Real.pi‖ ≤ a / NlsGge.ThirdConsultation.KSPS.indexWeight n)
    (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) (F : Finset ℤ) :
    ∑ n ∈ F, NlsGge.ThirdConsultation.KSPS.indexWeight n ^ 2 *
      ‖endpointOsc ((σ : ℂ) * xi n) (coverRep38 u) - (-1 : ℂ) ^ n * physicalFourier u (σ * n)‖ ^ 2 ≤
      Real.exp (2 * a) * ∫ t in (0 : ℝ)..1, ‖coverRep38 u t‖ ^ 2 := by
  have hH := NlsGge.ThirdConsultation.KSPSSupport.coverRep38_memLp_Icc u
  rcases hσ with rfl | rfl
  · have h := osc_pert_finite hH a ha (fun n => xi n - (n : ℂ) * Real.pi) hxi F
    refine le_trans (le_of_eq ?_) h
    refine Finset.sum_congr rfl (fun n _ => ?_)
    simp only [add_sub_cancel, endpointOsc_natPi_coverRep, Int.cast_one, one_mul]
  · have h := osc_pert_finite hH a ha (fun m => -(xi (-m) - ((-m : ℤ) : ℂ) * Real.pi))
      (refl_beta_bound a xi hxi) (F.image (fun n => -n))
    refine le_trans (le_of_eq ?_) h
    rw [sum_neg_reindex]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    beta_reduce
    have e : ((m : ℤ) : ℂ) * (Real.pi : ℂ) + -(xi (-m) - (((-m) : ℤ) : ℂ) * Real.pi) =
        ((-1 : ℤ) : ℂ) * xi (-m) := by push_cast; ring
    have e2 : (-1 : ℤ) * -m = m := by ring
    rw [e, endpointOsc_natPi_coverRep, indexWeight_neg011, neg_one_zpow_neg, e2]

end NlsGge.ThirdConsultation.KSPSQ1
