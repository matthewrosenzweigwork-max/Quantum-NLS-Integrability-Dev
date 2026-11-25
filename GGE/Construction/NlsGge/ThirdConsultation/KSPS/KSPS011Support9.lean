import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS011Host
import NlsGge.ThirdConsultation.KSPS.KSPS011Support1
import NlsGge.ThirdConsultation.KSPS.Perturbed008Support
import NlsGge.ThirdConsultation.KSPSSupport.ANA01

                                                                                                                                                                   
                                                                                                    
                                                                                                            
                                                                                                               
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.ThirdConsultation.KSPSWKB

def endpointOsc (μ : ℂ) (H : ℝ → ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1, Complex.exp (Complex.I * μ * ((1 - 2 * t : ℝ) : ℂ)) * H t

theorem isFiniteMeasure_intervalMeasure :
    IsFiniteMeasure NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure := by
  unfold NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure
  infer_instance

theorem memLp_hat {H : ℝ → ℂ} (hH : MemLp H 2 NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure) :
    MemLp ((Set.Icc (0 : ℝ) 1).indicator H) 2 volume := by
  rw [memLp_indicator_iff_restrict measurableSet_Icc]
  exact hH

theorem intervalIntegrable_hat {H : ℝ → ℂ}
    (hH : MemLp H 2 NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure) :
    IntervalIntegrable ((Set.Icc (0 : ℝ) 1).indicator H) volume 0 1 := by
  haveI := isFiniteMeasure_intervalMeasure
  have h1 : Integrable H NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure :=
    hH.integrable (by norm_num)
  have h2 : Integrable ((Set.Icc (0 : ℝ) 1).indicator H) volume := by
    rw [integrable_indicator_iff measurableSet_Icc]
    exact h1
  exact h2.intervalIntegrable

theorem intervalIntegrable_hat_sq {H : ℝ → ℂ}
    (hH : MemLp H 2 NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure) :
    IntervalIntegrable (fun t => ‖(Set.Icc (0 : ℝ) 1).indicator H t‖ ^ 2) volume 0 1 := by
  have h := memLp_hat hH
  exact ((memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).mp h).intervalIntegrable

theorem endpointOsc_hat (μ : ℂ) (H : ℝ → ℂ) :
    endpointOsc μ H = ∫ t in (0 : ℝ)..1, Complex.exp (Complex.I * μ * ((1 - 2 * t : ℝ) : ℂ)) *
      (Set.Icc (0 : ℝ) 1).indicator H t := by
  unfold endpointOsc
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  rw [Set.uIcc_of_le zero_le_one] at ht
  simp [Set.indicator_of_mem ht]

theorem intervalIntegrable_osc_integrand (μ : ℂ) {H : ℝ → ℂ}
    (hH : MemLp H 2 NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure) :
    IntervalIntegrable (fun t : ℝ => Complex.exp (Complex.I * μ * ((1 - 2 * t : ℝ) : ℂ)) *
      (Set.Icc (0 : ℝ) 1).indicator H t) volume 0 1 :=
  (intervalIntegrable_hat hH).continuousOn_mul (by fun_prop)

theorem endpointOsc_bessel {H : ℝ → ℂ}
    (hH : MemLp H 2 NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure) :
    Summable (fun n : ℤ => ‖endpointOsc ((n : ℂ) * (Real.pi : ℂ)) H‖ ^ 2) := by
  have h := (NlsGge.ThirdConsultation.KSPS008Support.bco_sq_summable_le
    ((Set.Icc (0 : ℝ) 1).indicator H) (memLp_hat hH).aestronglyMeasurable
    (intervalIntegrable_hat_sq hH) (x := 1) zero_le_one le_rfl 0).1
  refine h.congr (fun n => ?_)
  rw [endpointOsc_hat]
  unfold NlsGge.ThirdConsultation.KSPS008Support.bco
  simp only [pow_zero, one_mul]

theorem endpointOsc_pert_summable {H : ℝ → ℂ}
    (hH : MemLp H 2 NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure)
    (a : ℝ) (ha : 0 ≤ a) (β : ℤ → ℂ)
    (hβ : ∀ n : ℤ, ‖β n‖ ≤ a / NlsGge.ThirdConsultation.KSPS.indexWeight n) :
    Summable (fun n : ℤ => NlsGge.ThirdConsultation.KSPS.indexWeight n ^ 2 *
      ‖endpointOsc ((n : ℂ) * (Real.pi : ℂ) + β n) H - endpointOsc ((n : ℂ) * (Real.pi : ℂ)) H‖ ^ 2) := by
  have hw : ∀ n : ℤ, 1 ≤ NlsGge.ThirdConsultation.KSPS.indexWeight n :=
    NlsGge.ThirdConsultation.KSPS.one_le_indexWeight
  have hwpos : ∀ n : ℤ, 0 < NlsGge.ThirdConsultation.KSPS.indexWeight n :=
    NlsGge.ThirdConsultation.KSPS.indexWeight_pos
  have h := (NlsGge.ThirdConsultation.KSPS008Support.pert_weighted
    ((Set.Icc (0 : ℝ) 1).indicator H) (memLp_hat hH).aestronglyMeasurable
    (intervalIntegrable_hat hH) (intervalIntegrable_hat_sq hH) (x := 1) zero_le_one le_rfl ha
    NlsGge.ThirdConsultation.KSPS.indexWeight hw β
    (fun n => (le_div_iff₀ (hwpos n)).mp (hβ n))).1
  refine h.congr (fun n => ?_)
  congr 3
  rw [endpointOsc_hat, endpointOsc_hat, ← intervalIntegral.integral_sub
    (intervalIntegrable_osc_integrand _ hH) (intervalIntegrable_osc_integrand _ hH)]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  try simp only
  rw [← sub_mul]
  congr 3
  ring

theorem endpointOsc_sq_summable {H : ℝ → ℂ}
    (hH : MemLp H 2 NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure)
    (a : ℝ) (ha : 0 ≤ a) (β : ℤ → ℂ)
    (hβ : ∀ n : ℤ, ‖β n‖ ≤ a / NlsGge.ThirdConsultation.KSPS.indexWeight n) :
    Summable (fun n : ℤ => ‖endpointOsc ((n : ℂ) * (Real.pi : ℂ) + β n) H‖ ^ 2) := by
  have h1 := endpointOsc_bessel hH
  have h2 := endpointOsc_pert_summable hH a ha β hβ
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((h2.mul_left 2).add (h1.mul_left 2))
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

theorem endpointOsc_natPi_coverRep (u : PhysicalL2) (n : ℤ) :
    endpointOsc ((n : ℂ) * (Real.pi : ℂ)) (coverRep38 u) =
      (-1 : ℂ) ^ n * physicalFourier u n := by
  have hb : physicalFourier u n =
      ∫ s in (0 : ℝ)..1, Complex.exp (-(2 * Real.pi * Complex.I * n * s)) * coverRep38 u s := by
    unfold physicalFourier
    rw [fourierCoeff_eq_intervalIntegral (u : AddCircle (1 : ℝ) → ℂ) n 0]
    simp only [zero_add, div_one, one_smul, smul_eq_mul]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [coverRep38_ae_phys u] with s hs _
    rw [hs, fourier_coe_apply]
    push_cast
    simp
  rw [hb, endpointOsc, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  try simp only
  have e1 : Complex.exp (Complex.I * ((n : ℂ) * (Real.pi : ℂ)) * ((1 - 2 * t : ℝ) : ℂ)) =
      (-1 : ℂ) ^ n * Complex.exp (-(2 * Real.pi * Complex.I * n * t)) := by
    have : Complex.I * ((n : ℂ) * (Real.pi : ℂ)) * ((1 - 2 * t : ℝ) : ℂ) =
        (n : ℂ) * ((Real.pi : ℂ) * Complex.I) + -(2 * Real.pi * Complex.I * n * t) := by
      push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_int_mul, Complex.exp_pi_mul_I]
  rw [e1, mul_assoc]

end NlsGge.ThirdConsultation.KSPSWKB
