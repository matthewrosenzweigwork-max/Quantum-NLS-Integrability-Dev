import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS012Support2
import NlsGge.ThirdConsultation.KSPS.KSPS012Support6
import NlsGge.ThirdConsultation.KSPS.KSPS011Support11
import NlsGge.ThirdConsultation.KSPS.KSPS011Support13

                                                                                                                    
                                                                                                      
                                                                                                      
                                                                                                       
                                                                      
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Atomic.Common NlsGge.GK38
open NlsGge.Schur NlsGge.Analysis NlsGge.GKDefinitionDesign NlsGge.ThirdConsultation.KSPS

namespace NlsGge.ThirdConsultation.KSPSWKB

theorem Tz_sq_summable (w v : PhysicalL2) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) :
    RealSqSummable (fun n : ℤ => ‖NlsGge.ThirdConsultation.KSPS012Support5.Tz (coverRep38 w)
      (coverRep38 v) (((σ * n : ℤ) : ℂ) * (Real.pi : ℂ))‖) := by
  have h := NlsGge.ThirdConsultation.KSPS012Support2.T_sq_summable (c := coverRep38 w)
    (g := coverRep38 v) (stronglyMeasurable_coverRep38 w).aestronglyMeasurable
    (intervalIntegrable_coverRep38_one w) (intervalIntegrable_coverRep38_sq_one w)
    (intervalIntegrable_coverRep38_one v)
  have hk : ∀ k : ℤ, NlsGge.ThirdConsultation.KSPS012Support5.Tz (coverRep38 w) (coverRep38 v)
      ((k : ℂ) * (Real.pi : ℂ)) = ∫ t in (0 : ℝ)..1,
        (Complex.exp (-(2 * Real.pi * Complex.I * k * t)) * coverRep38 w t) *
          ∫ s in t..1, Complex.exp (2 * Real.pi * Complex.I * k * s) * coverRep38 v s := by
    intro k
    unfold NlsGge.ThirdConsultation.KSPS012Support5.Tz
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    beta_reduce
    have e1 : Complex.exp (-(2 * Complex.I * ((k : ℂ) * (Real.pi : ℂ)) * (t : ℂ))) =
        Complex.exp (-(2 * Real.pi * Complex.I * k * t)) := by congr 1; ring
    have e2 : ∫ s in t..1, Complex.exp (2 * Complex.I * ((k : ℂ) * (Real.pi : ℂ)) * (s : ℂ)) *
          coverRep38 v s =
        ∫ s in t..1, Complex.exp (2 * Real.pi * Complex.I * k * s) * coverRep38 v s := by
      refine intervalIntegral.integral_congr (fun s _ => ?_)
      beta_reduce
      have : Complex.exp (2 * Complex.I * ((k : ℂ) * (Real.pi : ℂ)) * (s : ℂ)) =
          Complex.exp (2 * Real.pi * Complex.I * k * s) := by congr 1; ring
      rw [this]
    rw [e1, e2]
  have hs : Summable (fun k : ℤ => ‖NlsGge.ThirdConsultation.KSPS012Support5.Tz (coverRep38 w)
      (coverRep38 v) ((k : ℂ) * (Real.pi : ℂ))‖ ^ 2) := by
    refine h.congr (fun k => ?_)
    rw [hk k]
  unfold RealSqSummable
  rcases hσ with rfl | rfl
  · simpa using hs
  · have := (Equiv.neg ℤ).summable_iff.2 hs
    refine this.congr (fun n => ?_)
    simp [Function.comp]

theorem abs_le_indexWeight (n : ℤ) : |(n : ℝ)| ≤ indexWeight n := by
  unfold indexWeight
  exact Real.abs_le_sqrt (by nlinarith [sq_nonneg (n : ℝ)])

theorem exp_neg_I_pi_int (σ n : ℤ) (hσ : σ = 1 ∨ σ = -1) :
    Complex.exp (-(Complex.I * (((σ * n : ℤ) : ℂ) * (Real.pi : ℂ)))) = (-1 : ℂ) ^ n := by
  have e : -(Complex.I * (((σ * n : ℤ) : ℂ) * (Real.pi : ℂ))) =
      ((-(σ * n) : ℤ) : ℂ) * ((Real.pi : ℂ) * Complex.I) := by push_cast; ring
  rw [e, Complex.exp_int_mul, Complex.exp_pi_mul_I]
  rcases hσ with rfl | rfl
  · rw [show -((1 : ℤ) * n) = -n by ring]
    exact neg_one_zpow_neg n
  · simp

theorem xi_lower_bound (a : ℝ) (xi : ℤ → ℂ)
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

theorem iw_le_two_mul (n : ℤ) (hn : 1 ≤ |(n : ℝ)|) : indexWeight n ≤ 2 * |(n : ℝ)| := by
  unfold indexWeight
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have : (n : ℝ) ^ 2 = |(n : ℝ)| ^ 2 := (sq_abs _).symm
  rw [this]; nlinarith

end NlsGge.ThirdConsultation.KSPSWKB
