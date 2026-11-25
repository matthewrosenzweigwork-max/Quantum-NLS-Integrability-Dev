import Mathlib
import NlsGge.ThirdConsultation.KSPSRiccatiHost

                                                                             
                                                                                                                      
                                                                                             
                                                                                                    
                                                                                                
                                                                                                
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators ENNReal
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.GK38 NlsGge.Atomic.Common
open NlsGge.GKDefinitionDesign NlsGge.ThirdConsultation.KSPS

namespace NlsGge.ThirdConsultation.KSPSSupport
noncomputable section

/-- S11a: the exponential remainder for an arbitrary complex argument. -/
theorem h161_exp_remainder (z : ℂ) :
    ‖Complex.exp z - 1 - z‖ ≤ ‖z‖ ^ 2 * Real.exp ‖z‖ := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp z 2
  have hs : ∑ m ∈ Finset.range 2, z ^ m / (m.factorial : ℂ) = 1 + z := by
    simp [Finset.sum_range_succ]
  rw [hs] at h
  have he : Complex.exp z - 1 - z = Complex.exp z - (1 + z) := by ring
  rw [he]
  exact h

/-- L2 tool: an L2 bound on the unit interval from the integral of the squared norm. -/
theorem h161_eLp2_le (f : ℝ → ℂ) (hf : MemLp f 2 KSPSRiccati.intervalMeasure)
    (C : ℝ) (hC : 0 ≤ C) (h : ∫ t in (0 : ℝ)..1, ‖f t‖ ^ 2 ≤ C ^ 2) :
    eLpNorm f 2 KSPSRiccati.intervalMeasure ≤ ENNReal.ofReal C := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  apply ENNReal.ofReal_le_ofReal
  rw [show ((2 : ENNReal).toReal) = 2 by norm_num]
  have hX : ∫ a, ‖f a‖ ^ (2 : ℝ) ∂KSPSRiccati.intervalMeasure =
      ∫ t in (0 : ℝ)..1, ‖f t‖ ^ 2 := by
    unfold KSPSRiccati.intervalMeasure
    rw [intervalIntegral.integral_of_le (by norm_num), integral_Icc_eq_integral_Ioc]
    simp only [Real.rpow_two]
  rw [hX]
  have hnn : 0 ≤ ∫ t in (0 : ℝ)..1, ‖f t‖ ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun t _ => by positivity)
  calc (∫ t in (0 : ℝ)..1, ‖f t‖ ^ 2) ^ (2 : ℝ)⁻¹
      ≤ (C ^ 2) ^ (2 : ℝ)⁻¹ := Real.rpow_le_rpow hnn h (by norm_num)
    _ = C := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hC]
      norm_num

/-- Pointwise: the product of two representatives is bounded by half the sum of squares. -/
theorem h161_coverRep_mul_le (p q : PhysicalL2) (t : ℝ) :
    ‖coverRep38 p t * coverRep38 q t‖ ≤ (‖coverRep38 p t‖ ^ 2 + ‖coverRep38 q t‖ ^ 2) / 2 := by
  rw [norm_mul]
  nlinarith [sq_nonneg (‖coverRep38 p t‖ - ‖coverRep38 q t‖),
    norm_nonneg (coverRep38 p t), norm_nonneg (coverRep38 q t)]

/-- S11b: the prefix integral of two representatives on [0,x], x in [0,1], is bounded by the
L2 norms of the two circle fields. -/
theorem h161_prefix_le (p q : PhysicalL2) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ‖∫ t in (0 : ℝ)..x, coverRep38 p t * coverRep38 q t‖ ≤ (‖p‖ ^ 2 + ‖q‖ ^ 2) / 2 := by
  have hx0 : (0 : ℝ) ≤ x := hx.1
  have hx1 : x ≤ 1 := hx.2
  have hg : IntervalIntegrable (fun t => (‖coverRep38 p t‖ ^ 2 + ‖coverRep38 q t‖ ^ 2) / 2)
      volume 0 1 :=
    ((intervalIntegrable_coverRep38_sq_one p).add
      (intervalIntegrable_coverRep38_sq_one q)).div_const 2
  have hsub : Set.uIcc (0 : ℝ) x ⊆ Set.uIcc (0 : ℝ) 1 :=
    Set.uIcc_subset_uIcc Set.left_mem_uIcc (Set.mem_uIcc.2 (Or.inl ⟨hx0, hx1⟩))
  have h1 : ‖∫ t in (0 : ℝ)..x, coverRep38 p t * coverRep38 q t‖ ≤
      ∫ t in (0 : ℝ)..x, (‖coverRep38 p t‖ ^ 2 + ‖coverRep38 q t‖ ^ 2) / 2 := by
    apply intervalIntegral.norm_integral_le_of_norm_le hx0
    · exact Filter.Eventually.of_forall (fun t _ => h161_coverRep_mul_le p q t)
    · exact hg.mono_set hsub
  have h2 : ∫ t in (0 : ℝ)..x, (‖coverRep38 p t‖ ^ 2 + ‖coverRep38 q t‖ ^ 2) / 2 ≤
      ∫ t in (0 : ℝ)..1, (‖coverRep38 p t‖ ^ 2 + ‖coverRep38 q t‖ ^ 2) / 2 :=
    intervalIntegral.integral_mono_interval le_rfl hx0 hx1
      (Filter.Eventually.of_forall (fun t => by positivity)) hg
  have h3 : ∫ t in (0 : ℝ)..1, (‖coverRep38 p t‖ ^ 2 + ‖coverRep38 q t‖ ^ 2) / 2 =
      (‖p‖ ^ 2 + ‖q‖ ^ 2) / 2 := by
    rw [intervalIntegral.integral_div,
      intervalIntegral.integral_add (intervalIntegrable_coverRep38_sq_one p)
        (intervalIntegrable_coverRep38_sq_one q),
      integral_sq_coverRep38_one, integral_sq_coverRep38_one]
  linarith

/-- S11b for the side pair of the Riccati prefix. -/
theorem h161_prefix_bound {N : ℕ} (φ : SobolevC N) (b : Bool) (k : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ‖KSPSRiccati.«prefix» φ b k x‖ ≤
      (‖KSPSRiccati.sidePotential φ b‖ ^ 2 + ‖KSPSRiccati.coefficient φ b k‖ ^ 2) / 2 :=
  h161_prefix_le _ _ hx

/-- S11b for the mass prefix of a pair. -/
theorem h161_massPrefix_bound {N : ℕ} (φ : SobolevC N) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ‖KSPSRiccati.massPrefix φ x‖ ≤
      (‖(toPotPair φ).1‖ ^ 2 + ‖(toPotPair φ).2‖ ^ 2) / 2 :=
  h161_prefix_le (toPotPair φ).1 (toPotPair φ).2 hx

end
end NlsGge.ThirdConsultation.KSPSSupport
