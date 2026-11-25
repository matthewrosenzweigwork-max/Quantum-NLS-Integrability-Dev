import Mathlib
import NlsGge.Atomic.M.M005
import NlsGge.Atomic.M.M045
import NlsGge.Atomic.M.M046
import NlsGge.Atomic.M.M047
import NlsGge.ThirdConsultation.M.M044Host
import NlsGge.ThirdConsultation.M.M053Host
import NlsGge.ThirdConsultation.M.Round5b
import NlsGge.ThirdConsultation.Sobolev.Round5
import NlsGge.Spectral.ActualActionSumE02_38
import NlsGge.Birkhoff.S03Measure38b
import NlsGge.ThirdConsultation.G1.NormCalculus
import NlsGge.ThirdConsultation.G6.SobolevBirkhoffCompatCore

                                                                                                                  
                                                                                  
                                                                                                                       
                                                                                                                       
                                                                                                  
                                               
                                                                                           
                                                                                                   
                                                          
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators ENNReal
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.GKDefinitionDesign NlsGge.Birkhoff
open NlsGge.Sobolev38 NlsGge.Atomic.Common
open NlsGge.ThirdConsultation

namespace NlsGge.ThirdConsultation.M048C

open NlsGge.ThirdConsultation.M

theorem summable_sq_fourierSeq38 (v : PhysicalL2) :
    Summable (fun n : ℤ => ‖fourierSeq38 v n‖ ^ 2) := by
  have h := (reflectedFourierL2 v).2
  have := (memℓp_gen_iff (p := (2 : ℝ≥0∞)) (by norm_num)).1 h
  simpa [fourierSeq38] using this

theorem weight_le (m : ℕ) (n : ℤ) :
    sobolevModeWeight (m : ℝ) n ≤ 2 ^ m * ((2 * Real.pi * |(n : ℝ)|) ^ (2 * m) + 1) := by
  have hw : sobolevModeWeight (m : ℝ) n = (1 + (n : ℝ) ^ 2) ^ m := by
    unfold sobolevModeWeight japaneseBracket
    rw [show (2 : ℝ) * (m : ℝ) = ((2 * m : ℕ) : ℝ) by push_cast; ring]
    change (Real.sqrt (1 + (n : ℝ) ^ 2)) ^ (((2 * m : ℕ) : ℝ)) = _
    rw [Real.rpow_natCast, pow_mul, Real.sq_sqrt (by positivity)]
  rw [hw]
  set x : ℝ := (n : ℝ) ^ 2 with hx
  have hx0 : 0 ≤ x := sq_nonneg _
  have hpi : (1 : ℝ) ≤ (2 * Real.pi) ^ 2 := by nlinarith [Real.pi_gt_three]
  have hxm : x ^ m ≤ (2 * Real.pi * |(n : ℝ)|) ^ (2 * m) := by
    rw [pow_mul, mul_pow, sq_abs]
    have : x ≤ (2 * Real.pi) ^ 2 * x := le_mul_of_one_le_left hx0 hpi
    exact pow_le_pow_left₀ hx0 this m
  by_cases h1 : x ≤ 1
  · have : (1 + x) ^ m ≤ 2 ^ m := pow_le_pow_left₀ (by positivity) (by linarith) m
    have h0 : 0 ≤ (2 * Real.pi * |(n : ℝ)|) ^ (2 * m) := by positivity
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) m]
  · have : (1 + x) ^ m ≤ (2 * x) ^ m := pow_le_pow_left₀ (by positivity) (by linarith) m
    rw [mul_pow] at this
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) m]

/-- Actual Fourier comparison of the house H^m norm with the top derivative and the mass. -/
theorem house_norm_le (m : ℕ) (u : SobolevR m) :
    ‖u‖ ^ 2 ≤ 2 ^ m * (topDerivativeNorm m u ^ 2 + massCharge (physicalOfSobolev u)) := by
  set x := physicalSobolevFourierEquiv38 (m : ℝ) u with hx
  have hu : ‖u‖ = ‖x‖ := ((physicalSobolevFourierEquiv38 (m : ℝ)).norm_map u).symm
  have hcar := carrier_hasSum_norm_sq38 (m : ℝ) x
  have hc : ∀ n, fourierSeq38 (physicalOfSobolev u) n = carrierCoe38 (m : ℝ) x n := by
    intro n; rw [← physicalSobolevEmbed_eq_M]; exact physicalSobolevEmbed_fourier m u n
  have hd : ∀ n, ‖fourierSeq38 (physicalSobolevDerivative38 m u) n‖ ^ 2 =
      (2 * Real.pi * |(n : ℝ)|) ^ (2 * m) * ‖carrierCoe38 (m : ℝ) x n‖ ^ 2 := by
    intro n
    rw [NlsGge.GKDefinitionDesign.physicalSobolevDerivative38_reflected, norm_mul, norm_pow, mul_pow]
    congr 1
    rw [show (-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) =
        ((-2 * Real.pi * (n : ℝ) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, ← pow_mul,
      show |-2 * Real.pi * (n : ℝ)| = 2 * Real.pi * |(n : ℝ)| by
        rw [abs_mul, abs_mul, abs_neg, abs_two, abs_of_pos Real.pi_pos]]
    ring_nf
  have htop : topDerivativeNorm m u ^ 2 =
      ∑' n : ℤ, (2 * Real.pi * |(n : ℝ)|) ^ (2 * m) * ‖carrierCoe38 (m : ℝ) x n‖ ^ 2 := by
    have h0 : topDerivativeNorm m u = ‖physicalSobolevDerivative38 m u‖ := rfl
    rw [h0, norm_sq_eq_tsum_fourierSeq38]
    exact tsum_congr hd
  have hmass : massCharge (physicalOfSobolev u) = ∑' n : ℤ, ‖carrierCoe38 (m : ℝ) x n‖ ^ 2 := by
    unfold massCharge; rw [norm_sq_eq_tsum_fourierSeq38]
    exact tsum_congr (fun n => by rw [hc n])
  have hs1 : Summable (fun n : ℤ => (2 * Real.pi * |(n : ℝ)|) ^ (2 * m) * ‖carrierCoe38 (m : ℝ) x n‖ ^ 2) := by
    have := summable_sq_fourierSeq38 (physicalSobolevDerivative38 m u)
    exact this.congr hd
  have hs2 : Summable (fun n : ℤ => ‖carrierCoe38 (m : ℝ) x n‖ ^ 2) := by
    have := summable_sq_fourierSeq38 (physicalOfSobolev u)
    exact this.congr (fun n => by rw [hc n])
  rw [hu, ← hcar.tsum_eq, htop, hmass, ← hs1.tsum_add hs2, ← tsum_mul_left]
  refine hcar.summable.tsum_le_tsum (fun n => ?_) ((hs1.add hs2).mul_left _)
  have := mul_le_mul_of_nonneg_right (weight_le m n) (sq_nonneg ‖carrierCoe38 (m : ℝ) x n‖)
  nlinarith

theorem A0_eq (m : ℕ) (hm : 1 ≤ m) (u : SobolevR m) :
    actionWeightedSum 0 (physicalOfSobolev u) = ‖physicalOfSobolev u‖ ^ 2 := by
  have hN : physicalSobolev (m : ℝ) (physicalOfSobolev u) := by
    rw [physicalSobolev_iff_mem, ← physicalSobolevEmbed_eq_M]
    exact NlsGge.GKDefinitionDesign.physicalSobolevEmbed_mem m u
  have h1 : physicalSobolev ((1 : ℕ) : ℝ) (physicalOfSobolev u) := (psn_mono hm hN).1
  have hH1 : SobolevSquareSummable 1 (physicalFourier (physicalOfSobolev u)) := by
    rw [physicalSobolev_iff_mem] at h1
    simpa using (fourierSeq38_mem_iff ((1 : ℕ) : ℝ) _).1 h1
  have hI := actualGapAction_hasSum_E02_38 (physicalOfSobolev u) hH1
  unfold actionWeightedSum
  rw [← hI.tsum_eq]
  exact tsum_congr (fun n => by simp [molnarWeight, action])

theorem inverse_core
    (htrace : ∀ (m : ℕ) (hm : 1 ≤ m) (u : SobolevR m),
      HasSum (fun n : ℤ =>
        (4 : ℝ) ^ m * higherAction (physicalOfSobolev u) n (2 * m + 1))
        (signedCharge m u))
    (h044 : ∀ (m : ℕ) (hm : 1 ≤ m) (u : SobolevR m),
      actionWeightedSumENNReal m (physicalOfSobolev u) ≠ ⊤ ∧
      oddTraceEnergy m (physicalOfSobolev u) ≠ ⊤ ∧
      oddTraceSum m (physicalOfSobolev u) ≤
        actionWeightedSum m (physicalOfSobolev u) +
          (64 * Real.pi) ^ (2 * m) *
            (1 + actionWeightedSum 0 (physicalOfSobolev u)) ^ (2 * m - 1) *
            actionWeightedSum 1 (physicalOfSobolev u) ^ (2 * m - 1))
    (h042 : ∀ (u : SobolevR 1),
      (1/3:ℝ) * ‖u‖^2 ≤
        actionWeightedSum 1 (physicalOfSobolev u) +
          actionWeightedSum 0 (physicalOfSobolev u)^2)
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ d : ℝ, 0 < d ∧ ∀ u : SobolevR m,
      ‖u‖^2 ≤
        d^2 * (actionWeightedSum m (physicalOfSobolev u) +
          (1+actionWeightedSum 1 (physicalOfSobolev u))^(4*m-3) *
            actionWeightedSum 0 (physicalOfSobolev u)) := by
  -- common facts for a field u
  have facts : ∀ (u : SobolevR m),
      0 ≤ actionWeightedSum 0 (physicalOfSobolev u) ∧
      actionWeightedSum 0 (physicalOfSobolev u) ≤ actionWeightedSum 1 (physicalOfSobolev u) ∧
      actionWeightedSum 1 (physicalOfSobolev u) ≤ actionWeightedSum m (physicalOfSobolev u) ∧
      actionWeightedSum 1 (physicalOfSobolev u) ^ m ≤
        actionWeightedSum m (physicalOfSobolev u) * actionWeightedSum 0 (physicalOfSobolev u) ^ (m - 1) := by
    intro u
    obtain ⟨hs0, hs1, hsm, hhol⟩ := action_weight_log_convex_finite (physicalOfSobolev u) m hm (h044 m hm u).1
    refine ⟨m046_real_nonneg _ 0, ?_, ?_, hhol⟩
    · exact hs0.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_right (m046_weight_le 0 1 (by norm_num) n)
        (actualGapAction_nonneg38 _ n)) hs1
    · exact hs1.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_right (m046_weight_le 1 m hm n)
        (actualGapAction_nonneg38 _ n)) hsm
  by_cases hm1 : m = 1
  · subst hm1
    refine ⟨2, by norm_num, fun u => ?_⟩
    obtain ⟨hA0, hA01, -, -⟩ := facts u
    have hseed := h042 u
    set A0 := actionWeightedSum 0 (physicalOfSobolev u)
    set A1 := actionWeightedSum 1 (physicalOfSobolev u)
    have hA1 : 0 ≤ A1 := le_trans hA0 hA01
    have hsq : A0 ^ 2 ≤ (1 + A1) * A0 := by
      have := mul_le_mul_of_nonneg_right hA01 hA0
      rw [sq]; linarith
    have hnn : 0 ≤ (1 + A1) * A0 := mul_nonneg (by linarith) hA0
    rw [show 4 * 1 - 3 = 1 by rfl, pow_one, show (2 : ℝ) ^ 2 = 4 by norm_num]
    linarith
  · have hm2 : 2 ≤ m := by omega
    obtain ⟨C45, hC45, h45⟩ := top_derivative_from_charge m hm
    obtain ⟨C47, hC47, h47⟩ := inverse_polynomial_domination m hm2
    set K := (64 * Real.pi) ^ (2 * m) with hK
    have hK0 : 0 ≤ K := by positivity
    set D := (2 : ℝ) ^ m * (3 + C45 + (2 * K + C45) * C47) with hD
    have hD0 : 0 < D := by positivity
    refine ⟨Real.sqrt D, Real.sqrt_pos.2 hD0, fun u => ?_⟩
    rw [Real.sq_sqrt hD0.le]
    obtain ⟨hA0, hA01, hA1m, hhol⟩ := facts u
    set w := physicalOfSobolev u with hw
    set A0 := actionWeightedSum 0 w with hA0d
    set A1 := actionWeightedSum 1 w with hA1d
    set Am := actionWeightedSum m w with hAmd
    have hA1 : 0 ≤ A1 := le_trans hA0 hA01
    have hAm : 0 ≤ Am := le_trans hA1 hA1m
    have hnorm : ‖w‖ ^ 2 = A0 := (A0_eq m hm u).symm
    have hmass : massCharge w = A0 := hnorm
    have hS : signedCharge m u = oddTraceSum m w := by
      rw [← (htrace m hm u).tsum_eq]; rfl
    have h44 := (h044 m hm u).2.2
    set P := (1 + A0) ^ (2 * m - 1) * A1 ^ (2 * m - 1) with hP
    have hP0 : 0 ≤ P := by positivity
    have hSle : signedCharge m u ≤ Am + K * P := by
      rw [hS]; calc oddTraceSum m w ≤ Am + K * (1 + A0) ^ (2 * m - 1) * A1 ^ (2 * m - 1) := h44
        _ = Am + K * P := by rw [hP]; ring
    have htop := h45 u
    have hw4 : ‖w‖ ^ (4 * m) = A0 ^ (2 * m) := by
      rw [show 4 * m = 2 * (2 * m) by ring, pow_mul, hnorm]
    rw [hw4, hnorm] at htop
    have hhouse := house_norm_le m u
    rw [hmass] at hhouse
    set T := Am + (1 + A1) ^ (4 * m - 3) * A0 with hT
    have hrel : ActionMomentRelations m A0 A1 Am := ⟨hA0, hA01, hA1m, hhol⟩
    have h47u := h47 A0 A1 Am hrel
    rw [← hT] at h47u
    have hpow0 : 0 ≤ A0 ^ (2 * m + 1) := by positivity
    have hT0 : 0 ≤ T := by positivity
    have hA0T : A0 ≤ T := by
      have : 1 ≤ (1 + A1) ^ (4 * m - 3) := one_le_pow₀ (by linarith)
      nlinarith [mul_le_mul_of_nonneg_right this hA0]
    have hAmT : Am ≤ T := by
      have : 0 ≤ (1 + A1) ^ (4 * m - 3) * A0 := by positivity
      linarith
    have hPT : P ≤ C47 * T := by linarith
    have hA0pT : A0 ^ (2 * m + 1) ≤ C47 * T := by linarith
    have hexp : C45 * (1 + A0 ^ (2 * m)) * A0 = C45 * (A0 + A0 ^ (2 * m + 1)) := by ring
    rw [hexp] at htop
    have hbound : topDerivativeNorm m u ^ 2 + A0 ≤ (3 + C45 + (2 * K + C45) * C47) * T := by
      have e1 : C45 * (A0 + A0 ^ (2 * m + 1)) ≤ C45 * T + C45 * (C47 * T) := by
        have := mul_le_mul_of_nonneg_left (add_le_add hA0T hA0pT) hC45
        linarith [show C45 * (T + C47 * T) = C45 * T + C45 * (C47 * T) by ring]
      have e2 : 2 * (Am + K * P) ≤ 2 * T + 2 * K * (C47 * T) := by
        have := mul_le_mul_of_nonneg_left hPT hK0
        linarith [show 2 * K * (C47 * T) = 2 * (K * (C47 * T)) by ring]
      have e3 : (3 + C45 + (2 * K + C45) * C47) * T =
          3 * T + C45 * T + 2 * K * (C47 * T) + C45 * (C47 * T) := by ring
      rw [e3]
      linarith [htop, hSle, e1, e2, hA0T]
    calc ‖u‖ ^ 2 ≤ 2 ^ m * (topDerivativeNorm m u ^ 2 + A0) := hhouse
      _ ≤ 2 ^ m * ((3 + C45 + (2 * K + C45) * C47) * T) :=
          mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = D * T := by rw [hD]; ring

end NlsGge.ThirdConsultation.M048C
