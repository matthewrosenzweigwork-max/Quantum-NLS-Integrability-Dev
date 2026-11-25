import Mathlib
import NlsGge.Atomic.S.S024
import NlsGge.Schur.ActualSchurGapEnergyLower38V1

                                                                                                            
                                                                                                                              
                                                                                                                         
                                                                                                                            
                                                                                
set_option autoImplicit false
noncomputable section
open NlsGge.Pilot NlsGge.Analysis NlsGge.Schur NlsGge.Measure NlsGge.SpectralFoundations
namespace NlsGge.ThirdConsultation.S

theorem weight_ge_on_highGap (lo up : ℝ) (hl : 0 < lo) (hlu : lo ≤ up) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ (c : BoundedCoefficients lo up)
      (R : ℝ), 1 ≤ R → ∀ (n : ℤ), K * R ^ 6 ≤ |(n : ℝ)| →
      ∀ (w : SchurH1), ‖w‖ ≤ R → ∀ r : ℝ,
      r ∈ Set.Icc (reflectedEndsAt n w).1 (reflectedEndsAt n w).2 →
      fullWeightRate c.val n * Real.exp (-C * R ^ 3 / |(n : ℝ)| ^ (3 / 2 : ℝ)) ≤
        NlsGge.Weights.weight c.val (2 * r) := by
  obtain ⟨Cs, Ks, hCs, hKs, hdisp⟩ := highGap_displacement_bound
  obtain ⟨Cg, hCg, hg⟩ := weight_gap_lower38 lo up hl hlu
  refine ⟨2 * Cg * Cs * Real.pi ^ (-1 / 2 : ℝ) + 1, Ks + Cs + 1, by positivity, by positivity, ?_⟩
  intro c R hR n hn w hwR r hr
  have hb : ∀ j, lo ≤ c.val j := fun j => (c.property.2.2 j).1
  have hu : ∀ j, c.val j ≤ up := fun j => (c.property.2.2 j).2
  have hR0 : 0 ≤ R := by linarith
  have hR3 : 1 ≤ R ^ 3 := one_le_pow₀ hR
  have hR36 : R ^ 3 ≤ R ^ 6 := pow_le_pow_right₀ hR (by norm_num)
  have hR3' : 0 ≤ R ^ 3 := by positivity
  have hR6' : 0 ≤ R ^ 6 := by positivity
  have hKR : (Ks + Cs + 1) * R ^ 3 ≤ |(n : ℝ)| :=
    le_trans (mul_le_mul_of_nonneg_left hR36 (by positivity)) hn
  have hKs3 : Ks * R ^ 3 ≤ |((-n : ℤ) : ℝ)| := by
    rw [Int.cast_neg, abs_neg]
    refine le_trans ?_ hKR
    exact mul_le_mul_of_nonneg_right (by linarith) hR3'
  have hnpos : 0 < |(n : ℝ)| := by nlinarith
  have hn0 : n ≠ 0 := by
    intro h; rw [h] at hnpos; simp at hnpos
  have hmax := hdisp R hR (-n) hKs3 w hwR
  rw [Int.cast_neg, abs_neg] at hmax
  obtain ⟨hlow, hupp⟩ := max_le_iff.mp hmax
  set δ : ℝ := Cs * R ^ 3 / |(n : ℝ)| with hδ
  have hδ0 : 0 ≤ δ := by positivity
  have hδ2 : 2 * δ ≤ Real.pi * |(n : ℝ)| := by
    have h1 : (Cs + 1) * R ^ 3 ≤ |(n : ℝ)| := by
      refine le_trans ?_ hKR
      exact mul_le_mul_of_nonneg_right (by linarith) hR3'
    have h2 : δ ≤ 1 := by
      rw [hδ, div_le_one hnpos]
      nlinarith
    have := Real.pi_gt_three
    nlinarith
  have hr' : -(actualGapUpperAllE02_38 (physicalH1ComplexCarrierToL2Actual22 w) (-n)) ≤ r ∧
      r ≤ -(actualGapLowerAllE02_38 (physicalH1ComplexCarrierToL2Actual22 w) (-n)) := hr
  have hlam : |(-r) + n * Real.pi| ≤ δ := by
    rw [abs_le] at hlow hupp ⊢
    push_cast at hlow hupp
    constructor <;> nlinarith [hr'.1, hr'.2, hlow.1, hlow.2, hupp.1, hupp.2]
  have hmain := hg c.val hb hu n (-r) δ hn0 hlam hδ2
  have hWe : NlsGge.Weights.weight c.val (2 * (-r)) = NlsGge.Weights.weight c.val (2 * r) := by
    rw [show 2 * (-r) = -(2 * r) by ring, NlsGge.Weights.weight_even]
  rw [hWe] at hmain
  refine le_trans ?_ hmain
  have hrate : fullWeightRate c.val n = NlsGge.Weights.weight c.val (2 * Real.pi * n) := rfl
  rw [hrate]
  have hWpos := NlsGge.Weights.weight_pos lo up c.val hl hb hu (2 * Real.pi * n)
  apply mul_le_mul_of_nonneg_left _ hWpos.le
  apply Real.exp_le_exp.mpr
  -- exponent comparison
  have h1 : (Real.pi * |(n : ℝ)|) ^ (-1 / 2 : ℝ) =
      Real.pi ^ (-1 / 2 : ℝ) * |(n : ℝ)| ^ (-1 / 2 : ℝ) :=
    Real.mul_rpow Real.pi_pos.le hnpos.le
  have h2 : |(n : ℝ)| ^ (-(3 / 2) : ℝ) = |(n : ℝ)| ^ (-1 / 2 : ℝ) * |(n : ℝ)|⁻¹ := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hnpos]; norm_num
  have h3 : |(n : ℝ)| ^ (3 / 2 : ℝ) = (|(n : ℝ)| ^ (-(3 / 2) : ℝ))⁻¹ := by
    rw [Real.rpow_neg hnpos.le, inv_inv]
  have hpow0 : 0 < |(n : ℝ)| ^ (-(3 / 2) : ℝ) := Real.rpow_pos_of_pos hnpos _
  have hA : Cg * (Real.pi * |(n : ℝ)|) ^ (-1 / 2 : ℝ) * (2 * δ) =
      (2 * Cg * Cs * Real.pi ^ (-1 / 2 : ℝ)) * (R ^ 3 * |(n : ℝ)| ^ (-(3 / 2) : ℝ)) := by
    rw [h1, h2, hδ]
    field_simp
  have hC : -(2 * Cg * Cs * Real.pi ^ (-1 / 2 : ℝ) + 1) * R ^ 3 / |(n : ℝ)| ^ (3 / 2 : ℝ) =
      -((2 * Cg * Cs * Real.pi ^ (-1 / 2 : ℝ) + 1) * (R ^ 3 * |(n : ℝ)| ^ (-(3 / 2) : ℝ))) := by
    rw [h3]
    field_simp
  rw [hC, hA]
  have hT : 0 ≤ R ^ 3 * |(n : ℝ)| ^ (-(3 / 2) : ℝ) := by positivity
  nlinarith [mul_nonneg hT hT]

end NlsGge.ThirdConsultation.S

end
