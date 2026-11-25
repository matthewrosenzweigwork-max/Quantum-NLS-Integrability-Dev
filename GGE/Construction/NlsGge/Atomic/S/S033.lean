import Mathlib
import NlsGge.ThirdConsultation.S.SShared06

                                                                                                            
                                                                                                                             
                                                                      
                                                                                                                         
set_option autoImplicit false
noncomputable section
open NlsGge.Pilot NlsGge.Analysis NlsGge.Schur
namespace NlsGge.ThirdConsultation.S

theorem schurThreshold_all :
    0 < schurAllThreshold ∧ ∀ (R : ℝ), 1 ≤ R →
      let M := splitCutoff schurAllThreshold R
      schurCommonThreshold * R ^ 6 ≤ (M : ℝ) ∧ 1 ≤ M ∧
      (∀ n : ℤ, M < n.natAbs → schurNumericConditions R n) := by
  have hPnn : 0 ≤ |freeResolventComplementaryInverseUniformConstant22 ^ 2 *
      freeResolventSchurUniformConstant ^ 2| := abs_nonneg _
  have ha1 := abs_nonneg schurCommonThreshold
  have ha2 := abs_nonneg actualSchurCenterThresholdConstant38
  have ha3 := abs_nonneg actualSchurShiftedRootsConstant38
  have ha4 := abs_nonneg actualSchurGapLocalConstant38
  have hA512 : 512 ≤ schurAllThreshold := by unfold schurAllThreshold; linarith
  have hA1 : 512 * |schurCommonThreshold| ≤ schurAllThreshold := by unfold schurAllThreshold; linarith
  have hA2 : 512 * |actualSchurCenterThresholdConstant38| ≤ schurAllThreshold := by
    unfold schurAllThreshold; linarith
  have hA3 : 512 * |actualSchurShiftedRootsConstant38| ≤ schurAllThreshold := by
    unfold schurAllThreshold; linarith
  have hA5 : 512 * |freeResolventComplementaryInverseUniformConstant22 ^ 2 *
      freeResolventSchurUniformConstant ^ 2| ≤ schurAllThreshold := by
    unfold schurAllThreshold; linarith
  refine ⟨by linarith, ?_⟩
  intro R hR
  intro M
  have hR0 : 0 ≤ R := by linarith
  have hR6 : 1 ≤ R ^ 6 := one_le_pow₀ hR
  have hR3 : 1 ≤ R ^ 3 := one_le_pow₀ hR
  have hR4 : 1 ≤ R ^ 4 := one_le_pow₀ hR
  have h36 : R ^ 3 ≤ R ^ 6 := pow_le_pow_right₀ hR (by norm_num)
  have h46 : R ^ 4 ≤ R ^ 6 := pow_le_pow_right₀ hR (by norm_num)
  have hR6' : 0 ≤ R ^ 6 := by positivity
  have hAR : schurAllThreshold * R ^ 6 ≤ (M : ℝ) := Nat.le_ceil _
  have hAR512 : 512 ≤ schurAllThreshold * R ^ 6 := by nlinarith
  have hM1 : 1 ≤ M := by
    have : (0 : ℝ) < (M : ℝ) := by linarith
    exact_mod_cast this
  refine ⟨?_, hM1, ?_⟩
  · calc schurCommonThreshold * R ^ 6 ≤ |schurCommonThreshold| * R ^ 6 :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hR6'
      _ ≤ schurAllThreshold * R ^ 6 :=
          mul_le_mul_of_nonneg_right (by linarith) hR6'
      _ ≤ (M : ℝ) := hAR
  · intro n hn
    have hx : (M : ℝ) < |(n : ℝ)| := by
      have : (M : ℝ) < (n.natAbs : ℝ) := by exact_mod_cast hn
      rwa [Nat.cast_natAbs, Int.cast_abs] at this
    set x : ℝ := |(n : ℝ)| with hxdef
    have hxA : schurAllThreshold * R ^ 6 < x := lt_of_le_of_lt hAR hx
    have hx512 : 512 < x := lt_of_le_of_lt hAR512 hxA
    have hx0 : 0 < x := by linarith
    have hcube : (4 * R) ^ 3 = 64 * R ^ 3 := by ring
    -- generic comparison: K * (4R)^3 <= x whenever 512 |K| <= A
    have key : ∀ K : ℝ, 512 * |K| ≤ schurAllThreshold → K * (4 * R) ^ 3 ≤ x := by
      intro K hK
      rw [hcube]
      have h1 : K * (64 * R ^ 3) ≤ |K| * (64 * R ^ 6) := by
        have := le_abs_self K
        have hh : 64 * R ^ 3 ≤ 64 * R ^ 6 := by linarith
        calc K * (64 * R ^ 3) ≤ |K| * (64 * R ^ 3) :=
              mul_le_mul_of_nonneg_right this (by positivity)
          _ ≤ |K| * (64 * R ^ 6) := mul_le_mul_of_nonneg_left hh (abs_nonneg _)
      have h2 : |K| * (64 * R ^ 6) ≤ schurAllThreshold * R ^ 6 := by
        have : 64 * |K| ≤ schurAllThreshold := by linarith [abs_nonneg K]
        nlinarith [mul_le_mul_of_nonneg_right this hR6']
      linarith
    refine ⟨by linarith, key _ hA2, key _ hA3, ?_⟩
    -- gap parameter
    unfold gapParameter actualSchurGapParameter38
    rw [← hxdef]
    set P := freeResolventComplementaryInverseUniformConstant22 ^ 2 *
      freeResolventSchurUniformConstant ^ 2 with hP
    have hP0 : 0 ≤ P := by positivity
    rw [abs_of_nonneg hP0] at hA5
    rw [div_le_iff₀ (by positivity)]
    have h4 : (4 * R) ^ 4 = 256 * R ^ 4 := by ring
    rw [h4]
    have hPR : 512 * P * R ^ 6 ≤ schurAllThreshold * R ^ 6 :=
      mul_le_mul_of_nonneg_right hA5 hR6'
    have hxx : 512 * x ≤ x * x := by nlinarith
    have hPR4 : P * R ^ 4 ≤ P * R ^ 6 := mul_le_mul_of_nonneg_left h46 hP0
    have hPx : 512 * (P * R ^ 6) ≤ x := by nlinarith
    have hPx2 : 512 * (512 * (P * R ^ 6)) ≤ x * x := by nlinarith [mul_nonneg hP0 hR6']
    nlinarith [mul_nonneg hP0 hR6', mul_nonneg hP0 (by positivity : (0:ℝ) ≤ R ^ 4)]

end NlsGge.ThirdConsultation.S

end
