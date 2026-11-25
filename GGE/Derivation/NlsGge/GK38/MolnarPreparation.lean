import NlsGge.GK38.MolnarPreparationTargets

set_option autoImplicit false
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.SpectralFoundations
open NlsGge.HierarchyRiccati.Core NlsGge.GK38

namespace NlsGge.GK38

theorem massChargeAllSobolev38 : MassChargeAllSobolevTarget38 := by
  intro m hm y
  have hsob := sobolevToL2_38_sobolev m y
  have hH1 := sobolevSquareSummable_restrict 1 (m : ℝ)
    (by exact_mod_cast hm) _ hsob
  have hmass := actualGapHeight_integral_eq_normSq_E02_38 (sobolevToL2_38 m y) hH1
  have hmoment := moment_integrable_charge38 m hm (sobolevToL2_38 m y) y
    (fun n => (sobolevToL2_38_fourier m y n).symm) 0 (Nat.zero_le m)
  have hvalue := hmoment.2
  simp only [Nat.mul_zero, pow_zero, one_mul] at hvalue
  exact hvalue.symm.trans hmass.2

theorem molnarWeight_le_japanese38 (m : ℕ) (n : ℤ) :
    (1 + |2 * Real.pi * (n : ℝ)|) ^ (2 * m) ≤
      (1 + 2 * Real.pi) ^ (2 * m) * japaneseBracket n ^ (2 * m) := by
  have hfreq : 0 ≤ 2 * Real.pi := by positivity
  have hbase : 1 + |2 * Real.pi * (n : ℝ)| ≤
      (1 + 2 * Real.pi) * japaneseBracket n := by
    rw [abs_mul, abs_of_nonneg hfreq]
    calc
      1 + (2 * Real.pi) * |(n : ℝ)| ≤
          1 + (2 * Real.pi) * japaneseBracket n :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (abs_le_japaneseBracket38 n) hfreq)
      _ ≤ japaneseBracket n + (2 * Real.pi) * japaneseBracket n :=
        add_le_add (japaneseBracket_one_le n) le_rfl
      _ = (1 + 2 * Real.pi) * japaneseBracket n := by ring
  calc
    (1 + |2 * Real.pi * (n : ℝ)|) ^ (2 * m) ≤
        ((1 + 2 * Real.pi) * japaneseBracket n) ^ (2 * m) :=
      pow_le_pow_left₀ (by positivity) hbase _
    _ = _ := mul_pow _ _ _

theorem molnarActionSummability38 : MolnarActionSummabilityTarget38 := by
  intro m hm u hu
  refine ((summable_bracket_action38 m hm u hu).mul_left
    ((1 + 2 * Real.pi) ^ (2 * m))).of_nonneg_of_le
      (fun n => mul_nonneg (by positivity) (actualGapAction_nonneg_F04_38 u n))
      (fun n => ?_)
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (molnarWeight_le_japanese38 m n)
    (actualGapAction_nonneg_F04_38 u n)

end NlsGge.GK38
