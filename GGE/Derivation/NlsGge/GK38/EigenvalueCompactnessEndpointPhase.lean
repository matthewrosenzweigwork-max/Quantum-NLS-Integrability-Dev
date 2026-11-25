import NlsGge.GK38.EigenvalueCompactnessPhaseRealization

/-! # S7: actual periodic eigen-directions give the signed endpoint phase -/
set_option autoImplicit false
open Set
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem eigenDirection_normalized_endpoint38 (u : PhysicalL2) (x : ℝ) (n : ℤ) (a : ℂ)
    (ha : EigenDirectionAt38 u x n a) :
    normalizedFirst38 u x a ⟨1, zero_le_one, le_rfl⟩ =
      (Real.cos ((n : ℝ) * Real.pi) : ℂ) := by
  have he := congrFun ha.2 0
  have hn := unit_direction_ne_zero38 a ha.1
  rw [monodromyPair_eq_fundPair] at he
  change (fundPair (realSlice u) (x : ℂ) ⟨1, zero_le_one, le_rfl⟩).mulVec (realInitial38 a) 0 / a = _
  rw [he]
  simp only [Pi.smul_apply, smul_eq_mul, realInitial38, Matrix.cons_val_zero]
  exact mul_div_cancel_right₀ _ hn

theorem eigenDirection_phase_exp38 (u : PhysicalL2) (x : ℝ) (n : ℤ) (a : ℂ)
    (ha : EigenDirectionAt38 u x n a) :
    Complex.exp (-Complex.I * (periodicPhase38 u x a 1 : ℂ)) =
      (Real.cos ((n : ℝ) * Real.pi) : ℂ) := by
  have he := (periodicPhase_realization38 u x a ha.1).2.2 ⟨1, zero_le_one, le_rfl⟩
  rw [eigenDirection_normalized_endpoint38 u x n a ha] at he
  have hn : ‖(Real.cos ((n : ℝ) * Real.pi) : ℂ)‖ = 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, Real.abs_cos_int_mul_pi]
  rw [hn, Complex.ofReal_one, div_one] at he
  exact he.2.symm

end
end NlsGge.GK38
