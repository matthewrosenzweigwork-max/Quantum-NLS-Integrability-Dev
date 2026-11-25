import QuantumNLS.TerraMultiRound41ScalarAgreement

/-! The zero-field branch of the REG-005 solution identification.
The nonzero branch and the all-order signed expansion remain separate. -/
set_option autoImplicit false
noncomputable section
open Complex
namespace QuantumNLS.TerraMultiRound42ZeroField
open QuantumNLS.PhysicalTensor QuantumNLS.RiccatiSobolevBanach
open QuantumNLS.ComplexifiedSobolevField QuantumNLS.TerraMultiRound39PhysicalBall
open QuantumNLS.TerraMultiRound38SignedPicard QuantumNLS.RootH1RatioBounds

/-- The independently constructed physical L² ratio is zero for zero input. -/
theorem ratioL2_zero {L Y κ : ℝ} [Fact (0 < L)] (hY : 0 < Y)
    (hlog : Real.log 3 ≤ Y * L) (hκ : 0 ≤ κ)
    (hsmall : 16 * κ * ‖(0 : L2T L)‖ ^ 2 ≤ Y) :
    ratioL2 hY hlog hκ (0 : L2T L) hsmall = 0 := by
  apply norm_eq_zero.mp
  have h := ratioL2_norm hY hlog hκ (0 : L2T L) hsmall
  simpa using h

/-- In the exact Fourier ball at zero input, the signed fixed point is zero,
whose physical field agrees with the separately constructed L² ratio. -/
theorem zero_field_solution_agreement {L a Y κ : ℝ} [hLf : Fact (0 < L)]
    (ha : 1 / 2 < a) (hY : 0 < Y) (hlog : Real.log 3 ≤ Y * L)
    (hκ : 0 ≤ κ) (hsmall : 16 * κ * ‖(0 : L2T L)‖ ^ 2 ≤ Y)
    (r : Ell2) (hr : ‖r‖ ≤ 2 * ‖(0 : Ell2)‖ / |Y|) :
    r = 0 ∧ physicalT hLf.out ha (abs_pos.mpr hY.ne') κ 0 r = r ∧
    fieldMap L a (by linarith : (0 : ℝ) ≤ a) r =
      ratioL2 hY hlog hκ (0 : L2T L) hsmall := by
  have hz : r = 0 := norm_eq_zero.mp (by simpa using hr)
  subst r
  refine ⟨rfl, ?_, ?_⟩
  · simp [physicalT, signedT]
  · rw [ratioL2_zero hY hlog hκ hsmall]
    exact map_zero _

#print axioms ratioL2_zero
#print axioms zero_field_solution_agreement
end QuantumNLS.TerraMultiRound42ZeroField
