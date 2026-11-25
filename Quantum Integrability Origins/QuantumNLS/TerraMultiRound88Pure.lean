import QuantumNLS.TerraMultiRound87Normalize
import QuantumNLS.RankTwoTrace

/-! The exact pure-state compression cost for an orthogonal component.
This is geometry only; the actual energy projection must still be bound. -/
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
namespace QuantumNLS.TerraMultiRound88Pure

/-- Normalizing a nonzero orthogonal component costs exactly twice the norm
of the discarded component in trace distance, avoiding the extra factor from
estimating the distance of the two vectors. -/
theorem normalized_projection_trace {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (v p : H) (hv : ‖v‖ = 1)
    (hp : 0 < ‖p‖) (hpyth : ‖v‖ ^ 2 = ‖p‖ ^ 2 + ‖v - p‖ ^ 2)
    (hip : ⟪v, p⟫_ℂ = ((‖p‖ ^ 2 : ℝ) : ℂ)) :
    TraceClass.traceNorm (InnerProductSpace.rankOne ℂ v v -
        InnerProductSpace.rankOne ℂ ((‖p‖⁻¹ : ℝ) • p) ((‖p‖⁻¹ : ℝ) • p)) =
      ENNReal.ofReal (2 * ‖v - p‖) := by
  have hn := (TerraMultiRound87Normalize.normalize_projection v p hv hp hpyth).1
  rw [RankTwoTrace.traceNorm_unit_sub_eq v _ hv hn]
  have hi : ‖⟪v, (‖p‖⁻¹ : ℝ) • p⟫_ℂ‖ = ‖p‖ := by
    have hs : (‖p‖⁻¹ : ℝ) • p = (((‖p‖⁻¹ : ℝ) : ℂ) • p) :=
      (Complex.coe_smul (‖p‖⁻¹ : ℝ) p).symm
    rw [hs, inner_smul_right, hip, norm_mul,
      Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr hp.le), abs_of_nonneg (sq_nonneg _)]
    field_simp
  rw [hi]
  have he : 1 - ‖p‖ ^ 2 = ‖v - p‖ ^ 2 := by nlinarith
  rw [he, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

#print axioms normalized_projection_trace
end QuantumNLS.TerraMultiRound88Pure
