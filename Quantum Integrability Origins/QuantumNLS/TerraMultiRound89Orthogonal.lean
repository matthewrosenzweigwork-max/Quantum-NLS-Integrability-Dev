import QuantumNLS.TerraMultiRound88Pure
import QuantumNLS.EnergyProjection

/-! Orthogonal projection normalization with the exact pure-state cost. The
actual spectral Markov defect bound remains a separate physical obligation. -/
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
namespace QuantumNLS.TerraMultiRound89Orthogonal
attribute [local instance] InnerProductSpace.complexToReal

/-- A selfadjoint idempotent with a unit vector whose discarded part has norm
less than one yields a nonzero normalized vector in its range. -/
theorem normalized_orthogonal_projection {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (P : H →L[ℂ] H)
    (hP : P * P = P) (hsa : ContinuousLinearMap.adjoint P = P)
    (v : H) (hv : ‖v‖ = 1) (hdef : ‖v - P v‖ < 1) :
    let w := (‖P v‖⁻¹ : ℝ) • P v
    ‖w‖ = 1 ∧ P w = w ∧
      TraceClass.traceNorm (InnerProductSpace.rankOne ℂ v v -
        InnerProductSpace.rankOne ℂ w w) = ENNReal.ofReal (2 * ‖v - P v‖) := by
  have hid : P (P v) = P v := congrArg (fun Q : H →L[ℂ] H => Q v) hP
  have hip : ⟪v, P v⟫_ℂ = ((‖P v‖ ^ 2 : ℝ) : ℂ) := by
    calc
      ⟪v, P v⟫_ℂ = ⟪v, P (P v)⟫_ℂ := by rw [hid]
      _ = ⟪(ContinuousLinearMap.adjoint P) v, P v⟫_ℂ := by
        rw [ContinuousLinearMap.adjoint_inner_left]
      _ = ((‖P v‖ ^ 2 : ℝ) : ℂ) := by
        rw [hsa, inner_self_eq_norm_sq_to_K]
        push_cast
        rfl
  have hc : ((‖P v‖ ^ 2 : ℝ) : ℂ) = ((‖P v‖ : ℂ) ^ 2) := by
    push_cast
    rfl
  have hor : ⟪v - P v, P v⟫_ℝ = 0 := by
    rw [real_inner_eq_re_inner ℂ, RCLike.re_to_complex, inner_sub_left,
      hip, inner_self_eq_norm_sq_to_K, hc]
    simp
  have hpyth : ‖v‖ ^ 2 = ‖P v‖ ^ 2 + ‖v - P v‖ ^ 2 := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_real hor
    rw [sub_add_cancel] at h
    linarith
  have hp : 0 < ‖P v‖ := by
    by_contra hn
    have hz : P v = 0 := norm_eq_zero.mp (le_antisymm (le_of_not_gt hn) (norm_nonneg _))
    rw [hz, sub_zero, hv] at hdef
    exact (lt_irrefl 1) hdef
  have hn := (TerraMultiRound87Normalize.normalize_projection v (P v) hv hp hpyth).1
  refine ⟨hn, ?_, TerraMultiRound88Pure.normalized_projection_trace v (P v) hv hp hpyth hip⟩
  have hs : (‖P v‖⁻¹ : ℝ) • P v = (((‖P v‖⁻¹ : ℝ) : ℂ) • P v) :=
    (Complex.coe_smul (‖P v‖⁻¹ : ℝ) (P v)).symm
  rw [hs, map_smul, hid]

#print axioms normalized_orthogonal_projection
end QuantumNLS.TerraMultiRound89Orthogonal
