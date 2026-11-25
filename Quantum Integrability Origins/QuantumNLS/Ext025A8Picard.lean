import QuantumNLS.Ext025A2ODE

/-! Uniform Picard slabs from actual value and Lipschitz bounds on a larger
ball. The unit sphere need not be compact. -/
set_option autoImplicit false
noncomputable section
open Set Metric
open scoped NNReal
namespace QuantumNLS.Ext025A8
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem bounded_ball_picard {f : E → E} {S : ℝ} (hS : 1 < S) {M K : ℝ≥0}
    (hM : ∀ x ∈ closedBall (0 : E) S, ‖f x‖ ≤ M)
    (hK : LipschitzOnWith K f (closedBall (0 : E) S)) :
    ∃ δ > (0 : ℝ), ∀ u : E, ‖u‖ ≤ 1 → ∀ b : ℝ,
      ∃ α : ℝ → E, Continuous α ∧ α b = u ∧
        (∀ t, α t ∈ closedBall (0 : E) S) ∧
        (∀ t ∈ Ioo (b - δ) (b + δ), HasDerivAt α (f (α t)) t) := by
  let r : ℝ≥0 := ⟨S - 1, sub_nonneg.mpr hS.le⟩
  let δ : ℝ := (S - 1) / ((M : ℝ) + 1)
  have hδ : 0 < δ := div_pos (sub_pos.mpr hS) (by positivity)
  refine ⟨δ, hδ, fun u hu b => ?_⟩
  have hsub : closedBall u (r : ℝ) ⊆ closedBall (0 : E) S := by
    intro x hx
    rw [mem_closedBall_zero_iff]
    have hx' : ‖x - u‖ ≤ S - 1 := mem_closedBall_iff_norm.mp hx
    have ht := norm_add_le (x - u) u
    rw [sub_add_cancel] at ht
    linarith
  have hPL : IsPicardLindelof (fun _ : ℝ => f)
      (tmin := b - δ) (tmax := b + δ) ⟨b, by constructor <;> linarith⟩ u r 0 M K := by
    refine ⟨fun _ _ => hK.mono hsub, fun _ _ => continuousOn_const,
      fun _ _ x hx => hM x (hsub hx), ?_⟩
    simp only [add_sub_cancel_left, sub_sub_cancel, max_self, NNReal.coe_zero, sub_zero]
    change (M : ℝ) * δ ≤ S - 1
    dsimp only [δ]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < (M : ℝ) + 1)).mpr
    nlinarith [sub_pos.mpr hS]
  obtain ⟨α, hc, hb, hm, _, hd⟩ := QuantumNLS.Ext025A2.gp04_differential_existence hPL
    (show u ∈ closedBall u (0 : ℝ≥0) by simp)
  exact ⟨α, hc, hb, fun t => hsub (hm t), fun t ht =>
    (hd t ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)⟩
end QuantumNLS.Ext025A8

#print axioms QuantumNLS.Ext025A8.bounded_ball_picard
