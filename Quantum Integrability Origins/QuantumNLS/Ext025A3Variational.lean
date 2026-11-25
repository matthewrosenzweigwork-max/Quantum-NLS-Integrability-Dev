import QuantumNLS.Ext025A2ODE

/-! A variational equation is constructed as a Picard equation in the Banach
space of continuous linear maps. This does not assume or assert that the
solution map is differentiable: identifying its derivative with this
constructed solution remains a separate GP-04 clause. -/
set_option autoImplicit false
noncomputable section
open Set Metric Topology Filter ODE
open scoped NNReal
namespace QuantumNLS.Ext025A3
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Construct the operator-valued variational solution from a continuous,
uniformly bounded coefficient; its initial value is the identity operator. -/
theorem gp04_variational_existence {a b : ℝ} {t₀ : Icc a b}
    (A : ℝ → E →L[ℝ] E) (hA : ContinuousOn A (Icc a b)) (K : ℝ≥0)
    (hK : ∀ t ∈ Icc a b, ‖A t‖ ≤ K)
    (hT : (2 * (K : ℝ)) * max (b - t₀) (t₀ - a) ≤ 1) :
    ∃ J : ℝ → E →L[ℝ] E, Continuous J ∧ J t₀ = ContinuousLinearMap.id ℝ E ∧
      (∀ t ∈ Icc a b, J t = ContinuousLinearMap.id ℝ E + ∫ s in t₀..t, (A s).comp (J s)) ∧
      (∀ t ∈ Icc a b, HasDerivWithinAt J ((A t).comp (J t)) (Icc a b) t) := by
  let I : E →L[ℝ] E := ContinuousLinearMap.id ℝ E
  have hf : IsPicardLindelof (fun t (J : E →L[ℝ] E) => (A t).comp J)
      t₀ I 1 0 (2*K) K := by
    constructor
    · intro t ht
      apply LipschitzOnWith.of_dist_le_mul
      intro J hJ Q hQ
      rw [dist_eq_norm, dist_eq_norm, ← ContinuousLinearMap.comp_sub]
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right (hK t ht) (norm_nonneg _))
    · intro J hJ
      exact (Continuous.clm_comp_const continuous_id J).comp_continuousOn hA
    · intro t ht J hJ
      have hj : ‖J - I‖ ≤ 1 := by simpa only [mem_closedBall, dist_eq_norm, NNReal.coe_one] using hJ
      have hn : ‖J‖ ≤ 2 := by
        have h := norm_le_norm_sub_add J I
        have hi : ‖I‖ ≤ 1 := ContinuousLinearMap.norm_id_le
        linarith
      calc
        ‖(A t).comp J‖ ≤ ‖A t‖ * ‖J‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ K * 2 := mul_le_mul (hK t ht) hn (norm_nonneg _) K.property
        _ = ↑(2*K) := by push_cast; ring
    · simpa only [NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_one, NNReal.coe_zero,
        sub_zero] using hT
  obtain ⟨J, hc, hi, hm, he, hd⟩ := QuantumNLS.Ext025A2.gp04_differential_existence hf
    (show I ∈ closedBall I (0 : ℝ≥0) by simp)
  refine ⟨J, hc, hi, ?_, hd⟩
  intro t ht
  exact he t ht

end QuantumNLS.Ext025A3
#print axioms QuantumNLS.Ext025A3.gp04_variational_existence
