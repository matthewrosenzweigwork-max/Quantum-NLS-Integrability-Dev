import NlsGge.GK38.GradEigenDefs

/-! # H181 supporting module (b): bounded bilinearity of mixedSquare on PairKernelCont38.
`mixedSquare v w` (GK38/GradEigenDefs.lean) is pointwise `starProd38 (v t) (w t)`, which is
bilinear in (v t, w t). This module packages it as the continuous ℂ-bilinear map `mixedSquareBL`
with bound `‖mixedSquare v w‖ ≤ ‖v‖ * ‖w‖` (sup norms). No hypotheses are added; bilinearity and
the norm bound are proved from the coordinatewise formula of starProd38. -/
set_option autoImplicit false
open NlsGge.GK38
namespace NlsGge.GK38.GradEigen38
noncomputable section

theorem starProd38_add_left (g g' h : PairVec38) :
    starProd38 (g + g') h = starProd38 g h + starProd38 g' h := by
  ext i; fin_cases i <;> simp [starProd38, add_mul]

theorem starProd38_add_right (g h h' : PairVec38) :
    starProd38 g (h + h') = starProd38 g h + starProd38 g h' := by
  ext i; fin_cases i <;> simp [starProd38, mul_add]

theorem starProd38_smul_left (c : ℂ) (g h : PairVec38) :
    starProd38 (c • g) h = c • starProd38 g h := by
  ext i; fin_cases i <;> simp [starProd38] <;> ring

theorem starProd38_smul_right (c : ℂ) (g h : PairVec38) :
    starProd38 g (c • h) = c • starProd38 g h := by
  ext i; fin_cases i <;> simp [starProd38] <;> ring

theorem norm_starProd38_le (g h : PairVec38) : ‖starProd38 g h‖ ≤ ‖g‖ * ‖h‖ := by
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 ?_
  refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
  · show ‖g 1 * h 1‖ ≤ ‖g‖ * ‖h‖
    rw [norm_mul]
    exact mul_le_mul (norm_le_pi_norm g 1) (norm_le_pi_norm h 1) (norm_nonneg _) (norm_nonneg _)
  · show ‖g 0 * h 0‖ ≤ ‖g‖ * ‖h‖
    rw [norm_mul]
    exact mul_le_mul (norm_le_pi_norm g 0) (norm_le_pi_norm h 0) (norm_nonneg _) (norm_nonneg _)

theorem mixedSquare_add_left (v v' w : PairKernelCont38) :
    mixedSquare (v + v') w = mixedSquare v w + mixedSquare v' w :=
  ContinuousMap.ext fun t => starProd38_add_left (v t) (v' t) (w t)

theorem mixedSquare_add_right (v w w' : PairKernelCont38) :
    mixedSquare v (w + w') = mixedSquare v w + mixedSquare v w' :=
  ContinuousMap.ext fun t => starProd38_add_right (v t) (w t) (w' t)

theorem mixedSquare_smul_left (c : ℂ) (v w : PairKernelCont38) :
    mixedSquare (c • v) w = c • mixedSquare v w :=
  ContinuousMap.ext fun t => starProd38_smul_left c (v t) (w t)

theorem mixedSquare_smul_right (c : ℂ) (v w : PairKernelCont38) :
    mixedSquare v (c • w) = c • mixedSquare v w :=
  ContinuousMap.ext fun t => starProd38_smul_right c (v t) (w t)

theorem norm_mixedSquare_le (v w : PairKernelCont38) : ‖mixedSquare v w‖ ≤ ‖v‖ * ‖w‖ := by
  refine (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 fun t => ?_
  exact (norm_starProd38_le (v t) (w t)).trans
    (mul_le_mul (v.norm_coe_le_norm t) (w.norm_coe_le_norm t) (norm_nonneg _) (norm_nonneg _))

/-- `mixedSquare` as a ℂ-bilinear map (algebraic form). -/
def mixedSquareLM : PairKernelCont38 →ₗ[ℂ] PairKernelCont38 →ₗ[ℂ] PairKernelCont38 :=
  LinearMap.mk₂ ℂ mixedSquare mixedSquare_add_left mixedSquare_smul_left
    mixedSquare_add_right mixedSquare_smul_right

/-- `mixedSquare` as a bounded ℂ-bilinear map on the sup-norm space of pair kernels. -/
def mixedSquareBL : PairKernelCont38 →L[ℂ] PairKernelCont38 →L[ℂ] PairKernelCont38 :=
  LinearMap.mkContinuous₂ mixedSquareLM 1 (fun v w => by
    rw [one_mul]
    exact norm_mixedSquare_le v w)

@[simp] theorem mixedSquareBL_apply (v w : PairKernelCont38) :
    mixedSquareBL v w = mixedSquare v w := rfl

theorem norm_mixedSquareBL_le (v w : PairKernelCont38) :
    ‖mixedSquareBL v w‖ ≤ ‖v‖ * ‖w‖ :=
  norm_mixedSquare_le v w

end
end NlsGge.GK38.GradEigen38
