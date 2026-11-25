import NlsGge.Ramer.FiniteGaussian

/-!
# Chain rule for the finite Ramer density (R9a item 3)

`finiteRamerDensity (T₂ ∘ T₁) v = finiteRamerDensity T₂ (T₁ v) * finiteRamerDensity T₁ v`
for `T₁` differentiable at `v` and `T₂` differentiable at `T₁ v`.
-/

open Real

namespace NlsGge.Ramer

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem finiteRamerDensity_comp (T₁ T₂ : V → V) (v : V)
    (h₁ : DifferentiableAt ℝ T₁ v) (h₂ : DifferentiableAt ℝ T₂ (T₁ v)) :
    finiteRamerDensity (T₂ ∘ T₁) v = finiteRamerDensity T₂ (T₁ v) * finiteRamerDensity T₁ v := by
  unfold finiteRamerDensity
  rw [fderiv_comp v h₂ h₁, ContinuousLinearMap.det, ContinuousLinearMap.det,
    ContinuousLinearMap.det]
  have hc : (↑((fderiv ℝ T₂ (T₁ v)).comp (fderiv ℝ T₁ v)) : V →ₗ[ℝ] V)
      = (fderiv ℝ T₂ (T₁ v) : V →ₗ[ℝ] V) * (fderiv ℝ T₁ v : V →ₗ[ℝ] V) := rfl
  rw [hc, Module.End.mul_eq_comp, LinearMap.det_comp, abs_mul]
  have he : Real.exp (-(‖(T₂ ∘ T₁) v‖ ^ 2 - ‖v‖ ^ 2) / 2)
      = Real.exp (-(‖T₂ (T₁ v)‖ ^ 2 - ‖T₁ v‖ ^ 2) / 2) * Real.exp (-(‖T₁ v‖ ^ 2 - ‖v‖ ^ 2) / 2) := by
    rw [← Real.exp_add]; congr 1; simp only [Function.comp]; ring
  rw [he]; ring

theorem finiteRamerDensity_comp_of_differentiable (T₁ T₂ : V → V)
    (h₁ : Differentiable ℝ T₁) (h₂ : Differentiable ℝ T₂) (v : V) :
    finiteRamerDensity (T₂ ∘ T₁) v = finiteRamerDensity T₂ (T₁ v) * finiteRamerDensity T₁ v :=
  finiteRamerDensity_comp T₁ T₂ v (h₁ v) (h₂ _)

omit [FiniteDimensional ℝ V] in
theorem finiteRamerDensity_id_gen (v : V) : finiteRamerDensity (id : V → V) v = 1 := by
  unfold finiteRamerDensity
  have : (ContinuousLinearMap.id ℝ V).det = 1 := LinearMap.det_id
  simp [this]


end NlsGge.Ramer
