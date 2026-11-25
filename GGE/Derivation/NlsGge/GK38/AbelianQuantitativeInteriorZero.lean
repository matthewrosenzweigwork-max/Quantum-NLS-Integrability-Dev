import NlsGge.GK38.AbelianUniformQuantitativeZero

/-! A quantitative zero lies strictly inside the uniqueness ball when the
actual residual fits the half-radius image ball. No solution oracle. -/
set_option autoImplicit false
open Set Metric
open scoped NNReal
namespace NlsGge.GK38.P6QuantitativeInverse
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem exists_interior_zero_unique_on_closedBall
    (f : E → E) (e : E ≃L[ℂ] E) (b : E) (r B : ℝ) (c : ℝ≥0)
    (hr : 0 < r) (hB : 0 < B)
    (he : ‖(e.symm : E →L[ℂ] E)‖ ≤ B) (hc : (c : ℝ) < B⁻¹)
    (hf : ApproximatesLinearOn f (e : E →L[ℂ] E) (closedBall b r) c)
    (hres : ‖f b‖ ≤ (B⁻¹-(c : ℝ))*(r/2)) :
    ∃ x : E, x ∈ closedBall b (r/2) ∧ f x=0 ∧
      ∀ y ∈ closedBall b r, f y=0 → y=x := by
  have hhalf : r/2 ≤ r := by linarith
  obtain ⟨x,hx,_hhalfUnique⟩ := exists_unique_zero_of_uniform_inverse_bound
    f e b (r/2) B c (half_pos hr) hB he hc
    (hf.mono_set (closedBall_subset_closedBall hhalf)) hres
  have hfullres : ‖f b‖ ≤ (B⁻¹-(c : ℝ))*r :=
    hres.trans (mul_le_mul_of_nonneg_left hhalf (sub_pos.mpr hc).le)
  obtain ⟨z,_hz,hfullUnique⟩ := exists_unique_zero_of_uniform_inverse_bound
    f e b r B c hr hB he hc hf hfullres
  have hxfull : x ∈ closedBall b r := closedBall_subset_closedBall hhalf hx.1
  refine ⟨x,hx.1,hx.2,?_⟩
  intro y hy hfy
  exact (hfullUnique y ⟨hy,hfy⟩).trans (hfullUnique x ⟨hxfull,hx.2⟩).symm

end
end NlsGge.GK38.P6QuantitativeInverse
