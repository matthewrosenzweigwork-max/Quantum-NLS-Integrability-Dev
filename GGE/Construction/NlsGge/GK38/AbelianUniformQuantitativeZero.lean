import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
import Mathlib.Analysis.Complex.Basic

/-! A quantitative zero theorem with earned inverse norm control. The SAME
radius/error constants can be fixed before every index of a family. Actual
period-map residual/linearization estimates are separate realizations. -/
set_option autoImplicit false
open Set Metric
open scoped NNReal
namespace NlsGge.GK38.P6QuantitativeInverse
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem exists_unique_zero_of_uniform_inverse_bound
    (f : E → E) (e : E ≃L[ℂ] E) (b : E) (r B : ℝ) (c : ℝ≥0)
    (hr : 0 < r) (hB : 0 < B)
    (he : ‖(e.symm : E →L[ℂ] E)‖ ≤ B) (hc : (c : ℝ) < B⁻¹)
    (hf : ApproximatesLinearOn f (e : E →L[ℂ] E) (closedBall b r) c)
    (hres : ‖f b‖ ≤ (B⁻¹-(c : ℝ))*r) :
    ∃! x : E, x ∈ closedBall b r ∧ f x=0 := by
  rcases e.subsingleton_or_norm_symm_pos with hE | hN
  · let : Subsingleton E := hE
    exact ⟨b,⟨mem_closedBall_self hr.le,Subsingleton.elim _ _⟩,
      fun y _hy => Subsingleton.elim _ _⟩
  · let N : ℝ := ‖(e.symm : E →L[ℂ] E)‖
    have hNB : B⁻¹ ≤ N⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hN he
    have hcN : c < ‖(e.symm : E →L[ℂ] E)‖₊⁻¹ := by
      have hh : (c : ℝ) < N⁻¹ := hc.trans_le hNB
      exact_mod_cast hh
    have hreach : (0 : E) ∈ closedBall (f b) ((N⁻¹-(c : ℝ))*r) := by
      rw [mem_closedBall,dist_zero_left]
      exact hres.trans (mul_le_mul_of_nonneg_right (sub_le_sub hNB le_rfl) hr.le)
    obtain ⟨x,hx,hfx⟩ := hf.surjOn_closedBall_of_nonlinearRightInverse
      e.toNonlinearRightInverse hr.le (Subset.rfl) hreach
    refine ⟨x,⟨hx,hfx⟩,?_⟩
    intro y hy
    exact (hf.injOn (Or.inr hcN)) hy.1 hx (hy.2.trans hfx.symm)

theorem family_unique_zeros_with_common_radius {ι : Type*}
    (f : ι → E → E) (e : ι → E ≃L[ℂ] E) (b : ι → E)
    (r B : ℝ) (c : ℝ≥0) (hr : 0 < r) (hB : 0 < B)
    (he : ∀ i, ‖((e i).symm : E →L[ℂ] E)‖ ≤ B)
    (hc : (c : ℝ) < B⁻¹)
    (hf : ∀ i, ApproximatesLinearOn (f i) (e i : E →L[ℂ] E) (closedBall (b i) r) c)
    (hres : ∀ i, ‖f i (b i)‖ ≤ (B⁻¹-(c : ℝ))*r) :
    ∀ i, ∃! x : E, x ∈ closedBall (b i) r ∧ f i x=0 := by
  intro i
  exact exists_unique_zero_of_uniform_inverse_bound (f i) (e i) (b i) r B c
    hr hB (he i) hc (hf i) (hres i)

end
end NlsGge.GK38.P6QuantitativeInverse
