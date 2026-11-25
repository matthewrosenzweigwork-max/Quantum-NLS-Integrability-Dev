import NlsGge.GK38.Lib.EntireProductsParama

/-! A genuine DIAGONAL continuous linear equivalence gives a positive
coefficient lower bound through its actual diagonal action. The corresponding
claim for a general invertible full matrix would be false. -/
set_option autoImplicit false
namespace NlsGge.GK38
noncomputable section

theorem angleReal_diagonal_equiv_lower38 {ι : Type*}
    (D : lp (fun _ : ι => ℝ) 2 ≃L[ℝ] lp (fun _ : ι => ℝ) 2)
    (d : ι → ℝ)
    (hD : ∀ (v : lp (fun _ : ι => ℝ) 2) (i : ι), D v i=d i*v i) :
    ∃ c : ℝ, 0 < c ∧ ∀ i : ι, c ≤ ‖d i‖ := by
  classical
  let B : ℝ := ‖D.symm.toContinuousLinearMap‖+1
  have hB : 0 < B := add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one
  refine ⟨B⁻¹,inv_pos.mpr hB,?_⟩
  intro i
  let e : lp (fun _ : ι => ℝ) 2 := lp.single 2 i (1 : ℝ)
  have he : ‖e‖=1 := by
    simpa only [e,norm_one] using lp.norm_single (E := fun _ : ι => ℝ) (by norm_num : (0 : ENNReal)<2) i (1 : ℝ)
  have himage : D e=lp.single 2 i (d i) := by
    apply Subtype.ext
    funext j
    rw [hD]
    by_cases hj : j=i
    · subst j
      simp only [e,lp.single_apply_self,mul_one]
    · simp only [e,lp.single_apply_ne (E := fun _ : ι => ℝ) 2 i (1 : ℝ) hj,
        lp.single_apply_ne (E := fun _ : ι => ℝ) 2 i (d i) hj,mul_zero]
  have himagenorm : ‖D e‖=‖d i‖ := by
    rw [himage,lp.norm_single (by norm_num : (0 : ENNReal)<2)]
  have hrev : 1 ≤ ‖D.symm.toContinuousLinearMap‖*‖d i‖ := by
    have h := D.symm.toContinuousLinearMap.le_opNorm (D e)
    simpa only [ContinuousLinearEquiv.coe_coe,D.symm_apply_apply,he,himagenorm] using h
  have hmul : 1 ≤ B*‖d i‖ := hrev.trans
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (norm_nonneg _))
  exact (inv_le_iff_one_le_mul₀' hB).mpr hmul

end
end NlsGge.GK38
