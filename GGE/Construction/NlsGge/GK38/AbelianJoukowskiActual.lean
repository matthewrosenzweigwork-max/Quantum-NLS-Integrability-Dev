import NlsGge.GK38.AbelianJoukowski

/-! Realization of the scalar Joukowski data by the ACTUAL standard root.
UNCOMPILED prospective source, retaining arbitrary complex unordered endpoints. -/
set_option autoImplicit false
open Set Metric
namespace NlsGge.GK38
noncomputable section

/-- All algebraic data, including the selected outside pole, are earned off the actual cut.
The distinct-endpoint split belongs ONLY to this scalar parametrization; collapse is to be
handled separately by ordinary Cauchy in the final root-average theorem. -/
theorem p2StdRoot_joukowski38 (a b z : ℂ) (hab : a ≠ b)
    (hz : z ∉ segment ℝ a b) :
    ∃ u : ℂ, 1 < ‖u‖ ∧
      z-(a+b)/2 = (((b-a)/2)/2)*(u+u⁻¹) ∧
      stdRoot38 ((a+b)/2) ((b-a)^2) z = (((b-a)/2)/2)*(u⁻¹-u) := by
  let w : ℂ := (a+b)/2-z
  let d : ℂ := (b-a)/2
  let q : ℂ := Complex.sqrt (1-d^2/w^2)
  have hw : w ≠ 0 := (stdRoot_slit38 a b z hz).1
  have hd : d ≠ 0 := div_ne_zero (sub_ne_zero.mpr hab.symm) (by norm_num)
  have hrad : 1-d^2/w^2 ∈ Complex.slitPlane := by
    convert (stdRoot_slit38 a b z hz).2 using 1
    dsimp [d,w]
    ring
  have hq : q^2=1-d^2/w^2 := Lib.sqrt_sq _
  have hqr : 0 < q.re := p2Sqrt_re_pos38 _ hrad
  have hroot : stdRoot38 ((a+b)/2) ((b-a)^2) z = w*q := by
    dsimp [stdRoot38,w,q,d]
    congr 2
    ring
  let u : ℂ := -w*(1+q)/d
  have hu : 1 < ‖u‖ := p2Joukowski_outside38 w d q hw hd hq hqr
  have hinv : u⁻¹=-w*(1-q)/d := by
    apply inv_eq_of_mul_eq_one_right
    dsimp [u]
    field_simp [hw,hd] at hq ⊢
    linear_combination -hq
  refine ⟨u,hu,?_,?_⟩
  · have hneg : z-(a+b)/2=-w := by dsimp [w]; ring
    rw [hneg]
    change -w = (d/2)*(u+u⁻¹)
    rw [hinv]
    dsimp [u]
    field_simp [hd]
    ring
  · rw [hroot]
    change w*q=(d/2)*(u⁻¹-u)
    rw [hinv]
    dsimp [u]
    field_simp [hd]
    ring

/-- Actual off-cut Joukowski data earn both unit-circle pole exclusions. -/
theorem p2Joukowski_poles38 {u : ℂ} (hu : 1 < ‖u‖) :
    u⁻¹ ∈ ball (0 : ℂ) 1 ∧ u ∉ closedBall (0 : ℂ) 1 ∧ u ≠ 0 := by
  have hpos : 0 < ‖u‖ := lt_trans zero_lt_one hu
  have hne : u ≠ 0 := norm_ne_zero_iff.mp hpos.ne'
  refine ⟨?_,?_,hne⟩
  · rw [mem_ball_zero_iff,norm_inv]
    exact (inv_lt_one₀ hpos).mpr hu
  · simpa only [mem_closedBall_zero_iff,not_le] using hu

/-- The cosine path is on the actual cut even when endpoints are complex and unordered. -/
theorem p2Cosine_mem_segment38 (a b : ℂ) (θ : ℝ) :
    (a+b)/2+((b-a)/2)*(Real.cos θ : ℂ) ∈ segment ℝ a b := by
  rw [segment_eq_image ℝ a b]
  refine ⟨(1+Real.cos θ)/2,⟨by linarith [Real.neg_one_le_cos θ],
    by linarith [Real.cos_le_one θ]⟩,?_⟩
  simp only [Complex.real_smul]
  push_cast
  ring

#print axioms p2StdRoot_joukowski38
#print axioms p2Joukowski_poles38
#print axioms p2Cosine_mem_segment38
end
end NlsGge.GK38
