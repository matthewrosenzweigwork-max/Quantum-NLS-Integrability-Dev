import NlsGge.GK38.PoissonDirichletTargets
import NlsGge.GK38.GradEigenStateODE
import NlsGge.GK38.GradFundamentalStar

/-! Actual rough-state Wronskian identity for canonical Dirichlet states. -/
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.GK38 NlsGge.GK38.GradEigen38
namespace NlsGge.GK38.PoissonDirichlet38
noncomputable section

theorem dirState_isPairSolution38 (φ : PotPair) (z : ℂ) :
    IsPairSolution38 φ z (pairKernelExt38 (state φ z ![1,1])) :=
  ⟨ac_state_component φ z ![1,1], ae_hasDerivAt_state_component φ z ![1,1]⟩

theorem dirState_terminal38 (φ : PotPair) (z : ℂ)
    (hz : dirichletChar φ z = 0) :
    state φ z ![1,1] t1 0 = state φ z ![1,1] t1 1 := by
  have hb := dirichlet_boundary_sum φ z hz
  rw [state_eq_mulVec]
  change (monodromyPair φ z).mulVec ![1,1] 0 = (monodromyPair φ z).mulVec ![1,1] 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, mul_one]
  linear_combination -hb

theorem dirState_endpointBracket38 (φ : PotPair) (z w : ℂ)
    (hz : dirichletChar φ z = 0) (hw : dirichletChar φ w = 0) :
    pairBracket38 (pairKernelExt38 (state φ z ![1,1]) 0)
        (pairKernelExt38 (state φ w ![1,1]) 0) = 0 ∧
    pairBracket38 (pairKernelExt38 (state φ z ![1,1]) 1)
        (pairKernelExt38 (state φ w ![1,1]) 1) = 0 := by
  constructor
  · rw [pairKernelExt38_of_mem _ (show (0 : ℝ) ∈ Icc 0 1 from ⟨le_rfl,zero_le_one⟩),
      pairKernelExt38_of_mem _ (show (0 : ℝ) ∈ Icc 0 1 from ⟨le_rfl,zero_le_one⟩)]
    change pairBracket38 (state φ z ![1,1] t0) (state φ w ![1,1] t0) = 0
    simp [state_initial,pairBracket38]
  · rw [pairKernelExt38_of_mem _ (show (1 : ℝ) ∈ Icc 0 1 from ⟨zero_le_one,le_rfl⟩),
      pairKernelExt38_of_mem _ (show (1 : ℝ) ∈ Icc 0 1 from ⟨zero_le_one,le_rfl⟩)]
    change pairBracket38 (state φ z ![1,1] t1) (state φ w ![1,1] t1) = 0
    unfold pairBracket38
    rw [dirState_terminal38 φ z hz, dirState_terminal38 φ w hw]
    ring

theorem integral_dirState_starBracket38_eq_zero (φ : PotPair) (z w : ℂ)
    (hz : dirichletChar φ z = 0) (hw : dirichletChar φ w = 0) :
    (∫ s in (0 : ℝ)..1,
      pairBracket38
        (starProd38 (pairKernelExt38 (state φ z ![1,1]) s)
          (pairKernelExt38 (state φ z ![1,1]) s))
        (starProd38 (pairKernelExt38 (state φ w ![1,1]) s)
          (pairKernelExt38 (state φ w ![1,1]) s))) = 0 := by
  have ha := dirState_isPairSolution38 φ z
  have hb := dirState_isPairSolution38 φ w
  have _hi := intervalIntegrable_starBracket38 ha hb ha hb
  by_cases hzw : z = w
  · subst w
    have he (v : PairVec38) : pairBracket38 v v = 0 := by
      unfold pairBracket38
      ring
    simp only [he, intervalIntegral.integral_zero]
  · have h := integrated_starIdentity38 ha hb ha hb ⟨1,zero_le_one,le_rfl⟩
    obtain ⟨h0,h1⟩ := dirState_endpointBracket38 φ z w hz hw
    simp only [h0,h1,mul_zero,sub_zero] at h
    have hc : 2 * Complex.I * (z-w) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) (sub_ne_zero.mpr hzw)
    exact (mul_eq_zero.mp h.symm).resolve_left hc

end
end NlsGge.GK38.PoissonDirichlet38
