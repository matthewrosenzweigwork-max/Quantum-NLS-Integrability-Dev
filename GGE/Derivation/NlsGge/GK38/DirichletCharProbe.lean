import NlsGge.GK38.DirichletNilpotentProbe
import NlsGge.GK38.DirichletTriangularModel

/-! # D1: free sign, zero mode, off-lattice and repeated-root regressions -/
set_option autoImplicit false
open Filter Topology SummationFilter Set
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem dirichlet_probe_free38 :
    (∀ z : ℂ, dirichletChar 0 z = Complex.sin z) ∧
    (∀ n : ℤ, muSeq 0 n = countingCenter38 n) ∧
    muSeq 0 (-1) = -(Real.pi : ℂ) ∧
      normalizedDirichletProduct38 0 ((Real.pi / 2 : ℝ) : ℂ) = 1 := by
  refine ⟨dirichletChar_zero, muSeq_zero38, ?_, ?_⟩
  · simp [muSeq_zero38, countingCenter38]
  · change -(∏'[symmetricIcc ℤ] m : ℤ,
      (muSeq 0 m - ((Real.pi / 2 : ℝ) : ℂ)) / (πn m : ℂ)) = 1
    rw [← dirichletChar_product, dirichletChar_zero, ← Complex.ofReal_sin, Real.sin_pi_div_two]
    norm_num

theorem dirichlet_probe_zero_mode38 :
    (πn 0 : ℂ) = 1 ∧ (muSeq 0 0 - 0) / (πn 0 : ℂ) = 0 ∧
      Multipliable (fun m : ℤ => (muSeq 0 m - 0) / (πn m : ℂ)) (symmetricIcc ℤ) := by
  exact ⟨by simp [πn_zero], by simp [muSeq_zero38, countingCenter38], dirichletChar_multipliable 0 0⟩

/-- The nilpotent real constant has an actual root off every free lattice position. -/
theorem dirichlet_probe_nonfree_constant38 :
    dirichletChar (realSlice (constL2 1)) 1 = 0 ∧
    (∀ n : ℤ, (1 : ℂ) ≠ countingCenter38 n) ∧
      ∃ n : ℤ, muSeq (realSlice (constL2 1)) n = 1 := by
  refine ⟨dirichlet_nonfree_constant_root38, ?_,
    ((muSeq_enumeration38 _).2.1 1).mp dirichlet_nonfree_constant_root38⟩
  intro n hn
  by_cases hz : n = 0
  · simpa [hz, countingCenter38] using hn
  · have hab : (1 : ℤ) ≤ |n| := by
      have hh := abs_pos.mpr hz
      omega
    have hr : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast hab
    have hnorm : ‖countingCenter38 n‖ = 1 := by rw [← hn]; norm_num
    rw [norm_countingCenter38] at hnorm
    nlinarith [Real.pi_gt_three]

theorem dirichlet_triangle_pi_occurrences38 :
    {n : ℤ | dirichletTriangleSeq38 n = (Real.pi : ℂ)} = {0, 1} := by
  ext n
  rw [Set.mem_setOf_eq, dirichlet_triangle_seq_eq38]
  by_cases hn : n = 0
  · simp [hn]
  · have hc : countingCenter38 n = (Real.pi : ℂ) ↔ n = 1 := by
      constructor
      · intro h
        apply countingCenter_injective38
        simpa [countingCenter38] using h
      · rintro rfl
        simp [countingCenter38]
    simp [hn, hc]

/-- A central double root really occupies both canonical positions, with exact analytic order. -/
theorem dirichlet_probe_repeated38 :
    let φ : PotPair := (constL2 (2 * (Real.pi : ℂ)), 0)
    dirichletChar φ 0 = -(Real.pi : ℂ) ∧ dirichletChar φ (Real.pi : ℂ) = 0 ∧
      analyticOrderAt (dirichletChar φ) (Real.pi : ℂ) = 2 ∧
      muSeq φ 0 = (Real.pi : ℂ) ∧ muSeq φ 1 = (Real.pi : ℂ) ∧
        Set.encard {n : ℤ | muSeq φ n = (Real.pi : ℂ)} = 2 := by
  let φ : PotPair := (constL2 (2 * (Real.pi : ℂ)), 0)
  have hz : dirichletChar φ 0 = -(Real.pi : ℂ) := by
    rw [dirichlet_triangle_zero38]
    ring
  have hroot : dirichletChar φ (Real.pi : ℂ) = 0 := by
    rw [dirichlet_triangle_nonzero38 _ _ (by exact_mod_cast Real.pi_ne_zero)]
    simp
  have ho : analyticOrderAt (dirichletChar φ) (Real.pi : ℂ) = 2 := by
    rw [dirichlet_triangle_model_order38, dirichlet_triangle_pi_occurrences38]
    rw [Set.encard_insert_of_notMem (by simp), Set.encard_singleton]
    norm_num
  have h := canonicalDirichletCutoff_spec38 φ
  have hpos := h.1
  have hm0 := dirichlet_triangle_central_labels38 h 0 (by constructor <;> omega)
  have hm1 := dirichlet_triangle_central_labels38 h 1 (by constructor <;> omega)
  simp only [dirichlet_triangle_seq_eq38, ite_eq_left rfl] at hm0
  simp only [dirichlet_triangle_seq_eq38, show ¬ ((1 : ℤ) = 0) from by decide,
    ite_eq_right, countingCenter38, Int.cast_one, one_mul] at hm1
  exact ⟨hz, hroot, ho, hm0, hm1, (muSeq_occurrence38 φ (Real.pi : ℂ)).2.trans ho⟩

end
end NlsGge.GK38
