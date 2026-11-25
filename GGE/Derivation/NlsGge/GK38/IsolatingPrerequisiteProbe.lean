import NlsGge.GK38.IsolatingGeometry
import NlsGge.GK38.IsolatingCounting

/-! Independent algebraic instances of disc distance and exact lattice geometry,
plus a genuinely prescribed actual common four-count cutoff. -/
set_option autoImplicit false
open Filter Topology Set Metric
namespace NlsGge.GK38
noncomputable section

theorem isolating_distance_probe38 :
    ballDistance38 (0 : ℂ) 4 1 1 = 2 ∧ ballDistance38 (0 : ℂ) 1 1 1 = 0 ∧
      ballDistance38 (0 : ℂ) 2 1 1 = 0 := by
  simp only [ballDistance38_eq _ _ (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1)]
  norm_num [dist_eq_norm]

theorem isolating_touching_open_probe38 :
    Disjoint (ball (0 : ℂ) 1) (ball (2 : ℂ) 1) ∧ ballDistance38 (0 : ℂ) 2 1 1 = 0 := by
  refine ⟨?_, isolating_distance_probe38.2.2⟩
  apply Set.disjoint_left.mpr
  intro z hz₀ hz₂
  have ht := dist_triangle (0 : ℂ) z 2
  have h0 : dist (0 : ℂ) z < 1 := by simpa only [dist_comm] using mem_ball.mp hz₀
  have h2 : dist z (2 : ℂ) < 1 := mem_ball.mp hz₂
  norm_num [dist_eq_norm] at ht
  rw [dist_eq_norm, zero_sub, norm_neg] at h0
  rw [dist_eq_norm] at h2
  linarith

theorem isolating_lattice_geometry_probe38 :
    ∃ c : ℝ, IsolatingGeometry38 countingCenter38 (fun _ => Real.pi / 4) c 0 := by
  apply tail_comparable_geometry38
  · intro n
    exact ⟨by positivity, by simp [countingCenter38]⟩
  · intro m n hmn
    change (countingCenter38 m).re < (countingCenter38 n).re
    rw [countingCenter_re38, countingCenter_re38]
    exact mul_lt_mul_of_pos_right (by exact_mod_cast hmn) Real.pi_pos
  · intro m n hmn
    have h := countingCenter_separated38 hmn
    rw [dist_eq_norm]
    nlinarith [Real.pi_pos]
  · intro n _
    exact ⟨rfl, rfl⟩

theorem isolating_prescribed_free_count_probe38 :
    ∃ N : ℕ, 137 ≤ N ∧ RootCountingAt38 (perChar 0) 2 N ∧
      RootCountingAt38 (deriv (discrim 0)) 1 N ∧ RootCountingAt38 (dirichletChar 0) 1 N ∧
      RootCountingAt38 (neumannChar38 0) 1 N := by
  obtain ⟨U, hU, N, hN, h⟩ := prescribed_common_counting38 0 137
  exact ⟨N, hN, h 0 (mem_of_mem_nhds hU)⟩

end
end NlsGge.GK38
