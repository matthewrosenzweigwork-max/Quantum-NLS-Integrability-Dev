import NlsGge.GK38.ContourAction

/-! Shrink a single contour inside its old full-family ball, retaining every other cut. -/
set_option autoImplicit false
open Set Metric Filter Topology MeasureTheory NlsGge.GK38
namespace NlsGge.GK38.ActionRadial
noncomputable section

theorem radial_sphere_subset (φ : PotPair) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hf : IsolatingFamily38 φ C R) (n : ℤ) (r ρ : ℝ)
    (hrρ : r ≤ ρ) (hρR : ρ ≤ R n)
    (hown : segment ℝ (lamMinus φ n) (lamPlus φ n) ⊆ ball (C n) r) :
    sphere (C n) ρ ⊆ actionCutDomain38 φ := by
  intro z hz
  change z ∉ gapSegments38 φ
  intro hall
  obtain ⟨m, hzm⟩ := mem_iUnion.mp hall
  obtain ⟨c, N, hg, hs⟩ := hf
  by_cases hmn : m = n
  · subst m
    have ho := mem_ball.mp (hown hzm)
    rw [mem_sphere.mp hz] at ho
    exact (not_lt_of_ge hrρ) ho
  · have hsep := isolating_geometry_closure_separated38 C R c N hg n m (Ne.symm hmn)
    have hzn : dist (C n) z ≤ R n := by
      rw [dist_comm]
      exact (mem_sphere.mp hz).trans_le hρR
    have hzm' : dist z (C m) < R m := mem_ball.mp ((hs.1 m).1 hzm)
    have htri := dist_triangle (C n) z (C m)
    linarith

end
end NlsGge.GK38.ActionRadial
