import NlsGge.GK38.PoissonMixedCalibration

set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.GK38 NlsGge.GK38.GradEigen38 NlsGge.GK38.PoissonDirichlet38
namespace NlsGge.GK38.PoissonMixed38
noncomputable section

theorem normingFactor_at_dirichlet_root38 (φ : PotPair) (z : ℂ)
    (hr : dirichletChar φ z = 0) :
    normingFactor φ z = monodromyPair φ z 0 0 + monodromyPair φ z 0 1 := by
  have hb := dirichlet_boundary_sum φ z hr
  unfold normingFactor
  linear_combination hb/2

theorem normingFactor_ne_zero_at_dirichlet_root38 (φ : PotPair) (z : ℂ)
    (hr : dirichletChar φ z = 0) : normingFactor φ z ≠ 0 := by
  rw [normingFactor_at_dirichlet_root38 φ z hr]
  exact (dirichlet_amplitudes_nonzero φ z hr).1

theorem norming_Q_at_dirichlet_root38 (φ : PotPair) (z : ℂ)
    (hr : dirichletChar φ z = 0) :
    Q (state φ z ![1,1]) = 2 * deriv (dirichletChar φ) z * normingFactor φ z := by
  have hi := dirichlet_amplitude_inverse φ z hr
  have hq := dirichlet_Q_spectral_relation φ z hr
  rw [normingFactor_at_dirichlet_root38 φ z hr]
  linear_combination (monodromyPair φ z 0 0 + monodromyPair φ z 0 1) * hq -
    Q (state φ z ![1,1]) * hi

theorem norming_terminal_at_dirichlet_root38 (φ : PotPair) (z : ℂ)
    (hr : dirichletChar φ z = 0) :
    state φ z ![1,1] t1 = normingFactor φ z • (![1,1] : PairVec38) := by
  have hb := dirichlet_boundary_sum φ z hr
  rw [normingFactor_at_dirichlet_root38 φ z hr]
  rw [state_eq_mulVec]
  change (monodromyPair φ z).mulVec ![1,1] =
    (monodromyPair φ z 0 0 + monodromyPair φ z 0 1) • (![1,1] : PairVec38)
  ext j
  fin_cases j <;> simp [Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  linear_combination hb

theorem norming_anti_at_dirichlet_root38 (φ : PotPair) (z : ℂ)
    (hr : dirichletChar φ z = 0) :
    (normingFactor φ z)^2-1 = normingFactor φ z * antiDiscrim φ z := by
  have hb := dirichlet_boundary_sum φ z hr
  have hi := dirichlet_amplitude_inverse φ z hr
  rw [normingFactor_at_dirichlet_root38 φ z hr]
  unfold antiDiscrim
  linear_combination hi - (monodromyPair φ z 0 0 + monodromyPair φ z 0 1) * hb

theorem normingRootDataTarget : NormingRootDataTarget := by
  intro φ z hr hs
  exact ⟨normingFactor_ne_zero_at_dirichlet_root38 φ z hr,
    dirichlet_Q_ne_zero φ z hr hs,norming_Q_at_dirichlet_root38 φ z hr,
    norming_terminal_at_dirichlet_root38 φ z hr,norming_anti_at_dirichlet_root38 φ z hr⟩

end
end NlsGge.GK38.PoissonMixed38
