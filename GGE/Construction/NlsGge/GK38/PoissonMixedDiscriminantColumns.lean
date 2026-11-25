import NlsGge.GK38.PoissonMixedRealKappaBrackets

set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.GK38 NlsGge.GK38.GradEigen38 NlsGge.GK38.PoissonDirichlet38
namespace NlsGge.GK38.PoissonMixed38
noncomputable section

theorem state_seed_initial_bracket38 (φ : PotPair) (z ζ : ℂ) (a : PairVec38) :
    pairBracket38 (pairKernelExt38 (state φ ζ a) 0)
      (pairKernelExt38 (state φ z ![1,1]) 0) = a 0-a 1 := by
  rw [pairKernelExt38_of_mem _ (show (0 : ℝ) ∈ Icc 0 1 from ⟨le_rfl,zero_le_one⟩),
    pairKernelExt38_of_mem _ (show (0 : ℝ) ∈ Icc 0 1 from ⟨le_rfl,zero_le_one⟩)]
  change pairBracket38 (state φ ζ a t0) (state φ z ![1,1] t0)=_
  rw [state_initial,state_initial]
  simp [pairBracket38]

theorem state_seed_terminal_bracket38 (φ : PotPair) (z ζ : ℂ) (a : PairVec38)
    (hr : dirichletChar φ z = 0) :
    pairBracket38 (pairKernelExt38 (state φ ζ a) 1)
      (pairKernelExt38 (state φ z ![1,1]) 1) =
    normingFactor φ z * (a 0*(monodromyPair φ ζ 0 0-monodromyPair φ ζ 1 0) +
      a 1*(monodromyPair φ ζ 0 1-monodromyPair φ ζ 1 1)) := by
  rw [pairKernelExt38_of_mem _ (show (1 : ℝ) ∈ Icc 0 1 from ⟨zero_le_one,le_rfl⟩),
    pairKernelExt38_of_mem _ (show (1 : ℝ) ∈ Icc 0 1 from ⟨zero_le_one,le_rfl⟩)]
  change pairBracket38 (state φ ζ a t1) (state φ z ![1,1] t1)=_
  rw [norming_terminal_at_dirichlet_root38 φ z hr,state_eq_mulVec]
  change pairBracket38 ((monodromyPair φ ζ).mulVec a)
    (normingFactor φ z • (![1,1] : PairVec38)) = _
  simp only [pairBracket38,Matrix.mulVec,dotProduct,Fin.sum_univ_two,
    Matrix.cons_val_zero,Matrix.cons_val_one,Pi.smul_apply,smul_eq_mul,mul_one]
  ring

theorem integrated_seed_dirichlet_star38 (φ : PotPair) (z ζ : ℂ) (a c : PairVec38)
    (hr : dirichletChar φ z = 0) :
    (normingFactor φ z)^2 *
      (a 0*(monodromyPair φ ζ 0 0-monodromyPair φ ζ 1 0) +
        a 1*(monodromyPair φ ζ 0 1-monodromyPair φ ζ 1 1)) *
      (c 0*(monodromyPair φ ζ 0 0-monodromyPair φ ζ 1 0) +
        c 1*(monodromyPair φ ζ 0 1-monodromyPair φ ζ 1 1)) -
      (a 0-a 1)*(c 0-c 1) =
    2*Complex.I*(ζ-z) * ∫ s in (0 : ℝ)..1,
      pairBracket38
        (starProd38 (pairKernelExt38 (state φ ζ a) s) (pairKernelExt38 (state φ ζ c) s))
        (starProd38 (pairKernelExt38 (state φ z ![1,1]) s)
          (pairKernelExt38 (state φ z ![1,1]) s)) := by
  have ha := state_isPairSolution38 φ ζ a
  have hb := state_isPairSolution38 φ z ![1,1]
  have hc := state_isPairSolution38 φ ζ c
  have _hi := intervalIntegrable_starBracket38 ha hb hc hb
  have h := integrated_starIdentity38 ha hb hc hb ⟨1,zero_le_one,le_rfl⟩
  rw [state_seed_initial_bracket38,state_seed_initial_bracket38,
    state_seed_terminal_bracket38 φ z ζ a hr,state_seed_terminal_bracket38 φ z ζ c hr] at h
  convert! h using 1 <;> ring

theorem discriminant_column_endpoint_polynomial38 (M : PairMat38) (u : ℂ)
    (hd : M 0 0*M 1 1-M 0 1*M 1 0=1) :
    M 0 1*((M 0 0-M 1 0)^2*u^2-1) +
      (M 1 1-M 0 0)*((M 0 0-M 1 0)*(M 0 1-M 1 1)*u^2+1) -
      M 1 0*((M 0 1-M 1 1)^2*u^2-1) =
      (M 0 0+M 0 1-M 1 0-M 1 1)*(u^2-1) := by
  linear_combination (M 0 0+M 0 1-M 1 0-M 1 1)*u^2*hd

end
end NlsGge.GK38.PoissonMixed38
