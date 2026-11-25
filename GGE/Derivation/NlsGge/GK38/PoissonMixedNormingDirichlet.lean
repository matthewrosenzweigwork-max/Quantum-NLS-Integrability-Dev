import NlsGge.GK38.PoissonMixedContinuity

set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.GK38 NlsGge.GK38.GradEigen38 NlsGge.GK38.PoissonDirichlet38
namespace NlsGge.GK38.PoissonMixed38
noncomputable section

theorem norming_dir_terminal_product38 (φ : PotPair) (z ζ : ℂ)
    (hr : dirichletChar φ z = 0) :
    pairBracket38 (pairKernelExt38 (state φ ζ ![1,1]) 1)
        (pairKernelExt38 (state φ z ![1,1]) 1) *
      pairBracket38 (pairKernelExt38 (state φ ζ (terminalSeed φ ζ)) 1)
        (pairKernelExt38 (state φ z ![1,1]) 1) =
      -4*Complex.I*dirichletChar φ ζ*(normingFactor φ z)^2 := by
  simp only [pairKernelExt38_of_mem _ (show (1 : ℝ) ∈ Icc 0 1 from ⟨zero_le_one,le_rfl⟩)]
  change pairBracket38 (state φ ζ ![1,1] t1) (state φ z ![1,1] t1) *
    pairBracket38 (state φ ζ (terminalSeed φ ζ) t1) (state φ z ![1,1] t1) = _
  rw [norming_terminal_at_dirichlet_root38 φ z hr,terminal_state,state_eq_mulVec]
  change pairBracket38 ((monodromyPair φ ζ).mulVec ![1,1])
      (normingFactor φ z • (![1,1] : PairVec38)) *
    pairBracket38 ![1,-1] (normingFactor φ z • (![1,1] : PairVec38)) = _
  simp only [pairBracket38,Matrix.mulVec,dotProduct,Fin.sum_univ_two,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
    Pi.smul_apply,smul_eq_mul,mul_one,mul_neg_one,dirichletChar_eq]
  field_simp
  ring

theorem norming_dir_integral_identity38 (φ : PotPair) (z ζ : ℂ)
    (hr : dirichletChar φ z = 0) :
    -4*Complex.I*dirichletChar φ ζ*(normingFactor φ z)^2 =
      2*Complex.I*(ζ-z) * ∫ s in (0 : ℝ)..1,
      pairBracket38
        (starProd38 (pairKernelExt38 (state φ ζ ![1,1]) s)
          (pairKernelExt38 (state φ ζ (terminalSeed φ ζ)) s))
        (starProd38 (pairKernelExt38 (state φ z ![1,1]) s)
          (pairKernelExt38 (state φ z ![1,1]) s)) := by
  have ha := state_isPairSolution38 φ ζ ![1,1]
  have hb := state_isPairSolution38 φ z ![1,1]
  have hc := state_isPairSolution38 φ ζ (terminalSeed φ ζ)
  have _hi := intervalIntegrable_starBracket38 ha hb hc hb
  have h := integrated_starIdentity38 ha hb hc hb ⟨1,zero_le_one,le_rfl⟩
  rw [norming_initial_bracket38,zero_mul,sub_zero] at h
  rw [norming_dir_terminal_product38 φ z ζ hr] at h
  exact h

theorem norming_dir_wedge_eq_raw38 (φ : PotPair) (z ζ : ℂ) (s : ℝ) :
    kernelWedge38 (normingKernel38 φ ζ) (dirEigenKernel38 φ z) s =
      ((2*Complex.I)⁻¹ * (Q (state φ z ![1,1]))⁻¹) *
      pairBracket38
        (starProd38 (pairKernelExt38 (state φ ζ ![1,1]) s)
          (pairKernelExt38 (state φ ζ (terminalSeed φ ζ)) s))
        (starProd38 (pairKernelExt38 (state φ z ![1,1]) s)
          (pairKernelExt38 (state φ z ![1,1]) s)) := by
  simp only [kernelWedge38,normingKernel38,dirEigenKernel38,pairKernelExt38,
    Set.IccExtend,Function.comp_apply,ContinuousMap.smul_apply,Pi.smul_apply,
    smul_eq_mul,mixedSquare,square,ContinuousMap.coe_mk,pairBracket38,starProd38,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  ring

end
end NlsGge.GK38.PoissonMixed38
