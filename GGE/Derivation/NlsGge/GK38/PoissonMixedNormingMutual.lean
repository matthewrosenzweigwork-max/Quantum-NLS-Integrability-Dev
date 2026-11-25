import NlsGge.GK38.PoissonMixedPairing

set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.GK38 NlsGge.GK38.GradEigen38 NlsGge.GK38.PoissonDirichlet38
namespace NlsGge.GK38.PoissonMixed38
noncomputable section

theorem state_isPairSolution38 (φ : PotPair) (z : ℂ) (a : PairVec38) :
    IsPairSolution38 φ z (pairKernelExt38 (state φ z a)) :=
  ⟨ac_state_component φ z a,ae_hasDerivAt_state_component φ z a⟩

theorem norming_initial_bracket38 (φ : PotPair) (z w : ℂ) :
    pairBracket38 (pairKernelExt38 (state φ z ![1,1]) 0)
      (pairKernelExt38 (state φ w ![1,1]) 0) = 0 := by
  rw [pairKernelExt38_of_mem _ (show (0 : ℝ) ∈ Icc 0 1 from ⟨le_rfl,zero_le_one⟩),
    pairKernelExt38_of_mem _ (show (0 : ℝ) ∈ Icc 0 1 from ⟨le_rfl,zero_le_one⟩)]
  change pairBracket38 (state φ z ![1,1] t0) (state φ w ![1,1] t0) = 0
  simp [state_initial,pairBracket38]

theorem norming_terminal_bracket38 (φ : PotPair) (z w : ℂ) :
    pairBracket38 (pairKernelExt38 (state φ z (terminalSeed φ z)) 1)
      (pairKernelExt38 (state φ w (terminalSeed φ w)) 1) = 0 := by
  rw [pairKernelExt38_of_mem _ (show (1 : ℝ) ∈ Icc 0 1 from ⟨zero_le_one,le_rfl⟩),
    pairKernelExt38_of_mem _ (show (1 : ℝ) ∈ Icc 0 1 from ⟨zero_le_one,le_rfl⟩)]
  change pairBracket38 (state φ z (terminalSeed φ z) t1)
    (state φ w (terminalSeed φ w) t1) = 0
  rw [terminal_state,terminal_state]
  simp [pairBracket38]

theorem integral_norming_starBracket38_eq_zero (φ : PotPair) (z w : ℂ) :
    (∫ s in (0 : ℝ)..1,
      pairBracket38
        (starProd38 (pairKernelExt38 (state φ z ![1,1]) s)
          (pairKernelExt38 (state φ z (terminalSeed φ z)) s))
        (starProd38 (pairKernelExt38 (state φ w ![1,1]) s)
          (pairKernelExt38 (state φ w (terminalSeed φ w)) s))) = 0 := by
  have ha := state_isPairSolution38 φ z ![1,1]
  have hb := state_isPairSolution38 φ w ![1,1]
  have hc := state_isPairSolution38 φ z (terminalSeed φ z)
  have hd := state_isPairSolution38 φ w (terminalSeed φ w)
  have _hi := intervalIntegrable_starBracket38 ha hb hc hd
  by_cases hzw : z = w
  · subst w
    have he (v : PairVec38) : pairBracket38 v v = 0 := by
      unfold pairBracket38
      ring
    simp only [he,intervalIntegral.integral_zero]
  · have h := integrated_starIdentity38 ha hb hc hd ⟨1,zero_le_one,le_rfl⟩
    rw [norming_initial_bracket38,norming_terminal_bracket38] at h
    simp only [zero_mul,mul_zero,sub_zero] at h
    have hn : 2*Complex.I*(z-w) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) (sub_ne_zero.mpr hzw)
    exact (mul_eq_zero.mp h.symm).resolve_left hn

theorem normingWedge38_eq_raw (φ : PotPair) (z w : ℂ) (s : ℝ) :
    kernelWedge38 (normingKernel38 φ z) (normingKernel38 φ w) s =
      ((2*Complex.I)⁻¹ * (2*Complex.I)⁻¹) *
      pairBracket38
        (starProd38 (pairKernelExt38 (state φ z ![1,1]) s)
          (pairKernelExt38 (state φ z (terminalSeed φ z)) s))
        (starProd38 (pairKernelExt38 (state φ w ![1,1]) s)
          (pairKernelExt38 (state φ w (terminalSeed φ w)) s)) := by
  simp only [kernelWedge38,normingKernel38,pairKernelExt38,Set.IccExtend,Function.comp_apply,
    ContinuousMap.smul_apply,Pi.smul_apply,smul_eq_mul,mixedSquare,
    ContinuousMap.coe_mk,pairBracket38,starProd38,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  ring

theorem normingSpectralMutualTarget : NormingSpectralMutualTarget := by
  intro φ z w
  have _hi := intervalIntegrable_kernelWedge38 (normingKernel38 φ z) (normingKernel38 φ w)
  unfold kernelPoisson38
  simp only [normingWedge38_eq_raw,intervalIntegral.integral_const_mul,
    integral_norming_starBracket38_eq_zero,mul_zero]

end
end NlsGge.GK38.PoissonMixed38
