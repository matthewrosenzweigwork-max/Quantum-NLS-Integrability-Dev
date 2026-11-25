import NlsGge.GK38.GradEigenFloquet

set_option autoImplicit false
open Set Filter Topology MeasureTheory
namespace NlsGge.GK38.GradEigen38
noncomputable section
theorem integralPairCLM38_kernelSmul (c : ℂ) (g : PairKernelCont38) (t : Time) :
    integralPairCLM38 (c • g) t = c • integralPairCLM38 g t := by
  apply ContinuousLinearMap.ext
  intro h
  have _hi := intervalIntegrable_pairKernel38 g t h
  change pairIntegral38 (c • g) t h = c * pairIntegral38 g t h
  unfold pairIntegral38
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : s ∈ Icc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le zero_le_one] using (uIcc_zero_subset t.2) hs
  simp only [pairKernelExt38_of_mem _ hs', ContinuousMap.smul_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

theorem norming_kernel_sum (φ : PotPair) (z : ℂ) :
    fundamentalEntryKernelCont38 φ z t1 0 0 +
      fundamentalEntryKernelCont38 φ z t1 0 1 +
      fundamentalEntryKernelCont38 φ z t1 1 0 +
      fundamentalEntryKernelCont38 φ z t1 1 1 =
    (-Complex.I) • mixedSquare (state φ z ![1,1]) (state φ z (terminalSeed φ z)) := by
  ext s i
  fin_cases i <;>
    simp [fundamentalEntryKernelCont38, fundamentalScaledKernel38,
      mixedSquare, state, terminalSeed, starProd38, monodromyPair_eq_fundPair, t1] <;>
    ring

theorem norming_derivative (φ : PotPair) (z : ℂ) :
    HasFDerivAt (fun ψ : PotPair => normingFactor ψ z)
      (((2 * Complex.I : ℂ)⁻¹) • integralPairCLM38
        (mixedSquare (state φ z ![1,1]) (state φ z (terminalSeed φ z))) t1) φ := by
  have hd := (((hasFDerivAt_fundamentalEntryCLM38 φ z t1 0 0).fun_add
    (hasFDerivAt_fundamentalEntryCLM38 φ z t1 0 1)).fun_add
    (hasFDerivAt_fundamentalEntryCLM38 φ z t1 1 0)).fun_add
    (hasFDerivAt_fundamentalEntryCLM38 φ z t1 1 1)
  have hc : (2 : ℂ)⁻¹ * (-Complex.I) = (2 * Complex.I)⁻¹ := by
    field_simp
    simp [← mul_assoc, Complex.I_mul_I]
  have hsum : fundamentalEntryCLM38 φ z t1 0 0 + fundamentalEntryCLM38 φ z t1 0 1 +
      fundamentalEntryCLM38 φ z t1 1 0 + fundamentalEntryCLM38 φ z t1 1 1 =
      (-Complex.I) • integralPairCLM38
        (mixedSquare (state φ z ![1,1]) (state φ z (terminalSeed φ z))) t1 := by
    simp only [fundamentalEntryCLM38, ← integralPairCLM38_kernelAdd]
    rw [norming_kernel_sum, integralPairCLM38_kernelSmul]
  have hscaled := hd.const_mul ((2 : ℂ)⁻¹)
  rw [hsum, smul_smul, hc] at hscaled
  simpa only [normingFactor, monodromyPair_eq_fundPair, t1, div_eq_mul_inv, mul_comm]
    using hscaled

theorem terminal_state (φ : PotPair) (z : ℂ) :
    state φ z (terminalSeed φ z) t1 = (![1,-1] : PairVec38) := by
  rw [state_eq_mulVec]
  have hd := monodromy_det_scalar φ z
  ext i
  fin_cases i <;>
    simp [terminalSeed, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      ← monodromyPair_eq_fundPair, t1]
  · linear_combination hd
  · linear_combination -hd

def NormingFactorGradientTarget : Prop :=
  ∀ (φ : PotPair) (z : ℂ),
    HasFDerivAt
      (fun ψ : PotPair =>
        (monodromyPair ψ z 0 0 + monodromyPair ψ z 0 1 +
          monodromyPair ψ z 1 0 + monodromyPair ψ z 1 1) / 2)
      (((2 * Complex.I : ℂ)⁻¹) •
        integralPairCLM38
          (mixedSquare
            (state φ z (![1, 1] : PairVec38))
            (state φ z
              (![monodromyPair φ z 0 1 + monodromyPair φ z 1 1,
                -(monodromyPair φ z 0 0 + monodromyPair φ z 1 0)] : PairVec38)))
          (⟨1, zero_le_one, le_rfl⟩ : Set.Icc (0 : ℝ) 1))
      φ ∧
    state φ z
        (![monodromyPair φ z 0 1 + monodromyPair φ z 1 1,
          -(monodromyPair φ z 0 0 + monodromyPair φ z 1 0)] : PairVec38)
        (⟨1, zero_le_one, le_rfl⟩ : Set.Icc (0 : ℝ) 1) =
      (![1, -1] : PairVec38)


theorem norming_factor_gradient_target : NormingFactorGradientTarget := by
  intro φ z
  exact ⟨norming_derivative φ z, terminal_state φ z⟩


end
end NlsGge.GK38.GradEigen38
