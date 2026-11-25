import NlsGge.GK38.GradFundamentalAction

/-! # K1: actual discriminant and antidiscriminant potential gradients.
GK Chapter I, Corollary3.2. The derivative equals the independent bilinear CLM.
-/
set_option autoImplicit false
open MeasureTheory Set
namespace NlsGge.GK38
noncomputable section

theorem integralPairCLM38_kernelAdd (g k : PairKernelCont38) (t : Icc (0 : ℝ) 1) :
    integralPairCLM38 (g + k) t = integralPairCLM38 g t + integralPairCLM38 k t := by
  apply ContinuousLinearMap.ext
  intro h
  change pairIntegral38 (g + k) t h = pairIntegral38 g t h + pairIntegral38 k t h
  unfold pairIntegral38
  rw [← intervalIntegral.integral_add (intervalIntegrable_pairKernel38 g t h)
    (intervalIntegrable_pairKernel38 k t h)]
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : s ∈ Icc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le zero_le_one] using (uIcc_zero_subset t.2) hs
  simp only [pairKernelExt38_of_mem _ hs', ContinuousMap.add_apply, Pi.add_apply]
  ring

theorem gradDiscrimCont38_entrySum (φ : PotPair) (z : ℂ) :
    gradDiscrimCont38 φ z =
      fundamentalEntryKernelCont38 φ z ⟨1, zero_le_one, le_rfl⟩ 0 0 +
        fundamentalEntryKernelCont38 φ z ⟨1, zero_le_one, le_rfl⟩ 1 1 := by
  ext s k
  fin_cases k <;> simp [gradDiscrimCont38, fundamentalEntryKernelCont38,
    gradDiscrim38, fundamentalScaledKernel38, monodromyPair_eq_fundPair,
    fundColumn38, starProd38] <;> ring

theorem gradAntiDiscrimCont38_entrySum (φ : PotPair) (z : ℂ) :
    gradAntiDiscrimCont38 φ z =
      fundamentalEntryKernelCont38 φ z ⟨1, zero_le_one, le_rfl⟩ 0 1 +
        fundamentalEntryKernelCont38 φ z ⟨1, zero_le_one, le_rfl⟩ 1 0 := by
  ext s k
  fin_cases k <;> simp [gradAntiDiscrimCont38, fundamentalEntryKernelCont38,
    gradAntiDiscrim38, fundamentalScaledKernel38, monodromyPair_eq_fundPair,
    fundColumn38, starProd38] <;> ring

theorem gradDiscrimCLM_entrySum (φ : PotPair) (z : ℂ) :
    gradDiscrimCLM φ z =
      fundamentalEntryCLM38 φ z ⟨1, zero_le_one, le_rfl⟩ 0 0 +
        fundamentalEntryCLM38 φ z ⟨1, zero_le_one, le_rfl⟩ 1 1 := by
  unfold gradDiscrimCLM fundamentalEntryCLM38
  rw [gradDiscrimCont38_entrySum, integralPairCLM38_kernelAdd]

theorem gradAntiDiscrimCLM_entrySum (φ : PotPair) (z : ℂ) :
    gradAntiDiscrimCLM φ z =
      fundamentalEntryCLM38 φ z ⟨1, zero_le_one, le_rfl⟩ 0 1 +
        fundamentalEntryCLM38 φ z ⟨1, zero_le_one, le_rfl⟩ 1 0 := by
  unfold gradAntiDiscrimCLM fundamentalEntryCLM38
  rw [gradAntiDiscrimCont38_entrySum, integralPairCLM38_kernelAdd]

theorem hasFDerivAt_gradDiscrimCLM (φ : PotPair) (z : ℂ) :
    HasFDerivAt (fun ψ => discrim ψ z) (gradDiscrimCLM φ z) φ := by
  rw [gradDiscrimCLM_entrySum]
  have hd := (hasFDerivAt_fundamentalEntryCLM38 φ z ⟨1, zero_le_one, le_rfl⟩ 0 0).fun_add
    (hasFDerivAt_fundamentalEntryCLM38 φ z ⟨1, zero_le_one, le_rfl⟩ 1 1)
  simpa only [discrim_eq, monodromyPair_eq_fundPair] using hd

theorem hasFDerivAt_gradAntiDiscrimCLM (φ : PotPair) (z : ℂ) :
    HasFDerivAt (fun ψ => antiDiscrim ψ z) (gradAntiDiscrimCLM φ z) φ := by
  rw [gradAntiDiscrimCLM_entrySum]
  have hd := (hasFDerivAt_fundamentalEntryCLM38 φ z ⟨1, zero_le_one, le_rfl⟩ 0 1).fun_add
    (hasFDerivAt_fundamentalEntryCLM38 φ z ⟨1, zero_le_one, le_rfl⟩ 1 0)
  simpa only [antiDiscrim, monodromyPair_eq_fundPair] using hd

end
end NlsGge.GK38
