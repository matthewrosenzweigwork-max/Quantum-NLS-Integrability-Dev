import NlsGge.GK38.GradFundamentalVOC

/-! # K1: integral action of the independent fundamental entry kernel.
GK Chapter I, Proposition3.1. Matrix integral transport uses entry integrability.
-/
set_option autoImplicit false
open MeasureTheory Set
namespace NlsGge.GK38
noncomputable section

theorem k1MatIntegralLeft38 (A : PairMat38) (f : ℝ → PairMat38) (t : ℝ)
    (hf : ∀ a b, IntervalIntegrable (fun s => f s a b) volume 0 t) (i j : Fin 2) :
    (A * Matrix.of (fun a b => ∫ s in (0 : ℝ)..t, f s a b)) i j =
      ∫ s in (0 : ℝ)..t, (A * f s) i j := by
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply]
  rw [intervalIntegral.integral_add ((hf 0 j).const_mul _) ((hf 1 j).const_mul _)]
  simp only [intervalIntegral.integral_const_mul]

theorem fundamentalPotentialKernel_action38 (φ : PotPair) (z : ℂ)
    (t : Icc (0 : ℝ) 1) (s : ℝ) (h : PotPair) (i j : Fin 2) :
    ((fundPair φ z t * (ext38 (fundContP φ z) s).adjugate) *
      potCoeff38 h s * ext38 (fundContP φ z) s) i j =
      ((-Complex.I) * fundamentalScaledKernel38 φ z t s i j 0) * potRepFst38 h s +
      ((-Complex.I) * fundamentalScaledKernel38 φ z t s i j 1) * potRepSnd38 h s := by
  fin_cases i <;> fin_cases j <;>
    simp [fundamentalScaledKernel38, fundColumn38, starProd38, potCoeff38,
      Matrix.adjugate_fin_two, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two] <;> ring

/-- An independent integral-defined entry gradient. -/
def fundamentalEntryCLM38 (φ : PotPair) (z : ℂ) (t : Icc (0 : ℝ) 1)
    (i j : Fin 2) : PotPair →L[ℂ] ℂ :=
  integralPairCLM38 (fundamentalEntryKernelCont38 φ z t i j) t

theorem fundamentalEntryCLM38_apply (φ : PotPair) (z : ℂ) (t : Icc (0 : ℝ) 1)
    (i j : Fin 2) (h : PotPair) :
    fundamentalEntryCLM38 φ z t i j h = fundPotentialIntegral38 φ z t h i j := by
  rw [fundPotentialIntegral38, k1MatIntegralLeft38 _ _ _
    (intervalIntegrable_fundPotentialKer38 φ z h t)]
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : s ∈ Icc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le zero_le_one] using (uIcc_zero_subset t.2) hs
  change pairKernelExt38 (fundamentalEntryKernelCont38 φ z t i j) s 0 * potRepFst38 h s +
    pairKernelExt38 (fundamentalEntryKernelCont38 φ z t i j) s 1 * potRepSnd38 h s = _
  rw [pairKernelExt38_of_mem _ hs']
  change ((-Complex.I) * fundamentalScaledKernel38 φ z t s i j 0) * potRepFst38 h s +
    ((-Complex.I) * fundamentalScaledKernel38 φ z t s i j 1) * potRepSnd38 h s = _
  rw [← fundamentalPotentialKernel_action38]
  simp only [mul_assoc]

 theorem fundamentalEntryCLM38_eq (φ : PotPair) (z : ℂ) (t : Icc (0 : ℝ) 1)
    (i j : Fin 2) :
    fundamentalEntryCLM38 φ z t i j =
      (fundEntryL38 t i j).comp (fundPotentialResolventCLM38 φ z) := by
  apply ContinuousLinearMap.ext
  intro h
  rw [fundamentalEntryCLM38_apply, ← fundPotentialResolventCLM38_voc]
  rfl

theorem hasFDerivAt_fundamentalEntryCLM38 (φ : PotPair) (z : ℂ)
    (t : Icc (0 : ℝ) 1) (i j : Fin 2) :
    HasFDerivAt (fun ψ => fundPair ψ z t i j) (fundamentalEntryCLM38 φ z t i j) φ := by
  rw [fundamentalEntryCLM38_eq]
  exact (fundEntryL38 t i j).hasFDerivAt.comp φ (hasFDerivAt_fundPotentialResolvent38 φ z)

end
end NlsGge.GK38
