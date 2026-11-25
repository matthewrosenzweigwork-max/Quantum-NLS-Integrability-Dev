import LiebLiniger.FixedPeriod.Quantum.WickMixedOuterFactors
import LiebLiniger.FixedPeriod.Quantum.WickGuardedOuterNaturality

/-! Exact Source13 guarded mixed outer pairing on the original source degrees.
All degree casts are discharged by actual sector-cast naturality; the same
four physical field families and actual kernels are retained. SOURCE ONLY. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace LiebLiniger.FixedPeriod.Quantum
variable {X : Type} [MeasurableSpace X] (μ : Measure X)
  [SigmaFinite μ] [IsFiniteMeasure μ]

theorem sourceDerivativeContractionKernel_mixed_outer_pairing (p q r s j : ℕ)
    (gs : Fin p → Lp ℂ 2 μ) (as : Fin q → Lp ℂ 2 μ)
    (hs : Fin s → Lp ℂ 2 μ) (ks : Fin r → Lp ℂ 2 μ) (v u : Lp ℂ 2 μ) :
    wickKernelPolarized μ (sourceDerivativeContractionKernel μ
        (InnerProductSpace.rankOne ℂ (symmetricTensorContinuousMultilinear μ q as)
          (symmetricTensorContinuousMultilinear μ p gs))
        (InnerProductSpace.rankOne ℂ (symmetricTensorContinuousMultilinear μ s hs)
          (symmetricTensorContinuousMultilinear μ r ks)) j) v u =
      ((∏ i : Fin q, inner ℂ v (as i)) * (∏ k : Fin r, inner ℂ (ks k) u)) *
        wickKernelPolarized μ (sourceDerivativeContractionKernel μ
          (InnerProductSpace.rankOne ℂ (pureSymmetricTensor μ 0 (0 : Lp ℂ 2 μ))
            (symmetricTensorContinuousMultilinear μ p gs))
          (InnerProductSpace.rankOne ℂ (symmetricTensorContinuousMultilinear μ s hs)
            (pureSymmetricTensor μ 0 (0 : Lp ℂ 2 μ))) j) v u := by
  by_cases hj : j ≤ min p s
  · have hdegrees : ∃ a b : ℕ, p = a + j ∧ s = j + b :=
      (contractionDegrees_coverage p s j).mp hj
    obtain ⟨a, b, hp, hsdeg⟩ := hdegrees
    subst p
    subst s
    let A := InnerProductSpace.rankOne ℂ (symmetricTensorContinuousMultilinear μ q as)
      (symmetricTensorContinuousMultilinear μ (a + j) gs)
    let A0 := InnerProductSpace.rankOne ℂ (pureSymmetricTensor μ 0 (0 : Lp ℂ 2 μ))
      (symmetricTensorContinuousMultilinear μ (a + j) gs)
    let B := InnerProductSpace.rankOne ℂ (symmetricTensorContinuousMultilinear μ (j + b) hs)
      (symmetricTensorContinuousMultilinear μ r ks)
    let B0 := InnerProductSpace.rankOne ℂ (symmetricTensorContinuousMultilinear μ (j + b) hs)
      (pureSymmetricTensor μ 0 (0 : Lp ℂ 2 μ))
    let c : ℂ := (∏ i : Fin q, inner ℂ v (as i)) * (∏ k : Fin r, inner ℂ (ks k) u)
    change wickKernelPolarized μ (sourceDerivativeContractionKernel μ A B j) v u =
      c * wickKernelPolarized μ (sourceDerivativeContractionKernel μ A0 B0 j) v u
    have hAB := sourceDerivativeContractionKernel_available_outer_naturality μ a j b q r A B v u
    have hAB0 := sourceDerivativeContractionKernel_available_outer_naturality μ a j b 0 0 A0 B0 v u
    have hfactor : wickKernelPolarized μ (tensorDerivativeContraction (j := j) μ A B) v u =
        c * wickKernelPolarized μ (tensorDerivativeContraction (j := j) μ A0 B0) v u :=
      tensorDerivativeContraction_mixed_outer_pairing μ a j b q r gs as hs ks v u
    calc
      _ = wickKernelPolarized μ (tensorDerivativeContraction (j := j) μ A B) v u := hAB
      _ = c * wickKernelPolarized μ (tensorDerivativeContraction (j := j) μ A0 B0) v u := hfactor
      _ = c * wickKernelPolarized μ (sourceDerivativeContractionKernel μ A0 B0 j) v u :=
        congrArg (fun z : ℂ => c * z) hAB0.symm
  · let A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q :=
      InnerProductSpace.rankOne ℂ (symmetricTensorContinuousMultilinear μ q as)
        (symmetricTensorContinuousMultilinear μ p gs)
    let A0 : SymmetricSector μ p →L[ℂ] SymmetricSector μ 0 :=
      InnerProductSpace.rankOne ℂ (pureSymmetricTensor μ 0 (0 : Lp ℂ 2 μ))
        (symmetricTensorContinuousMultilinear μ p gs)
    let B : SymmetricSector μ r →L[ℂ] SymmetricSector μ s :=
      InnerProductSpace.rankOne ℂ (symmetricTensorContinuousMultilinear μ s hs)
        (symmetricTensorContinuousMultilinear μ r ks)
    let B0 : SymmetricSector μ 0 →L[ℂ] SymmetricSector μ s :=
      InnerProductSpace.rankOne ℂ (symmetricTensorContinuousMultilinear μ s hs)
        (pureSymmetricTensor μ 0 (0 : Lp ℂ 2 μ))
    have hAB : wickKernelPolarized μ (sourceDerivativeContractionKernel μ A B j) v u = 0 := by
      rw [sourceDerivativeContractionKernel_unavailable μ A B j hj]
      simp only [wickKernelPolarized, ContinuousLinearMap.zero_apply, inner_zero_right]
    have hAB0 : wickKernelPolarized μ (sourceDerivativeContractionKernel μ A0 B0 j) v u = 0 := by
      rw [sourceDerivativeContractionKernel_unavailable μ A0 B0 j hj]
      simp only [wickKernelPolarized, ContinuousLinearMap.zero_apply, inner_zero_right]
    change wickKernelPolarized μ (sourceDerivativeContractionKernel μ A B j) v u =
      ((∏ i : Fin q, inner ℂ v (as i)) * (∏ k : Fin r, inner ℂ (ks k) u)) *
        wickKernelPolarized μ (sourceDerivativeContractionKernel μ A0 B0 j) v u
    rw [hAB, hAB0, mul_zero]

end LiebLiniger.FixedPeriod.Quantum
end
