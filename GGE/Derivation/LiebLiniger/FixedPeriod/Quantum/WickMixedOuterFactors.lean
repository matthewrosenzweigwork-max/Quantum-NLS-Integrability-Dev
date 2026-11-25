import LiebLiniger.FixedPeriod.Quantum.WickGuardedDerivativePairing

/-! Bounded Source13 outer-derivative factor leaf. These are the literal
physical tensor contractions and field families from the whole source.
Uncompiled; no global product or guarded theorem is claimed. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace LiebLiniger.FixedPeriod.Quantum
variable {X : Type} [MeasurableSpace X] (μ : Measure X)
  [SigmaFinite μ] [IsFiniteMeasure μ]

/-- The actual source input derivative functional retains the independent
outer creator slots as their physical pure pairing. This is an equality on
the COMPLETE free tensor space, earned from the actual insertion definition. -/
theorem wickInputDerivativeFunctional_mixed_outer_factor (r j q : ℕ)
    (gs : Fin (r + j) → Lp ℂ 2 μ) (as : Fin q → Lp ℂ 2 μ) (v u : Lp ℂ 2 μ) :
    wickInputDerivativeFunctional (j := j) μ
        (InnerProductSpace.rankOne ℂ (symmetricTensorContinuousMultilinear μ q as)
          (symmetricTensorContinuousMultilinear μ (r + j) gs)) v u =
      (∏ i : Fin q, inner ℂ v (as i)) •
        wickInputDerivativeFunctional (j := j) μ
          (InnerProductSpace.rankOne ℂ (pureSymmetricTensor μ 0 (0 : Lp ℂ 2 μ))
            (symmetricTensorContinuousMultilinear μ (r + j) gs)) v u := by
  ext w
  simp only [wickInputDerivativeFunctional, ContinuousLinearMap.smul_apply,
    wickInputSlotFunctional, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    InnerProductSpace.rankOne_apply, inner_smul_right, inner_pure_symmetricMixedTensor,
    inner_pureSymmetricTensor, pow_zero, mul_one, smul_eq_mul]
  ring

/-- The actual source output derivative Riesz vector retains the independent
outer annihilator slots, including the conjugation forced by Riesz only when
this vector is paired in its first slot. This equality is on actual vectors. -/
theorem wickOutputDerivativeVector_mixed_outer_factor (j s r : ℕ)
    (hs : Fin (j + s) → Lp ℂ 2 μ) (ks : Fin r → Lp ℂ 2 μ) (v u : Lp ℂ 2 μ) :
    wickOutputDerivativeVector (j := j) μ
        (InnerProductSpace.rankOne ℂ (symmetricTensorContinuousMultilinear μ (j + s) hs)
          (symmetricTensorContinuousMultilinear μ r ks)) v u =
      (∏ k : Fin r, inner ℂ (ks k) u) •
        wickOutputDerivativeVector (j := j) μ
          (InnerProductSpace.rankOne ℂ (symmetricTensorContinuousMultilinear μ (j + s) hs)
            (pureSymmetricTensor μ 0 (0 : Lp ℂ 2 μ))) v u := by
  simp only [wickOutputDerivativeVector, wickOutputSlotVector,
    InnerProductSpace.rankOne_apply, inner_symmetricMixedTensor_pure,
    inner_pureSymmetricTensor, pow_zero, one_smul, map_smul]
  exact smul_comm _ _ _

/-- The SAME actual source tensor derivative contraction retains all outer
creator/annihilator slots, while its contracted slots are precisely those of
the previously earned pure-annihilation/pure-creation contraction. -/
theorem tensorDerivativeContraction_mixed_outer_pairing (a j b q r : ℕ)
    (gs : Fin (a + j) → Lp ℂ 2 μ) (as : Fin q → Lp ℂ 2 μ)
    (hs : Fin (j + b) → Lp ℂ 2 μ) (ks : Fin r → Lp ℂ 2 μ) (v u : Lp ℂ 2 μ) :
    wickKernelPolarized μ (tensorDerivativeContraction (j := j) μ
        (InnerProductSpace.rankOne ℂ (symmetricTensorContinuousMultilinear μ q as)
          (symmetricTensorContinuousMultilinear μ (a + j) gs))
        (InnerProductSpace.rankOne ℂ (symmetricTensorContinuousMultilinear μ (j + b) hs)
          (symmetricTensorContinuousMultilinear μ r ks))) v u =
      ((∏ i : Fin q, inner ℂ v (as i)) * (∏ k : Fin r, inner ℂ (ks k) u)) *
        wickKernelPolarized μ (tensorDerivativeContraction (j := j) μ
          (InnerProductSpace.rankOne ℂ (pureSymmetricTensor μ 0 (0 : Lp ℂ 2 μ))
            (symmetricTensorContinuousMultilinear μ (a + j) gs))
          (InnerProductSpace.rankOne ℂ (symmetricTensorContinuousMultilinear μ (j + b) hs)
            (pureSymmetricTensor μ 0 (0 : Lp ℂ 2 μ)))) v u := by
  let A := InnerProductSpace.rankOne ℂ (symmetricTensorContinuousMultilinear μ q as)
    (symmetricTensorContinuousMultilinear μ (a + j) gs)
  let A0 := InnerProductSpace.rankOne ℂ (pureSymmetricTensor μ 0 (0 : Lp ℂ 2 μ))
    (symmetricTensorContinuousMultilinear μ (a + j) gs)
  let B := InnerProductSpace.rankOne ℂ (symmetricTensorContinuousMultilinear μ (j + b) hs)
    (symmetricTensorContinuousMultilinear μ r ks)
  let B0 := InnerProductSpace.rankOne ℂ (symmetricTensorContinuousMultilinear μ (j + b) hs)
    (pureSymmetricTensor μ 0 (0 : Lp ℂ 2 μ))
  let c : ℂ := (∏ i : Fin q, inner ℂ v (as i)) * (∏ k : Fin r, inner ℂ (ks k) u)
  have hA : wickInputDerivativeFunctional (j := j) μ A v u =
      (∏ i : Fin q, inner ℂ v (as i)) •
        wickInputDerivativeFunctional (j := j) μ A0 v u :=
    wickInputDerivativeFunctional_mixed_outer_factor μ a j q gs as v u
  have hB : wickOutputDerivativeVector (j := j) μ B v u =
      (∏ k : Fin r, inner ℂ (ks k) u) •
        wickOutputDerivativeVector (j := j) μ B0 v u :=
    wickOutputDerivativeVector_mixed_outer_factor μ j b r hs ks v u
  change wickKernelPolarized μ (tensorDerivativeContraction (j := j) μ A B) v u =
    c * wickKernelPolarized μ (tensorDerivativeContraction (j := j) μ A0 B0) v u
  calc
    _ = wickDerivativeDot (j := j) μ A B v u :=
      (wickDerivativeDot_eq_tensorKernel (j := j) μ A B v u).symm
    _ = c * wickDerivativeDot (j := j) μ A0 B0 v u := by
      change wickInputDerivativeFunctional (j := j) μ A v u
          (wickOutputDerivativeVector (j := j) μ B v u) =
        c * wickInputDerivativeFunctional (j := j) μ A0 v u
          (wickOutputDerivativeVector (j := j) μ B0 v u)
      rw [hA, hB, ContinuousLinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul]
      dsimp only [c]
      ring
    _ = c * wickKernelPolarized μ (tensorDerivativeContraction (j := j) μ A0 B0) v u :=
      congrArg (fun z : ℂ => c * z) (wickDerivativeDot_eq_tensorKernel (j := j) μ A0 B0 v u)

end LiebLiniger.FixedPeriod.Quantum
end
