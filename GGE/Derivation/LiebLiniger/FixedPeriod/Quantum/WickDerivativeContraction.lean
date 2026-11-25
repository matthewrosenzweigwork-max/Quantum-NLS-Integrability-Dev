import LiebLiniger.FixedPeriod.Quantum.WickContractionPairing

/-!
# Actual derivative contraction represented by the source tensor kernel

The derivative functional and Riesz vector are constructed independently from
physical tensor insertion. Their action on arbitrary elementary tensors is
proved equal to the actual iterated Fréchet derivatives. Their Hilbert pairing
is then represented by the concrete source three-block contraction kernel.
No kernel identity is built into the derivative-dot definition.
-/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace ComplexConjugate
namespace LiebLiniger.FixedPeriod.Quantum
variable {X : Type} [MeasurableSpace X] (μ : Measure X)
  [SigmaFinite μ] [IsFiniteMeasure μ]

/-- The genuine j-th input derivative extended to the complete free tensor. -/
def wickInputDerivativeFunctional {r j qb : ℕ}
    (A1 : SymmetricSector μ (r + j) →L[ℂ] SymmetricSector μ qb)
    (v u : Lp ℂ 2 μ) : ProductL2 μ (Fin j) →L[ℂ] ℂ :=
  ((r + j).descFactorial j : ℂ) • wickInputSlotFunctional μ A1 v u

/-- The actual Riesz vector for the j-th conjugated output derivative. -/
def wickOutputDerivativeVector {pc j s : ℕ}
    (A2 : SymmetricSector μ pc →L[ℂ] SymmetricSector μ (j + s))
    (v u : Lp ℂ 2 μ) : ProductL2 μ (Fin j) :=
  ((j + s).descFactorial j : ℂ) • wickOutputSlotVector μ A2 v u

/-- The input extension agrees with the actual derivative on every elementary
family, including j=0; this is not a derivative assumption. -/
theorem wickInputDerivativeFunctional_mixed {r j qb : ℕ}
    (A1 : SymmetricSector μ (r + j) →L[ℂ] SymmetricSector μ qb)
    (v u : Lp ℂ 2 μ) (h : Fin j → Lp ℂ 2 μ) :
    wickInputDerivativeFunctional μ A1 v u (mixedTensorL2 μ h) =
      iteratedFDeriv ℂ j (wickKernelPolarized μ A1 v) u h := by
  rw [wickKernelPolarized_iteratedFDeriv_input_tensor]
  change ((r + j).descFactorial j : ℂ) •
      inner ℂ (pureSymmetricTensor μ qb v)
        (A1 (wickInputTensorInsertion μ r j u (mixedTensorL2 μ h))) = _
  rw [Nat.cast_smul_eq_nsmul]

/-- The output vector represents the actual conjugated derivative against every
arbitrary elementary free tensor, with the inner-product conjugation checked. -/
theorem wickOutputDerivativeVector_inner_mixed {pc j s : ℕ}
    (A2 : SymmetricSector μ pc →L[ℂ] SymmetricSector μ (j + s))
    (v u : Lp ℂ 2 μ) (h : Fin j → Lp ℂ 2 μ) :
    inner ℂ (wickOutputDerivativeVector μ A2 v u) (mixedTensorL2 μ h) =
      iteratedFDeriv ℂ j (fun w => conj (wickKernelPolarized μ A2 w u)) v h := by
  rw [wickKernelPolarized_iteratedFDeriv_conj_output_tensor]
  change inner ℂ (((j + s).descFactorial j : ℂ) • wickOutputSlotVector μ A2 v u)
    (mixedTensorL2 μ h) = _
  rw [inner_smul_left (𝕜 := ℂ)]
  simp only [map_natCast, ← Nat.cast_smul_eq_nsmul ℂ, smul_eq_mul,
    wickOutputSlotVector]

/-- Physical derivative-dot contraction, defined from the independently proved
derivative functional and its output Riesz vector, without a target kernel. -/
def wickDerivativeDot {r j s qb pc : ℕ}
    (A1 : SymmetricSector μ (r + j) →L[ℂ] SymmetricSector μ qb)
    (A2 : SymmetricSector μ pc →L[ℂ] SymmetricSector μ (j + s))
    (v u : Lp ℂ 2 μ) : ℂ :=
  wickInputDerivativeFunctional μ A1 v u (wickOutputDerivativeVector μ A2 v u)

/-- Source Q2-025 representation: the independently defined physical j-th
derivative-dot polynomial has exactly the concrete contraction kernel, with
both falling factorials and the source tensor slot order. -/
theorem wickDerivativeDot_eq_tensorKernel {r j s qb pc : ℕ}
    (A1 : SymmetricSector μ (r + j) →L[ℂ] SymmetricSector μ qb)
    (A2 : SymmetricSector μ pc →L[ℂ] SymmetricSector μ (j + s))
    (v u : Lp ℂ 2 μ) :
    wickDerivativeDot μ A1 A2 v u =
      wickKernelPolarized μ (tensorDerivativeContraction μ A1 A2) v u := by
  rw [tensorDerivativeContraction_polarized]
  change ((r + j).descFactorial j : ℂ) •
    wickInputSlotFunctional μ A1 v u
      (((j + s).descFactorial j : ℂ) • wickOutputSlotVector μ A2 v u) = _
  rw [map_smul, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]

end LiebLiniger.FixedPeriod.Quantum
