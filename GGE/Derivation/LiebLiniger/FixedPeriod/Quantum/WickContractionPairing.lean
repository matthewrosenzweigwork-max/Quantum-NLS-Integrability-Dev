import LiebLiniger.FixedPeriod.Quantum.WickTensorComposition

/-!
# Source Wick contraction as the physical derivative free-slot pairing

The two block swaps are actual pullbacks on product measure. Applying the
checked three-block pairing to the actual kernels identifies their composed
contraction with the independently constructed free derivative-slot pairing.
There is no CCR or unspecified intertwiner hypothesis.
-/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace ComplexConjugate
namespace LiebLiniger.FixedPeriod.Quantum

section Swap
variable {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
    (ν : Measure Y) (τ : Measure Z) [SigmaFinite ν] [SigmaFinite τ]

/-- Actual product-measure pullback swaps arbitrary separated L² vectors. -/
theorem wickSeparated_swap (f : Lp ℂ 2 ν) (g : Lp ℂ 2 τ) :
    Lp.compMeasurePreserving Prod.swap (Measure.measurePreserving_swap (μ := τ) (ν := ν))
      (separatedL2 ν τ f g) = separatedL2 τ ν g f := by
  apply Lp.ext
  have hl := Lp.coeFn_compMeasurePreserving (separatedL2 ν τ f g)
    (Measure.measurePreserving_swap (μ := τ) (ν := ν))
  have hm := (Measure.measurePreserving_swap (μ := τ) (ν := ν)).quasiMeasurePreserving.ae_eq_comp
    (separatedL2_coeFn ν τ f g)
  have hr := separatedL2_coeFn τ ν g f
  filter_upwards [hl, hm, hr] with z hl hm hr
  change _ = g z.1 * f z.2 at hr
  change separatedL2 ν τ f g z.swap = f z.2 * g z.1 at hm
  change _ = separatedL2 ν τ f g z.swap at hl
  exact hl.trans (hm.trans ((mul_comm _ _).trans hr.symm))
end Swap

variable {X : Type} [MeasurableSpace X] (μ : Measure X)
  [SigmaFinite μ] [IsFiniteMeasure μ]

/-- The concrete block swap in the source tensor contraction has the literal
factor-swapping action on every separated complete tensor. -/
theorem contractionSwapBlocks_separated (p k : ℕ)
    (f : ProductL2 μ (Fin p)) (g : ProductL2 μ (Fin k)) :
    contractionSwapBlocks μ p k
      (unregroupL2 μ p k (separatedL2 (sectorMeasure μ p) (sectorMeasure μ k) f g)) =
    unregroupL2 μ k p (separatedL2 (sectorMeasure μ k) (sectorMeasure μ p) g f) := by
  change unregroupL2 μ k p
    (Lp.compMeasurePreserving Prod.swap
      (Measure.measurePreserving_swap (μ := sectorMeasure μ k) (ν := sectorMeasure μ p))
      (regroupL2 μ p k (unregroupL2 μ p k
        (separatedL2 (sectorMeasure μ p) (sectorMeasure μ k) f g)))) = _
  rw [regroupL2_unregroupL2, wickSeparated_swap]

/-- Pure physical tensors split into the literal two complete coordinate blocks. -/
theorem wickPureTensor_split (p k : ℕ) (u : Lp ℂ 2 μ) :
    pureTensorL2 (ι := Fin (p + k)) μ u =
      unregroupL2 μ p k (separatedL2 (sectorMeasure μ p) (sectorMeasure μ k)
        (pureTensorL2 (ι := Fin p) μ u) (pureTensorL2 (ι := Fin k) μ u)) := by
  apply (regroupL2 μ p k).injective
  rw [regroupL2_pureTensorL2, regroupL2_unregroupL2]

theorem contractionSwapBlocks_pure (p k : ℕ) (u : Lp ℂ 2 μ) :
    contractionSwapBlocks μ p k (pureTensorL2 (ι := Fin (p + k)) μ u) =
      pureTensorL2 (ι := Fin (k + p)) μ u := by
  rw [wickPureTensor_split μ p k u, contractionSwapBlocks_separated,
    ← wickPureTensor_split μ k p u]

/-- Both equal-index transports are the same actual carrier transport. -/
theorem contractionFullSectorCast_eq_productL2Cast {m n : ℕ} (h : m = n) :
    contractionFullSectorCast μ h = productL2Cast μ h := by
  subst n
  rfl

/-- A literal pure full tensor absorbs the physical orthogonal symmetrizer. -/
theorem wickPureTensor_inner_symmetrize (n : ℕ) (v : Lp ℂ 2 μ)
    (w : ProductL2 μ (Fin n)) :
    inner ℂ (pureTensorL2 (ι := Fin n) μ v) (symmetrizeL2 μ w) =
      inner ℂ (pureTensorL2 (ι := Fin n) μ v) w := by
  have hs := symmetrizeL2_isSymmetric (ι := Fin n) μ
    (pureTensorL2 (ι := Fin n) μ v) w
  change inner ℂ (symmetrizeL2 μ (pureTensorL2 (ι := Fin n) μ v)) w =
    inner ℂ (pureTensorL2 (ι := Fin n) μ v) (symmetrizeL2 μ w) at hs
  rw [symmetrizeL2_pureTensorL2] at hs
  exact hs.symm

/-- Exact physical matrix element of the source three-block contraction.
The first j outputs of A2 are paired with the last j inputs of A1, as recorded
by the independently proved input/output insertions. -/
theorem unscaledTensorContraction_pairing {r j s qb pc : ℕ}
    (A1 : SymmetricSector μ (r + j) →L[ℂ] SymmetricSector μ qb)
    (A2 : SymmetricSector μ pc →L[ℂ] SymmetricSector μ (j + s))
    (v u : Lp ℂ 2 μ) :
    inner ℂ (pureSymmetricTensor μ (qb + s) v)
      (unscaledTensorContraction μ A1 A2 (pureSymmetricTensor μ (r + pc) u)) =
      wickInputSlotFunctional μ A1 v u (wickOutputSlotVector μ A2 v u) := by
  change inner ℂ (pureTensorL2 (ι := Fin (qb + s)) μ v)
    (symmetrizeL2 μ
      (fullTensorLift μ (fullSectorExtension μ A1) s
        (contractionFullSectorCast μ (show r + (j + s) = (r + j) + s by omega)
          (contractionSwapBlocks μ (j + s) r
            (fullTensorLift μ (fullSectorExtension μ A2) r
              (contractionSwapBlocks μ r pc (pureTensorL2 (ι := Fin (r + pc)) μ u))))))) = _
  rw [wickPureTensor_inner_symmetrize]
  rw [contractionSwapBlocks_pure, wickPureTensor_split μ pc r u]
  change inner ℂ (pureTensorL2 (ι := Fin (qb + s)) μ v)
    (fullTensorLift μ (fullSectorExtension μ A1) s
      (contractionFullSectorCast μ (show r + (j + s) = (r + j) + s by omega)
        (contractionSwapBlocks μ (j + s) r
          (fullTensorLift μ (fullSectorExtension μ A2) r
            (unregroupL2 μ pc r (separatedL2 (sectorMeasure μ pc) (sectorMeasure μ r)
              (pureSymmetricTensor μ pc u : ProductL2 μ (Fin pc))
              (pureTensorL2 (ι := Fin r) μ u))))))) = _
  have hA2 := fullSectorExtension_tensor_symmetric μ A2 r
    (pureSymmetricTensor μ pc u) (pureTensorL2 (ι := Fin r) μ u)
  rw [hA2, contractionSwapBlocks_separated,
    contractionFullSectorCast_eq_productL2Cast, wickPureTensor_split μ qb s v,
    ← ContinuousLinearMap.adjoint_inner_left]
  have hadj := fullSectorExtension_tensor_adjoint_symmetric μ A1 s
    (pureSymmetricTensor μ qb v) (pureTensorL2 (ι := Fin s) μ v)
  change (fullTensorLift μ (fullSectorExtension μ A1) s).adjoint
      (unregroupL2 μ qb s (separatedL2 (sectorMeasure μ qb) (sectorMeasure μ s)
        (pureTensorL2 (ι := Fin qb) μ v) (pureTensorL2 (ι := Fin s) μ v))) =
    unregroupL2 μ (r + j) s
      (separatedL2 (sectorMeasure μ (r + j)) (sectorMeasure μ s)
        (A1.adjoint (pureSymmetricTensor μ qb v) : ProductL2 μ (Fin (r + j)))
        (pureTensorL2 (ι := Fin s) μ v)) at hadj
  rw [hadj]
  change inner ℂ
    (unregroupL2 μ (r + j) s (separatedL2 (sectorMeasure μ (r + j)) (sectorMeasure μ s)
      (A1.adjoint (pureSymmetricTensor μ qb v) : ProductL2 μ (Fin (r + j)))
      (pureTensorL2 (ι := Fin s) μ v)))
    (productL2Cast μ (Nat.add_assoc r j s).symm
      (wickFullLeftInsertion μ r (j + s) u
        (A2 (pureSymmetricTensor μ pc u) : ProductL2 μ (Fin (j + s))))) = _
  have hi := wickInputTensorInsertion_adjoint μ r j u
    (A1.adjoint (pureSymmetricTensor μ qb v))
  have ho := wickOutputTensorInsertion_adjoint μ j s v (A2 (pureSymmetricTensor μ pc u))
  rw [wickThreeBlock_pairing μ r j s u v, ← hi, ← ho,
    ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]
  rfl

/-- Multiplying by the actual source falling factorials identifies the
polarized polynomial of the concrete contraction kernel with the physical
free-slot derivative pairing. -/
theorem tensorDerivativeContraction_polarized {r j s qb pc : ℕ}
    (A1 : SymmetricSector μ (r + j) →L[ℂ] SymmetricSector μ qb)
    (A2 : SymmetricSector μ pc →L[ℂ] SymmetricSector μ (j + s))
    (v u : Lp ℂ 2 μ) :
    wickKernelPolarized μ (tensorDerivativeContraction μ A1 A2) v u =
      (r + j).descFactorial j • ((j + s).descFactorial j •
        wickInputSlotFunctional μ A1 v u (wickOutputSlotVector μ A2 v u)) := by
  change inner ℂ (pureSymmetricTensor μ (qb + s) v)
    ((((((r + j).descFactorial j : ℝ) * ((j + s).descFactorial j : ℝ) : ℝ) : ℂ) •
      unscaledTensorContraction μ A1 A2) (pureSymmetricTensor μ (r + pc) u)) = _
  rw [ContinuousLinearMap.smul_apply, inner_smul_right (𝕜 := ℂ),
    unscaledTensorContraction_pairing]
  rw [← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ]
  simp only [Complex.ofReal_mul, Complex.ofReal_natCast, smul_eq_mul]
  ring

end LiebLiniger.FixedPeriod.Quantum
