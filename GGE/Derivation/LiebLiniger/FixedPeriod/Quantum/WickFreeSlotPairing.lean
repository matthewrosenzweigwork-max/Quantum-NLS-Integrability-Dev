import LiebLiniger.FixedPeriod.Quantum.WickTensorSlices
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Summable pairing of the actual free derivative tensor slots

The physical input derivative is a bounded linear functional on the complete
j-fold tensor; the conjugated output derivative has a Riesz representative
constructed by the output insertion adjoint. Their scalar contraction is
expressed below in every actual Hilbert basis, with HasSum proved before any
totalized tsum is used. No finite-mode cutoff or contraction theorem is assumed.
The equality of this pairing with the three-block Wick contraction is separate.
-/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace ComplexConjugate
namespace LiebLiniger.FixedPeriod.Quantum

variable {X : Type} [MeasurableSpace X] (μ : Measure X)
  [SigmaFinite μ] [IsFiniteMeasure μ]

/-- The actual linear extension of the input derivative to its free Hilbert
tensor slots, before multiplication by the source falling factorial. -/
def wickInputSlotFunctional {r j qb : ℕ}
    (A1 : SymmetricSector μ (r + j) →L[ℂ] SymmetricSector μ qb)
    (v u : Lp ℂ 2 μ) : ProductL2 μ (Fin j) →L[ℂ] ℂ :=
  (innerSL ℂ (pureSymmetricTensor μ qb v)).comp
    (A1.comp (wickInputTensorInsertion μ r j u))

/-- The actual Riesz vector of the conjugated output derivative, before its
falling factorial, including the empty free tensor when j=0. -/
def wickOutputSlotVector {pc j s : ℕ}
    (A2 : SymmetricSector μ pc →L[ℂ] SymmetricSector μ (j + s))
    (v u : Lp ℂ 2 μ) : ProductL2 μ (Fin j) :=
  (wickOutputTensorInsertion μ j s v).adjoint (A2 (pureSymmetricTensor μ pc u))

/-- Basis expansion of the physical derivative-slot pairing. The sum is proved
to converge; no divergent tsum or formal coefficient expansion is used. -/
theorem wickFreeSlotPairing_hasSum {r j s qb pc : ℕ} {ι : Type*}
    (A1 : SymmetricSector μ (r + j) →L[ℂ] SymmetricSector μ qb)
    (A2 : SymmetricSector μ pc →L[ℂ] SymmetricSector μ (j + s))
    (v u : Lp ℂ 2 μ) (e : HilbertBasis ι ℂ (ProductL2 μ (Fin j))) :
    HasSum (fun k => wickInputSlotFunctional μ A1 v u (e k) *
      conj (inner ℂ (A2 (pureSymmetricTensor μ pc u))
        (wickOutputTensorInsertion μ j s v (e k))))
      (wickInputSlotFunctional μ A1 v u (wickOutputSlotVector μ A2 v u)) := by
  have hc (k : ι) : conj (inner ℂ (A2 (pureSymmetricTensor μ pc u))
      (wickOutputTensorInsertion μ j s v (e k))) =
        inner ℂ (e k) (wickOutputSlotVector μ A2 v u) := by
    rw [← ContinuousLinearMap.adjoint_inner_left, inner_conj_symm]
    rfl
  have hs := (e.hasSum_repr (wickOutputSlotVector μ A2 v u)).mapL
    (wickInputSlotFunctional μ A1 v u)
  simpa only [map_smul, smul_eq_mul, e.repr_apply_apply, hc, mul_comm] using hs

/-- The preceding HasSum justifies the basis-independent infinite contraction. -/
theorem wickFreeSlotPairing_tsum {r j s qb pc : ℕ} {ι : Type*}
    (A1 : SymmetricSector μ (r + j) →L[ℂ] SymmetricSector μ qb)
    (A2 : SymmetricSector μ pc →L[ℂ] SymmetricSector μ (j + s))
    (v u : Lp ℂ 2 μ) (e : HilbertBasis ι ℂ (ProductL2 μ (Fin j))) :
    ∑' k, wickInputSlotFunctional μ A1 v u (e k) *
      conj (inner ℂ (A2 (pureSymmetricTensor μ pc u))
        (wickOutputTensorInsertion μ j s v (e k))) =
      wickInputSlotFunctional μ A1 v u (wickOutputSlotVector μ A2 v u) :=
  (wickFreeSlotPairing_hasSum μ A1 A2 v u e).tsum_eq

end LiebLiniger.FixedPeriod.Quantum
