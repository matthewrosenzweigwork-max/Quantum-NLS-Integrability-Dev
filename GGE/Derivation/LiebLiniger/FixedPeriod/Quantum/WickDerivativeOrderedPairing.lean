import LiebLiniger.FixedPeriod.Quantum.OneModeWickNormalOrder
import LiebLiniger.FixedPeriod.Quantum.WickDerivativeContraction
import LiebLiniger.FixedPeriod.Quantum.WickWeightedMatching
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Embedding
import Mathlib.Data.Fintype.CardEmbedding

/-! Bounded source-exact derivative-slot and ordered-pairing producer extracted
from e459 Source7–8. The literal physicalUnusedProduct is imported from the
weighted matching provider. This file is uncompiled and awaiting independent
source review and qualification of its imported exact provider. -/

/- Source-frozen leaf LiebLiniger.FixedPeriod.Quantum.WickMixedProductDerivativeSlots; 37f8b7e8ba62a36f8079370d2e1970953d3433754075227b8b1649f24283719f -/
section Q2024Source7

/-! Actual all-order derivatives of independent physical linear factors.
The UNSYMMETRIZED multilinear product has the SAME diagonal as the actual
mixed-rank-one Wick polynomial. Its real physical tensor derivative extension
therefore equals the explicit ordered-injection sum, proved through actual
complex Frechet derivatives. This is the direct derivative side of the matching
kernel comparison, with no derivative/matching/product premise.
SOURCE ONLY / UNCOMPILED. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace LiebLiniger.FixedPeriod.Quantum
variable {X : Type} [MeasurableSpace X] (μ : Measure X)
  [SigmaFinite μ] [IsFiniteMeasure μ]

/-- Pure pairing with the actual symmetrized MIXED physical tensor. -/
theorem inner_pure_symmetricMixedTensor (p : ℕ) (v : Lp ℂ 2 μ)
    (gs : Fin p → Lp ℂ 2 μ) :
    inner ℂ (pureSymmetricTensor μ p v) (symmetricTensorContinuousMultilinear μ p gs) =
      ∏ i : Fin p, inner ℂ v (gs i) := by
  change inner ℂ (pureTensorL2 (ι := Fin p) μ v) (symmetrizeL2 μ (mixedTensorL2 μ gs)) = _
  rw [wickPureTensor_inner_symmetrize,
    ← mixedTensorL2_diagonal (ι := Fin p) μ v, inner_mixedTensorL2]

/-- The reverse pure pairing, with the actual conjugate-first convention. -/
theorem inner_symmetricMixedTensor_pure (p : ℕ) (gs : Fin p → Lp ℂ 2 μ)
    (u : Lp ℂ 2 μ) :
    inner ℂ (symmetricTensorContinuousMultilinear μ p gs) (pureSymmetricTensor μ p u) =
      ∏ i : Fin p, inner ℂ (gs i) u := by
  have hh := congrArg conj (inner_pure_symmetricMixedTensor μ p u gs)
  simpa only [map_prod, inner_conj_symm] using hh

/-- Independent physical linear forms, without imposing artificial symmetry on
these OFF-diagonal slots. Its actual diagonal is the Wick mixed polynomial. -/
def physicalLinearProductMultilinear (p : ℕ) (gs : Fin p → Lp ℂ 2 μ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin p => Lp ℂ 2 μ) ℂ :=
  (ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin p) ℂ).compContinuousLinearMap
    (fun i => innerSL ℂ (gs i))

@[simp] theorem physicalLinearProductMultilinear_apply (p : ℕ)
    (gs xs : Fin p → Lp ℂ 2 μ) :
    physicalLinearProductMultilinear μ p gs xs = ∏ i : Fin p, inner ℂ (gs i) (xs i) := rfl

/-- Actual j-th complex Frechet derivative as the ordered injection sum.
ALL j/p are retained; an overdegree derivative is zero because there are no
embeddings, and p=0/j=0 are the genuine empty product/tensor cases. -/
theorem physicalLinearProduct_iteratedFDeriv (p j : ℕ) (gs : Fin p → Lp ℂ 2 μ)
    (u : Lp ℂ 2 μ) (dirs : Fin j → Lp ℂ 2 μ) :
    iteratedFDeriv ℂ j (fun x : Lp ℂ 2 μ => ∏ i : Fin p, inner ℂ (gs i) x) u dirs =
      ∑ e : Fin j ↪ Fin p,
        ∏ i : Fin p, inner ℂ (gs i) (wickKernelSlotTuple μ e u dirs i) := by
  classical
  let M := physicalLinearProductMultilinear μ p gs
  have hdiag : (fun x : Lp ℂ 2 μ => M (fun _ => x)) =
      (fun x : Lp ℂ 2 μ => ∏ i : Fin p, inner ℂ (gs i) x) := by
    funext x
    rfl
  rw [← hdiag]
  change iteratedFDeriv ℂ j (M ∘ wickKernelDiagonalMap μ p) u dirs = _
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right _ M.contDiff _ le_rfl,
    ContinuousMultilinearMap.iteratedFDeriv_eq]
  simp only [ContinuousMultilinearMap.iteratedFDeriv,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, sum_apply,
    ContinuousMultilinearMap.iteratedFDerivComponent_apply, Pi.compRightL_apply,
    wickKernelDiagonalMap_apply]
  apply Finset.sum_congr (Finset.ext (fun e => by simp only [Finset.mem_univ]))
  intro e he
  letI : DecidableEq (Fin p) := fun a b => Classical.propDecidable (a = b)
  have ht : (fun i : Fin p => if hi : i ∈ Set.range e then
      dirs (e.toEquivRange.symm ⟨i, hi⟩) else u) = wickKernelSlotTuple μ e u dirs := by
    funext i
    unfold wickKernelSlotTuple
    simp only [Function.Embedding.toEquivRange_eq_ofInjective]
  change M (fun i : Fin p => if hi : i ∈ Set.range e then
      dirs (e.toEquivRange.symm ⟨i, hi⟩) else u) = _
  rw [ht]
  rfl

/-- The independent actual pure-annihilation source kernel has the physical
product of its independently chosen linear forms as its polarized polynomial. -/
theorem wickKernelPolarized_mixed_annihilation (p : ℕ) (gs : Fin p → Lp ℂ 2 μ)
    (v u : Lp ℂ 2 μ) :
    wickKernelPolarized μ
        (InnerProductSpace.rankOne ℂ (pureSymmetricTensor μ 0 (0 : Lp ℂ 2 μ))
          (symmetricTensorContinuousMultilinear μ p gs)) v u =
      ∏ i : Fin p, inner ℂ (gs i) u := by
  simp only [wickKernelPolarized, InnerProductSpace.rankOne_apply, inner_smul_right,
    inner_symmetricMixedTensor_pure, inner_pureSymmetricTensor, pow_zero, mul_one]

/-- Conjugation of the independent actual pure-creation kernel's output
polynomial produces the physical complex-linear forms, with no sign change. -/
theorem conj_wickKernelPolarized_mixed_creation (q : ℕ) (hs : Fin q → Lp ℂ 2 μ)
    (v u : Lp ℂ 2 μ) :
    conj (wickKernelPolarized μ
        (InnerProductSpace.rankOne ℂ (symmetricTensorContinuousMultilinear μ q hs)
          (pureSymmetricTensor μ 0 (0 : Lp ℂ 2 μ))) v u) =
      ∏ i : Fin q, inner ℂ (hs i) v := by
  simp only [wickKernelPolarized, InnerProductSpace.rankOne_apply, inner_smul_right,
    inner_pureSymmetricTensor, pow_zero, one_mul, inner_pure_symmetricMixedTensor,
    map_prod, inner_conj_symm]

/-- ACTUAL source input derivative free functional, evaluated on arbitrary
mixed free tensors, equals the ordered embedding sum of independent fields. -/
theorem wickInputDerivativeFunctional_mixed_annihilation_slots (r j : ℕ)
    (gs : Fin (r + j) → Lp ℂ 2 μ) (v u : Lp ℂ 2 μ)
    (dirs : Fin j → Lp ℂ 2 μ) :
    wickInputDerivativeFunctional (j := j) μ
        (InnerProductSpace.rankOne ℂ (pureSymmetricTensor μ 0 (0 : Lp ℂ 2 μ))
          (symmetricTensorContinuousMultilinear μ (r + j) gs)) v u (mixedTensorL2 μ dirs) =
      ∑ e : Fin j ↪ Fin (r + j),
        ∏ i : Fin (r + j), inner ℂ (gs i) (wickKernelSlotTuple μ e u dirs i) := by
  rw [wickInputDerivativeFunctional_mixed]
  have hf : wickKernelPolarized μ
      (InnerProductSpace.rankOne ℂ (pureSymmetricTensor μ 0 (0 : Lp ℂ 2 μ))
        (symmetricTensorContinuousMultilinear μ (r + j) gs)) v =
      (fun x : Lp ℂ 2 μ => ∏ i : Fin (r + j), inner ℂ (gs i) x) := by
    funext x
    exact wickKernelPolarized_mixed_annihilation μ (r + j) gs v x
  rw [hf]
  exact physicalLinearProduct_iteratedFDeriv μ (r + j) j gs u dirs

/-- ACTUAL source output Riesz vector paired with arbitrary mixed free tensors
has the corresponding genuine ordered derivative-slot sum, all j/s=0 retained. -/
theorem wickOutputDerivativeVector_mixed_creation_slots (j s : ℕ)
    (hs : Fin (j + s) → Lp ℂ 2 μ) (v u : Lp ℂ 2 μ)
    (dirs : Fin j → Lp ℂ 2 μ) :
    inner ℂ (wickOutputDerivativeVector (j := j) μ
        (InnerProductSpace.rankOne ℂ (symmetricTensorContinuousMultilinear μ (j + s) hs)
          (pureSymmetricTensor μ 0 (0 : Lp ℂ 2 μ))) v u) (mixedTensorL2 μ dirs) =
      ∑ e : Fin j ↪ Fin (j + s),
        ∏ i : Fin (j + s), inner ℂ (hs i) (wickKernelSlotTuple μ e v dirs i) := by
  rw [wickOutputDerivativeVector_inner_mixed]
  have hf : (fun x : Lp ℂ 2 μ => conj (wickKernelPolarized μ
      (InnerProductSpace.rankOne ℂ (symmetricTensorContinuousMultilinear μ (j + s) hs)
        (pureSymmetricTensor μ 0 (0 : Lp ℂ 2 μ))) x u)) =
      (fun x : Lp ℂ 2 μ => ∏ i : Fin (j + s), inner ℂ (hs i) x) := by
    funext x
    exact conj_wickKernelPolarized_mixed_creation μ (j + s) hs x u
  rw [hf]
  exact physicalLinearProduct_iteratedFDeriv μ (j + s) j hs v dirs
end LiebLiniger.FixedPeriod.Quantum
end
end Q2024Source7


/- Source-frozen leaf LiebLiniger.FixedPeriod.Quantum.WickOrderedEmbeddingKernelPairing; 4941d70b4283a368f29cc0918aa69c10e1c026b7ac30bab22247ad6f2c4e4b3b -/
section Q2024Source8

/-! ACTUAL source derivative kernel as an ordered embedding-pair scalar sum.
The free functional/Riesz vector are earned on every complete free tensor from
actual all-order derivatives and mixed-tensor density. No matching/kernel
identity is supplied. No ordered complement carrier is constructed: unused
slots are explicit scalar products, so later comparison can use pure pairings
and the already proved complete-sector totality. SOURCE ONLY / UNCOMPILED. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace LiebLiniger.FixedPeriod.Quantum
variable {X : Type} [MeasurableSpace X] (μ : Measure X)
  [SigmaFinite μ] [IsFiniteMeasure μ]

/-- Split the actual ordered physical derivative slots into unused factors and
independent selected-direction factors. Includes j=0 and p=0. -/
theorem physicalLinearProduct_slots_factor {p j : ℕ} (gs : Fin p → Lp ℂ 2 μ)
    (e : Fin j ↪ Fin p) (u : Lp ℂ 2 μ) (dirs : Fin j → Lp ℂ 2 μ) :
    (∏ k : Fin p, inner ℂ (gs k) (wickKernelSlotTuple μ e u dirs k)) =
      physicalUnusedProduct μ gs e u * ∏ i : Fin j, inner ℂ (gs (e i)) (dirs i) := by
  classical
  let f : Fin p → ℂ := fun k => inner ℂ (gs k) (wickKernelSlotTuple μ e u dirs k)
  let selected : Fin p → ℂ := fun k => if k ∈ Set.range e then f k else 1
  let selectedSet : Finset (Fin p) := Finset.univ.map e
  have hmem (k : Fin p) : k ∈ selectedSet ↔ k ∈ Set.range e := by
    simp only [selectedSet, Finset.mem_map, Finset.mem_univ, true_and, Set.mem_range]
  have hselected : (∏ k : Fin p, selected k) =
      ∏ i : Fin j, inner ℂ (gs (e i)) (dirs i) := by
    calc
      _ = ∏ k : Fin p, if k ∈ selectedSet then f k else 1 := by
        apply Finset.prod_congr rfl
        intro k hk
        simp only [selected, hmem]
      _ = ∏ k ∈ selectedSet, f k := Fintype.prod_ite_mem selectedSet f
      _ = _ := by
        change (∏ k ∈ Finset.univ.map e, f k) = _
        rw [Finset.prod_map]
        simp only [f, wickKernelSlotTuple_selected]
  change (∏ k : Fin p, f k) = _
  calc
    _ = ∏ k : Fin p,
        selected k * (if k ∈ Set.range e then 1 else inner ℂ (gs k) u) := by
      apply Finset.prod_congr rfl
      intro k hk
      by_cases hkr : k ∈ Set.range e
      · simp only [selected, if_pos hkr, mul_one]
      · simp only [selected, if_neg hkr, one_mul, f,
          wickKernelSlotTuple, dif_neg hkr]
    _ = (∏ k : Fin p, selected k) * physicalUnusedProduct μ gs e u := by
      rw [Finset.prod_mul_distrib]
      rfl
    _ = _ := by rw [hselected]; exact mul_comm _ _

/-- ACTUAL complete free input functional is the finite ordered embedding sum
of genuine physical inner-product functionals. This earns a representation,
rather than assuming derivative values on arbitrary completed tensor vectors. -/
theorem wickInputDerivativeFunctional_mixed_annihilation_eq_sum (r j : ℕ)
    (gs : Fin (r + j) → Lp ℂ 2 μ) (v u : Lp ℂ 2 μ) :
    wickInputDerivativeFunctional (j := j) μ
        (InnerProductSpace.rankOne ℂ (pureSymmetricTensor μ 0 (0 : Lp ℂ 2 μ))
          (symmetricTensorContinuousMultilinear μ (r + j) gs)) v u =
      ∑ e : Fin j ↪ Fin (r + j), physicalUnusedProduct μ gs e u •
        innerSL ℂ (mixedTensorL2 μ (fun i : Fin j => gs (e i))) := by
  classical
  apply wickContinuousLinearMap_ext_mixed μ
  intro dirs
  rw [wickInputDerivativeFunctional_mixed_annihilation_slots]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    innerSL_apply_apply, inner_mixedTensorL2, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro e he
  exact physicalLinearProduct_slots_factor μ gs e u dirs

/-- ACTUAL complete free output Riesz vector is its finite ordered embedding
sum. The conjugate on the unused factor is earned from conjugate-first pairing,
not silently renamed; every free tensor is covered by proved mixed density. -/
theorem wickOutputDerivativeVector_mixed_creation_eq_sum (j s : ℕ)
    (hs : Fin (j + s) → Lp ℂ 2 μ) (v u : Lp ℂ 2 μ) :
    wickOutputDerivativeVector (j := j) μ
        (InnerProductSpace.rankOne ℂ (symmetricTensorContinuousMultilinear μ (j + s) hs)
          (pureSymmetricTensor μ 0 (0 : Lp ℂ 2 μ))) v u =
      ∑ e : Fin j ↪ Fin (j + s), conj (physicalUnusedProduct μ hs e v) •
        mixedTensorL2 μ (fun i : Fin j => hs (e i)) := by
  classical
  apply sub_eq_zero.mp
  apply mixedTensorL2_eq_zero_of_inner μ
  intro dirs
  rw [inner_sub_left]
  apply sub_eq_zero.mpr
  rw [wickOutputDerivativeVector_mixed_creation_slots]
  simp only [sum_inner, inner_smul_left, inner_mixedTensorL2, star_star]
  apply Finset.sum_congr rfl
  intro e he
  simpa only [starRingEnd_self_apply] using
    physicalLinearProduct_slots_factor μ hs e v dirs

/-- SAME independently constructed source derivative kernel, characterized by
its actual polarized PURE matrix elements as an ordered embedding-pair sum.
Every contraction uses its actual physical inner product; every unselected slot
retains its scalar factor. No j! matching-count identity or product theorem is
a premise. This is the earned analytic side of the remaining weighted bijection. -/
theorem tensorDerivativeContraction_mixed_ordered_pairing (r j s : ℕ)
    (gs : Fin (r + j) → Lp ℂ 2 μ) (hs : Fin (j + s) → Lp ℂ 2 μ)
    (v u : Lp ℂ 2 μ) :
    wickKernelPolarized μ (tensorDerivativeContraction (j := j) μ
        (InnerProductSpace.rankOne ℂ (pureSymmetricTensor μ 0 (0 : Lp ℂ 2 μ))
          (symmetricTensorContinuousMultilinear μ (r + j) gs))
        (InnerProductSpace.rankOne ℂ (symmetricTensorContinuousMultilinear μ (j + s) hs)
          (pureSymmetricTensor μ 0 (0 : Lp ℂ 2 μ)))) v u =
      ∑ a : Fin j ↪ Fin (r + j), ∑ b : Fin j ↪ Fin (j + s),
        physicalUnusedProduct μ gs a u * conj (physicalUnusedProduct μ hs b v) *
          ∏ i : Fin j, inner ℂ (gs (a i)) (hs (b i)) := by
  classical
  let A1 : SymmetricSector μ (r + j) →L[ℂ] SymmetricSector μ 0 :=
    InnerProductSpace.rankOne ℂ (pureSymmetricTensor μ 0 (0 : Lp ℂ 2 μ))
      (symmetricTensorContinuousMultilinear μ (r + j) gs)
  let A2 : SymmetricSector μ 0 →L[ℂ] SymmetricSector μ (j + s) :=
    InnerProductSpace.rankOne ℂ (symmetricTensorContinuousMultilinear μ (j + s) hs)
      (pureSymmetricTensor μ 0 (0 : Lp ℂ 2 μ))
  let F : ProductL2 μ (Fin j) →L[ℂ] ℂ := wickInputDerivativeFunctional μ A1 v u
  let V : ProductL2 μ (Fin j) := wickOutputDerivativeVector μ A2 v u
  let G : ProductL2 μ (Fin j) →L[ℂ] ℂ :=
    ∑ a : Fin j ↪ Fin (r + j), physicalUnusedProduct μ gs a u •
      innerSL ℂ (mixedTensorL2 μ (fun i : Fin j => gs (a i)))
  let W : ProductL2 μ (Fin j) :=
    ∑ b : Fin j ↪ Fin (j + s), conj (physicalUnusedProduct μ hs b v) •
      mixedTensorL2 μ (fun i : Fin j => hs (b i))
  have hF : F = G :=
    wickInputDerivativeFunctional_mixed_annihilation_eq_sum μ r j gs v u
  have hV : V = W :=
    wickOutputDerivativeVector_mixed_creation_eq_sum μ j s hs v u
  change wickKernelPolarized μ (tensorDerivativeContraction (j := j) μ A1 A2) v u = _
  calc
    _ = F V := (wickDerivativeDot_eq_tensorKernel μ A1 A2 v u).symm
    _ = G V := congrArg (fun T : ProductL2 μ (Fin j) →L[ℂ] ℂ => T V) hF
    _ = G W := congrArg (fun z : ProductL2 μ (Fin j) => G z) hV
    _ = _ := by
      dsimp only [G, W]
      simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
        map_sum, map_smul, innerSL_apply_apply, inner_mixedTensorL2,
        smul_eq_mul, Finset.mul_sum, mul_assoc]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      exact mul_left_comm _ _ _
end LiebLiniger.FixedPeriod.Quantum
end
end Q2024Source8


