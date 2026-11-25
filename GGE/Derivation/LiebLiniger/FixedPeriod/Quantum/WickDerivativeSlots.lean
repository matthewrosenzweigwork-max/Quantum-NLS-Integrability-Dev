import LiebLiniger.FixedPeriod.Quantum.WickDerivatives
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fintype.CardEmbedding

/-!
# Ordered physical derivative slots and their falling factorials

For the genuine source kernel polynomial, every j-th holomorphic derivative is
an ordered sum over injections Fin j -> Fin p of the actual tensor directions.
Symmetry identifies these terms and the number of injections is (p)_j.
The output variable is conjugated before taking its complex derivative.
The chosen input slots are the last j, and the chosen output slots the first j,
matching the source contraction order. The pairing of these remaining free
slots and identification with the physical composed contraction is still open.

This is a source-written candidate; only the root compiler lane validates it.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace ComplexConjugate ContDiff

namespace LiebLiniger.FixedPeriod.Quantum

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]

/-- Insert j independently specified directions into the ordered slots selected
by an injection, filling every other physical tensor slot by u. -/
def wickKernelSlotTuple {p j : ℕ} (e : Fin j ↪ Fin p)
    (u : Lp ℂ 2 μ) (h : Fin j → Lp ℂ 2 μ) : Fin p → Lp ℂ 2 μ :=
  fun i => if hi : i ∈ Set.range e then h (e.toEquivRange.symm ⟨i, hi⟩) else u

@[simp] theorem wickKernelSlotTuple_selected {p j : ℕ} (e : Fin j ↪ Fin p)
    (u : Lp ℂ 2 μ) (h : Fin j → Lp ℂ 2 μ) (i : Fin j) :
    wickKernelSlotTuple μ e u h (e i) = h i := by
  simp [wickKernelSlotTuple]

/-- The physical polynomial is complex smooth in its holomorphic input slot. -/
theorem wickKernelPolarized_contDiff_input {p q : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q)
    (v : Lp ℂ 2 μ) (n : ℕ∞ω) : ContDiff ℂ n (wickKernelPolarized μ A v) := by
  have hc : ContDiff ℂ n
      (wickKernelInputMultilinear μ A v ∘ wickKernelDiagonalMap μ p) :=
    (wickKernelInputMultilinear μ A v).contDiff.comp (wickKernelDiagonalMap μ p).contDiff
  simpa only [Function.comp_def, wickKernelDiagonalMap_apply,
    wickKernelInputMultilinear_diagonal] using hc

/-- Literal ordered-slot formula for every iterated input derivative. There are
no embeddings when j>p, so this formula also states exact derivative vanishing. -/
theorem wickKernelPolarized_iteratedFDeriv_input_slots {p q j : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q)
    (v u : Lp ℂ 2 μ) (h : Fin j → Lp ℂ 2 μ) :
    iteratedFDeriv ℂ j (wickKernelPolarized μ A v) u h =
      ∑ e : Fin j ↪ Fin p, inner ℂ (pureSymmetricTensor μ q v)
        (A (symmetricTensorContinuousMultilinear μ p (wickKernelSlotTuple μ e u h))) := by
  classical
  have hdiag : (fun x => wickKernelInputMultilinear μ A v (fun _ => x)) =
      wickKernelPolarized μ A v := by
    funext x
    exact wickKernelInputMultilinear_diagonal μ A v x
  rw [← hdiag]
  change iteratedFDeriv ℂ j
    (wickKernelInputMultilinear μ A v ∘ wickKernelDiagonalMap μ p) u h = _
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right _
    (wickKernelInputMultilinear μ A v).contDiff _ le_rfl,
    ContinuousMultilinearMap.iteratedFDeriv_eq]
  simp only [ContinuousMultilinearMap.iteratedFDeriv,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    sum_apply,
    ContinuousMultilinearMap.iteratedFDerivComponent_apply, Pi.compRightL_apply,
    wickKernelDiagonalMap_apply, wickKernelInputMultilinear_apply]
  apply Finset.sum_congr (Finset.ext (fun e => by simp only [Finset.mem_univ]))
  intro e he
  letI : DecidableEq (Fin p) := fun a b => Classical.propDecidable (a = b)
  have ht : (fun i : Fin p => if hi : i ∈ Set.range e then
      h (e.toEquivRange.symm ⟨i, hi⟩) else u) = wickKernelSlotTuple μ e u h := by
    funext i
    unfold wickKernelSlotTuple
    simp only [Function.Embedding.toEquivRange_eq_ofInjective]
  exact congrArg (fun t : Fin p → Lp ℂ 2 μ =>
    inner ℂ (pureSymmetricTensor μ q v) (A (symmetricTensorContinuousMultilinear μ p t))) ht

/-- Actual symmetric tensors identify all ordered choices of j slots, even with
repeated direction vectors. The permutation is built from the two injections. -/
theorem symmetricTensor_wickKernelSlotTuple_eq {p j : ℕ}
    (e e₀ : Fin j ↪ Fin p) (u : Lp ℂ 2 μ) (h : Fin j → Lp ℂ 2 μ) :
    symmetricTensorContinuousMultilinear μ p (wickKernelSlotTuple μ e u h) =
      symmetricTensorContinuousMultilinear μ p (wickKernelSlotTuple μ e₀ u h) := by
  classical
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair e e₀ e.injective e₀.injective
  have ht : wickKernelSlotTuple μ e u h =
      fun i => wickKernelSlotTuple μ e₀ u h (σ i) := by
    funext i
    by_cases hi : i ∈ Set.range e
    · obtain ⟨k, rfl⟩ := hi
      rw [hσ]
      simp only [wickKernelSlotTuple_selected]
    · have hi₀ : σ i ∉ Set.range e₀ := by
        rintro ⟨k, hk⟩
        apply hi
        exact ⟨k, σ.injective ((hσ k).trans hk)⟩
      simp only [wickKernelSlotTuple, dif_neg hi, dif_neg hi₀]
  rw [ht]
  exact symmetricTensorContinuousMultilinear_permutation μ p σ _

/-- Source normalization of the j-th input derivative: the last j physical
input slots carry the directions, multiplied by the exact falling factorial. -/
theorem wickKernelPolarized_iteratedFDeriv_input_falling {p q j : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q)
    (hj : j ≤ p) (v u : Lp ℂ 2 μ) (h : Fin j → Lp ℂ 2 μ) :
    iteratedFDeriv ℂ j (wickKernelPolarized μ A v) u h =
      p.descFactorial j • inner ℂ (pureSymmetricTensor μ q v)
        (A (symmetricTensorContinuousMultilinear μ p
          (wickKernelSlotTuple μ (Fin.natAdd_castLEEmb hj) u h))) := by
  classical
  rw [wickKernelPolarized_iteratedFDeriv_input_slots]
  simp_rw [symmetricTensor_wickKernelSlotTuple_eq μ _ (Fin.natAdd_castLEEmb hj)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_embedding_eq,
    Fintype.card_fin]

/-- Literal ordered-slot formula for the conjugated output polynomial. -/
theorem wickKernelPolarized_iteratedFDeriv_conj_output_slots {p q j : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q)
    (u v : Lp ℂ 2 μ) (h : Fin j → Lp ℂ 2 μ) :
    iteratedFDeriv ℂ j (fun w => conj (wickKernelPolarized μ A w u)) v h =
      ∑ e : Fin j ↪ Fin q, inner ℂ (A (pureSymmetricTensor μ p u))
        (symmetricTensorContinuousMultilinear μ q (wickKernelSlotTuple μ e v h)) := by
  classical
  have hdiag : (fun x => wickKernelConjugateOutputMultilinear μ A u (fun _ => x)) =
      (fun x => conj (wickKernelPolarized μ A x u)) := by
    funext x
    exact wickKernelConjugateOutputMultilinear_diagonal μ A u x
  rw [← hdiag]
  change iteratedFDeriv ℂ j
    (wickKernelConjugateOutputMultilinear μ A u ∘ wickKernelDiagonalMap μ q) v h = _
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right _
    (wickKernelConjugateOutputMultilinear μ A u).contDiff _ le_rfl,
    ContinuousMultilinearMap.iteratedFDeriv_eq]
  simp only [ContinuousMultilinearMap.iteratedFDeriv,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    sum_apply,
    ContinuousMultilinearMap.iteratedFDerivComponent_apply, Pi.compRightL_apply,
    wickKernelDiagonalMap_apply, wickKernelConjugateOutputMultilinear_apply]
  apply Finset.sum_congr (Finset.ext (fun e => by simp only [Finset.mem_univ]))
  intro e he
  letI : DecidableEq (Fin q) := fun a b => Classical.propDecidable (a = b)
  have ht : (fun i : Fin q => if hi : i ∈ Set.range e then
      h (e.toEquivRange.symm ⟨i, hi⟩) else v) = wickKernelSlotTuple μ e v h := by
    funext i
    unfold wickKernelSlotTuple
    simp only [Function.Embedding.toEquivRange_eq_ofInjective]
  exact congrArg (fun t : Fin q → Lp ℂ 2 μ =>
    inner ℂ (A (pureSymmetricTensor μ p u)) (symmetricTensorContinuousMultilinear μ q t)) ht

/-- Source normalization in the output slot: conjugation makes this an actual
complex Fréchet derivative, with directions in the first j physical slots. -/
theorem wickKernelPolarized_iteratedFDeriv_conj_output_falling {p q j : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q)
    (hj : j ≤ q) (u v : Lp ℂ 2 μ) (h : Fin j → Lp ℂ 2 μ) :
    iteratedFDeriv ℂ j (fun w => conj (wickKernelPolarized μ A w u)) v h =
      q.descFactorial j • inner ℂ (A (pureSymmetricTensor μ p u))
        (symmetricTensorContinuousMultilinear μ q
          (wickKernelSlotTuple μ (Fin.castLEEmb hj) v h)) := by
  classical
  rw [wickKernelPolarized_iteratedFDeriv_conj_output_slots]
  simp_rw [symmetricTensor_wickKernelSlotTuple_eq μ _ (Fin.castLEEmb hj)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_embedding_eq,
    Fintype.card_fin]

end LiebLiniger.FixedPeriod.Quantum
