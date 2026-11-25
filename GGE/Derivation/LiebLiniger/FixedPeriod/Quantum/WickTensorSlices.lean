import LiebLiniger.FixedPeriod.Quantum.WickDerivativeSlots
import LiebLiniger.FixedPeriod.Quantum.CanonicalTensorAction
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Physical Hilbert-tensor representatives of derivative slots

The free j derivative slots are represented on the genuine completed j-particle
spatial Hilbert tensor. The input insertion fills the first r positions by u;
the output insertion fills the last s positions by v. The adjoint of the latter
is the actual Riesz representative of the conjugated output derivative.
No tensor contraction identity or target commutator is assumed here.

Source-written candidate; only the root's compiler lane validates it.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace ComplexConjugate
namespace LiebLiniger.FixedPeriod.Quantum

section SeparatedContinuous
variable {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
    (ν : Measure Y) (τ : Measure Z) [SigmaFinite ν] [SigmaFinite τ]

/-- Tensor by a fixed left vector, on the actual spatial Hilbert product. -/
def wickSeparatedRight (f : Lp ℂ 2 ν) : Lp ℂ 2 τ →L[ℂ] Lp ℂ 2 (ν.prod τ) :=
  (separatedL2Bilinear ν τ f).mkContinuous ‖f‖ (by
    intro g
    exact (norm_separatedL2 ν τ f g).le)

/-- Tensor by a fixed right vector, preserving the order of tensor factors. -/
def wickSeparatedLeft (g : Lp ℂ 2 τ) : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 (ν.prod τ) :=
  ({ toFun := fun f => separatedL2 ν τ f g
     map_add' := fun f f' => separatedL2_add_left ν τ f f' g
     map_smul' := fun c f => separatedL2_smul_left ν τ c f g } :
      Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 (ν.prod τ)).mkContinuous ‖g‖ (by
    intro f
    exact ((norm_separatedL2 ν τ f g).trans (mul_comm _ _)).le)

end SeparatedContinuous

variable {X : Type} [MeasurableSpace X] (μ : Measure X)
  [SigmaFinite μ] [IsFiniteMeasure μ]

/-- Fill the first r input slots by u and leave the last j slots free. -/
def wickInputTensorInsertion (r j : ℕ) (u : Lp ℂ 2 μ) :
    ProductL2 μ (Fin j) →L[ℂ] SymmetricSector μ (r + j) :=
  symmetricSectorProjection μ (r + j) ∘L (unregroupL2 μ r j).toContinuousLinearMap ∘L
    wickSeparatedRight (sectorMeasure μ r) (sectorMeasure μ j)
      (pureTensorL2 (ι := Fin r) μ u)

/-- Leave the first j output slots free and fill the last s slots by v. -/
def wickOutputTensorInsertion (j s : ℕ) (v : Lp ℂ 2 μ) :
    ProductL2 μ (Fin j) →L[ℂ] SymmetricSector μ (j + s) :=
  symmetricSectorProjection μ (j + s) ∘L (unregroupL2 μ j s).toContinuousLinearMap ∘L
    wickSeparatedLeft (sectorMeasure μ j) (sectorMeasure μ s)
      (pureTensorL2 (ι := Fin s) μ v)

/-- Input insertion has the literal arbitrary elementary-tensor action. -/
theorem wickInputTensorInsertion_mixed (r j : ℕ) (u : Lp ℂ 2 μ)
    (h : Fin j → Lp ℂ 2 μ) :
    wickInputTensorInsertion μ r j u (mixedTensorL2 μ h) =
      symmetricTensorContinuousMultilinear μ (r + j)
        (tensorFamilyAppend μ (fun _ => u) h) := by
  apply Subtype.ext
  change symmetrizeL2 μ
      (unregroupL2 μ r j (separatedL2 (sectorMeasure μ r) (sectorMeasure μ j)
        (pureTensorL2 (ι := Fin r) μ u) (mixedTensorL2 μ h))) =
    symmetrizeL2 μ (mixedTensorL2 μ (tensorFamilyAppend μ (fun _ : Fin r => u) h))
  congr 1
  apply (regroupL2 μ r j).injective
  rw [regroupL2_unregroupL2, regroupL2_mixedTensorL2, mixedTensorL2_diagonal]

/-- Output insertion has the literal arbitrary elementary-tensor action. -/
theorem wickOutputTensorInsertion_mixed (j s : ℕ) (v : Lp ℂ 2 μ)
    (h : Fin j → Lp ℂ 2 μ) :
    wickOutputTensorInsertion μ j s v (mixedTensorL2 μ h) =
      symmetricTensorContinuousMultilinear μ (j + s)
        (tensorFamilyAppend μ h (fun _ => v)) := by
  apply Subtype.ext
  change symmetrizeL2 μ
      (unregroupL2 μ j s (separatedL2 (sectorMeasure μ j) (sectorMeasure μ s)
        (mixedTensorL2 μ h) (pureTensorL2 (ι := Fin s) μ v))) =
    symmetrizeL2 μ (mixedTensorL2 μ (tensorFamilyAppend μ h (fun _ : Fin s => v)))
  congr 1
  apply (regroupL2 μ j s).injective
  rw [regroupL2_unregroupL2, regroupL2_mixedTensorL2, mixedTensorL2_diagonal]

/-- The source's last-j-slot insertion is the actual coordinate concatenation. -/
theorem wickKernelSlotTuple_natAdd (r j : ℕ) (u : Lp ℂ 2 μ)
    (h : Fin j → Lp ℂ 2 μ) :
    wickKernelSlotTuple μ (Fin.natAddEmb r) u h =
      tensorFamilyAppend μ (fun _ : Fin r => u) h := by
  classical
  funext i
  obtain ⟨i, rfl⟩ := (finSumFinEquiv : Fin r ⊕ Fin j ≃ Fin (r + j)).surjective i
  cases i with
  | inl a =>
    have ha : finSumFinEquiv (Sum.inl a) ∉ Set.range (Fin.natAddEmb r (m := j)) := by
      rintro ⟨k, hk⟩
      have hv := congrArg Fin.val hk
      simp only [finSumFinEquiv_apply_left, Fin.natAddEmb_apply, Fin.val_natAdd,
        Fin.val_castAdd] at hv
      omega
    simp only [wickKernelSlotTuple, dif_neg ha, tensorFamilyAppend,
      Equiv.symm_apply_apply, Sum.elim_inl]
  | inr a =>
    rw [finSumFinEquiv_apply_right]
    change wickKernelSlotTuple μ (Fin.natAddEmb r) u h ((Fin.natAddEmb r) a) = _
    rw [wickKernelSlotTuple_selected]
    simp only [tensorFamilyAppend, finSumFinEquiv_symm_apply_natAdd, Sum.elim_inr]

/-- The source's first-j-slot insertion is the actual coordinate concatenation. -/
theorem wickKernelSlotTuple_castAdd (j s : ℕ) (v : Lp ℂ 2 μ)
    (h : Fin j → Lp ℂ 2 μ) :
    wickKernelSlotTuple μ (Fin.castAddEmb s) v h =
      tensorFamilyAppend μ h (fun _ : Fin s => v) := by
  classical
  funext i
  obtain ⟨i, rfl⟩ := (finSumFinEquiv : Fin j ⊕ Fin s ≃ Fin (j + s)).surjective i
  cases i with
  | inl a =>
    rw [finSumFinEquiv_apply_left]
    change wickKernelSlotTuple μ (Fin.castAddEmb s) v h ((Fin.castAddEmb s) a) = _
    rw [wickKernelSlotTuple_selected]
    simp only [tensorFamilyAppend, finSumFinEquiv_symm_apply_castAdd, Sum.elim_inl]
  | inr a =>
    have ha : finSumFinEquiv (Sum.inr a) ∉ Set.range (Fin.castAddEmb s (n := j)) := by
      rintro ⟨k, hk⟩
      have hv := congrArg Fin.val hk
      simp only [finSumFinEquiv_apply_right, Fin.castAddEmb_apply, Fin.val_natAdd,
        Fin.val_castAdd] at hv
      omega
    simp only [wickKernelSlotTuple, dif_neg ha, tensorFamilyAppend,
      Equiv.symm_apply_apply, Sum.elim_inr]

/-- The actual j-th input derivative is represented on the genuine j-fold
Hilbert tensor by the bounded input insertion, with its exact falling factorial. -/
theorem wickKernelPolarized_iteratedFDeriv_input_tensor {r j q : ℕ}
    (A : SymmetricSector μ (r + j) →L[ℂ] SymmetricSector μ q)
    (v u : Lp ℂ 2 μ) (h : Fin j → Lp ℂ 2 μ) :
    iteratedFDeriv ℂ j (wickKernelPolarized μ A v) u h =
      (r + j).descFactorial j • inner ℂ (pureSymmetricTensor μ q v)
        (A (wickInputTensorInsertion μ r j u (mixedTensorL2 μ h))) := by
  classical
  rw [wickKernelPolarized_iteratedFDeriv_input_slots]
  have hs (e : Fin j ↪ Fin (r + j)) :
      symmetricTensorContinuousMultilinear μ (r + j) (wickKernelSlotTuple μ e u h) =
        wickInputTensorInsertion μ r j u (mixedTensorL2 μ h) := by
    rw [symmetricTensor_wickKernelSlotTuple_eq μ e (Fin.natAddEmb r),
      wickKernelSlotTuple_natAdd, wickInputTensorInsertion_mixed]
  simp only [hs, Finset.sum_const, Finset.card_univ, Fintype.card_embedding_eq,
    Fintype.card_fin]

/-- The actual conjugated output derivative is represented by the adjoint of
the physical output insertion. This is the Riesz free-slot vector, constructed
from the genuine kernel and tensor maps rather than postulated as a contraction. -/
theorem wickKernelPolarized_iteratedFDeriv_conj_output_tensor {p j s : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ (j + s))
    (u v : Lp ℂ 2 μ) (h : Fin j → Lp ℂ 2 μ) :
    iteratedFDeriv ℂ j (fun w => conj (wickKernelPolarized μ A w u)) v h =
      (j + s).descFactorial j • inner ℂ
        ((wickOutputTensorInsertion μ j s v).adjoint (A (pureSymmetricTensor μ p u)))
        (mixedTensorL2 μ h) := by
  classical
  rw [wickKernelPolarized_iteratedFDeriv_conj_output_slots]
  have hs (e : Fin j ↪ Fin (j + s)) :
      symmetricTensorContinuousMultilinear μ (j + s) (wickKernelSlotTuple μ e v h) =
        wickOutputTensorInsertion μ j s v (mixedTensorL2 μ h) := by
    rw [symmetricTensor_wickKernelSlotTuple_eq μ e (Fin.castAddEmb s),
      wickKernelSlotTuple_castAdd, wickOutputTensorInsertion_mixed]
  simp only [hs, Finset.sum_const, Finset.card_univ, Fintype.card_embedding_eq,
    Fintype.card_fin, ContinuousLinearMap.adjoint_inner_left]

end LiebLiniger.FixedPeriod.Quantum
