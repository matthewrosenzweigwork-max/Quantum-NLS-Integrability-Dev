import LiebLiniger.FixedPeriod.Quantum.WickTensorAdjoints
import LiebLiniger.FixedPeriod.Quantum.WickFreeSlotPairing
import LiebLiniger.FixedPeriod.Quantum.WickProducts
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Actual three-block Hilbert-tensor composition for Wick contraction

All maps below use the complete product-L² tensor realization. The associativity
identity is proved on arbitrary elementary families and extended by the proved
density theorem. The resulting pairing moves exactly the first j output slots
into the last j input slots. No tensor interchange or contraction is assumed.
-/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace BigOperators ComplexConjugate
namespace LiebLiniger.FixedPeriod.Quantum
variable {X : Type} [MeasurableSpace X] (μ : Measure X)
  [SigmaFinite μ] [IsFiniteMeasure μ]

/-- Actual elementary tensors span a dense subspace, by their established
orthogonality characterization. -/
theorem wickMixedTensor_dense_span (n : ℕ) :
    (Submodule.span ℂ (Set.range (mixedTensorL2 (ι := Fin n) μ))).topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro f hf
  apply mixedTensorL2_eq_zero_of_inner μ f
  intro h
  exact (Submodule.span ℂ (Set.range (mixedTensorL2 (ι := Fin n) μ))).inner_left_of_mem_orthogonal
    (Submodule.subset_span ⟨h, rfl⟩) hf

/-- Continuous linear maps on the genuine tensor space agree when they agree
on every independently chosen elementary family. -/
theorem wickContinuousLinearMap_ext_mixed {n : ℕ} {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (T S : ProductL2 μ (Fin n) →L[ℂ] G)
    (h : ∀ v : Fin n → Lp ℂ 2 μ, T (mixedTensorL2 μ v) = S (mixedTensorL2 μ v)) : T = S := by
  apply ContinuousLinearMap.ext_on
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr (wickMixedTensor_dense_span μ n))
  rintro _ ⟨v, rfl⟩
  exact h v

/-- The checked tensor-family concatenation is Mathlib's literal finite tuple append. -/
theorem tensorFamilyAppend_eq_finAppend {p k : ℕ}
    (u : Fin p → Lp ℂ 2 μ) (v : Fin k → Lp ℂ 2 μ) :
    tensorFamilyAppend μ u v = Fin.append u v := by
  funext i
  obtain ⟨i, rfl⟩ := (finSumFinEquiv : Fin p ⊕ Fin k ≃ Fin (p + k)).surjective i
  cases i <;> simp only [tensorFamilyAppend, Equiv.symm_apply_apply, Sum.elim_inl,
    Sum.elim_inr, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
    Fin.append_left, Fin.append_right, finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd]

/-- Regrouping an arbitrary separated elementary family has no residual projection. -/
theorem wickUnregroup_mixed {p k : ℕ}
    (u : Fin p → Lp ℂ 2 μ) (v : Fin k → Lp ℂ 2 μ) :
    unregroupL2 μ p k (separatedL2 (sectorMeasure μ p) (sectorMeasure μ k)
      (mixedTensorL2 μ u) (mixedTensorL2 μ v)) =
        mixedTensorL2 μ (tensorFamilyAppend μ u v) := by
  apply (regroupL2 μ p k).injective
  rw [regroupL2_unregroupL2, regroupL2_mixedTensorL2]

/-- Unsymmetrized physical insertion u^r tensor h, with j free coordinates. -/
def wickFullLeftInsertion (r j : ℕ) (u : Lp ℂ 2 μ) :
    ProductL2 μ (Fin j) →L[ℂ] ProductL2 μ (Fin (r + j)) :=
  (unregroupL2 μ r j).toContinuousLinearMap ∘L
    wickSeparatedRight (sectorMeasure μ r) (sectorMeasure μ j)
      (pureTensorL2 (ι := Fin r) μ u)

/-- Unsymmetrized physical insertion h tensor v^s, with j free coordinates. -/
def wickFullRightInsertion (j s : ℕ) (v : Lp ℂ 2 μ) :
    ProductL2 μ (Fin j) →L[ℂ] ProductL2 μ (Fin (j + s)) :=
  (unregroupL2 μ j s).toContinuousLinearMap ∘L
    wickSeparatedLeft (sectorMeasure μ j) (sectorMeasure μ s)
      (pureTensorL2 (ι := Fin s) μ v)

theorem wickFullLeftInsertion_mixed (r j : ℕ) (u : Lp ℂ 2 μ)
    (h : Fin j → Lp ℂ 2 μ) :
    wickFullLeftInsertion μ r j u (mixedTensorL2 μ h) =
      mixedTensorL2 μ (tensorFamilyAppend μ (fun _ : Fin r => u) h) := by
  change unregroupL2 μ r j (separatedL2 (sectorMeasure μ r) (sectorMeasure μ j)
    (pureTensorL2 (ι := Fin r) μ u) (mixedTensorL2 μ h)) = _
  rw [← mixedTensorL2_diagonal μ u, wickUnregroup_mixed]

/-- Literal associativity in the complete physical tensor: inserting u^r in
front of a (j+s)-tensor is the tensor lift of insertion in front of its j slots. -/
theorem wickFullLeftInsertion_assoc (r j s : ℕ) (u : Lp ℂ 2 μ) :
    (productL2Cast μ (Nat.add_assoc r j s).symm).toLinearIsometry.toContinuousLinearMap ∘L
        wickFullLeftInsertion μ r (j + s) u =
      fullTensorLift μ (wickFullLeftInsertion μ r j u) s := by
  apply wickContinuousLinearMap_ext_mixed μ
  intro h
  let h₁ : Fin j → Lp ℂ 2 μ := fun i => h (Fin.castAdd s i)
  let h₂ : Fin s → Lp ℂ 2 μ := fun i => h (Fin.natAdd j i)
  have hh : h = tensorFamilyAppend μ h₁ h₂ := by
    rw [tensorFamilyAppend_eq_finAppend]
    exact Fin.append_castAdd_natAdd.symm
  have hm : mixedTensorL2 μ h = unregroupL2 μ j s
      (separatedL2 (sectorMeasure μ j) (sectorMeasure μ s)
        (mixedTensorL2 μ h₁) (mixedTensorL2 μ h₂)) := by
    rw [wickUnregroup_mixed, hh]
  change productL2Cast μ (Nat.add_assoc r j s).symm
    (wickFullLeftInsertion μ r (j + s) u (mixedTensorL2 μ h)) = _
  rw [wickFullLeftInsertion_mixed, productL2Cast_mixedTensorL2, hm,
    fullTensorLift_separated, wickFullLeftInsertion_mixed, wickUnregroup_mixed, hh]
  congr 1
  simpa only [tensorFamilyAppend_eq_finAppend, Function.comp_def] using
    (Fin.append_assoc (fun _ : Fin r => u) h₁ h₂).symm

/-- Exact three-block pairing in the complete physical Hilbert tensor. The
left and right insertions refer to the same j coordinates, in the source order. -/
theorem wickThreeBlock_pairing (r j s : ℕ) (u v : Lp ℂ 2 μ)
    (x : ProductL2 μ (Fin (r + j))) (y : ProductL2 μ (Fin (j + s))) :
    inner ℂ
      (unregroupL2 μ (r + j) s (separatedL2 (sectorMeasure μ (r + j)) (sectorMeasure μ s)
        x (pureTensorL2 (ι := Fin s) μ v)))
      (productL2Cast μ (Nat.add_assoc r j s).symm (wickFullLeftInsertion μ r (j + s) u y)) =
    inner ℂ ((wickFullLeftInsertion μ r j u).adjoint x)
      ((wickFullRightInsertion μ j s v).adjoint y) := by
  have ha := congrArg (fun T : ProductL2 μ (Fin (j + s)) →L[ℂ]
      ProductL2 μ (Fin ((r + j) + s)) => T y) (wickFullLeftInsertion_assoc μ r j s u)
  change productL2Cast μ (Nat.add_assoc r j s).symm
    (wickFullLeftInsertion μ r (j + s) u y) =
      fullTensorLift μ (wickFullLeftInsertion μ r j u) s y at ha
  rw [ha, ← ContinuousLinearMap.adjoint_inner_left, fullTensorLift_adjoint_separated]
  change inner ℂ
    (wickFullRightInsertion μ j s v ((wickFullLeftInsertion μ r j u).adjoint x)) y = _
  exact (ContinuousLinearMap.adjoint_inner_right (wickFullRightInsertion μ j s v)
    ((wickFullLeftInsertion μ r j u).adjoint x) y).symm

/-- Orthogonal output symmetrization can be moved across the adjoint exactly. -/
theorem wickProjection_comp_adjoint {j n : ℕ}
    (T : ProductL2 μ (Fin j) →L[ℂ] ProductL2 μ (Fin n)) (x : SymmetricSector μ n) :
    ((symmetricSectorProjection μ n).comp T).adjoint x =
      T.adjoint (x : ProductL2 μ (Fin n)) := by
  apply ext_inner_right ℂ
  intro w
  rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]
  change inner ℂ (x : ProductL2 μ (Fin n)) (symmetrizeL2 μ (T w)) = _
  exact inner_symmetricSector_symmetrize μ n x (T w)

/-- The checked physical input insertion and its full-tensor form have the
same adjoint on symmetric vectors. -/
theorem wickInputTensorInsertion_adjoint (r j : ℕ) (u : Lp ℂ 2 μ)
    (x : SymmetricSector μ (r + j)) :
    (wickInputTensorInsertion μ r j u).adjoint x =
      (wickFullLeftInsertion μ r j u).adjoint (x : ProductL2 μ (Fin (r + j))) :=
  wickProjection_comp_adjoint μ (wickFullLeftInsertion μ r j u) x

/-- The checked output Riesz vector is the literal full-tensor right slice. -/
theorem wickOutputTensorInsertion_adjoint (j s : ℕ) (v : Lp ℂ 2 μ)
    (y : SymmetricSector μ (j + s)) :
    (wickOutputTensorInsertion μ j s v).adjoint y =
      (wickFullRightInsertion μ j s v).adjoint (y : ProductL2 μ (Fin (j + s))) :=
  wickProjection_comp_adjoint μ (wickFullRightInsertion μ j s v) y

end LiebLiniger.FixedPeriod.Quantum
