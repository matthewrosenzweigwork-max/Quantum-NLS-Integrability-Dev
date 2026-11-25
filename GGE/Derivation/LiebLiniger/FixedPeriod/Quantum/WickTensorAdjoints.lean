import LiebLiniger.FixedPeriod.Quantum.WickTensorSlices

/-!
# Adjoint action needed for the physical derivative-contraction pairing

These identities concern the actual complete spatial Hilbert tensor operators.
The tensor-lift adjoint is checked against every arbitrary elementary tensor and
extended using the established density theorem; no adjoint/tensor compatibility
is assumed. This moves the first physical kernel across the output pairing in
the source three-block contraction. The final three-block rearrangement remains
an additional identity, not an assumption here.
-/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace LiebLiniger.FixedPeriod.Quantum

variable {X : Type} [MeasurableSpace X] (μ : Measure X)
  [SigmaFinite μ] [IsFiniteMeasure μ]

/-- Extension by orthogonal symmetrization has the expected genuine adjoint
on symmetric output vectors, including the zero-particle sector. -/
theorem fullSectorExtension_adjoint_on_symmetric {p q : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q) (v : SymmetricSector μ q) :
    (fullSectorExtension μ A).adjoint (v : ProductL2 μ (Fin q)) =
      (A.adjoint v : ProductL2 μ (Fin p)) := by
  apply ext_inner_right ℂ
  intro w
  rw [ContinuousLinearMap.adjoint_inner_left]
  change inner ℂ v (A (symmetricSectorProjection μ p w)) =
    inner ℂ (A.adjoint v : ProductL2 μ (Fin p)) w
  rw [← inner_symmetricSector_symmetrize μ p (A.adjoint v) w]
  change inner ℂ v (A (symmetricSectorProjection μ p w)) =
    inner ℂ (A.adjoint v) (symmetricSectorProjection μ p w)
  rw [ContinuousLinearMap.adjoint_inner_left]

/-- The adjoint of B tensor identity acts as B-adjoint on every separated
complete tensor. The proof tests all arbitrary elementary families, rather
than only diagonal powers. -/
theorem fullTensorLift_adjoint_separated {p q : ℕ}
    (B : ProductL2 μ (Fin p) →L[ℂ] ProductL2 μ (Fin q)) (k : ℕ)
    (f : ProductL2 μ (Fin q)) (g : ProductL2 μ (Fin k)) :
    (fullTensorLift μ B k).adjoint
      (unregroupL2 μ q k (separatedL2 (sectorMeasure μ q) (sectorMeasure μ k) f g)) =
    unregroupL2 μ p k
      (separatedL2 (sectorMeasure μ p) (sectorMeasure μ k) (B.adjoint f) g) := by
  apply sub_eq_zero.mp
  apply mixedTensorL2_eq_zero_of_inner μ
  intro h
  let h₁ : Fin p → Lp ℂ 2 μ := fun i => h (Fin.castAdd k i)
  let h₂ : Fin k → Lp ℂ 2 μ := fun i => h (Fin.natAdd p i)
  have hh : h = tensorFamilyAppend μ h₁ h₂ := by
    funext i
    obtain ⟨i, rfl⟩ := (finSumFinEquiv : Fin p ⊕ Fin k ≃ Fin (p + k)).surjective i
    cases i <;> simp only [tensorFamilyAppend, h₁, h₂, Equiv.symm_apply_apply,
      Sum.elim_inl, Sum.elim_inr, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
      finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd]
  have hm : mixedTensorL2 μ h = unregroupL2 μ p k
      (separatedL2 (sectorMeasure μ p) (sectorMeasure μ k)
        (mixedTensorL2 μ h₁) (mixedTensorL2 μ h₂)) := by
    apply (regroupL2 μ p k).injective
    rw [hh, regroupL2_mixedTensorL2, regroupL2_unregroupL2]
  rw [inner_sub_left]
  apply sub_eq_zero.mpr
  rw [hm, ContinuousLinearMap.adjoint_inner_left, fullTensorLift_separated,
    LinearIsometry.inner_map_map, LinearIsometry.inner_map_map,
    separatedL2_inner, separatedL2_inner, ContinuousLinearMap.adjoint_inner_left]

/-- The previous identity for actual symmetric kernels, retaining the literal
spectator tensor and the original full-sector inclusion. -/
theorem fullSectorExtension_tensor_adjoint_symmetric {p q : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q) (k : ℕ)
    (v : SymmetricSector μ q) (g : ProductL2 μ (Fin k)) :
    (fullTensorLift μ (fullSectorExtension μ A) k).adjoint
      (unregroupL2 μ q k (separatedL2 (sectorMeasure μ q) (sectorMeasure μ k)
        (v : ProductL2 μ (Fin q)) g)) =
    unregroupL2 μ p k (separatedL2 (sectorMeasure μ p) (sectorMeasure μ k)
      (A.adjoint v : ProductL2 μ (Fin p)) g) := by
  rw [fullTensorLift_adjoint_separated, fullSectorExtension_adjoint_on_symmetric]

end LiebLiniger.FixedPeriod.Quantum
