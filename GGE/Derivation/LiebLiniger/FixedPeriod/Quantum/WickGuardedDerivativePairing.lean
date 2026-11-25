import LiebLiniger.FixedPeriod.Quantum.WickDerivativeOrderedPairing
import LiebLiniger.FixedPeriod.Quantum.WickTransferContractionBound

/-! Bounded source-exact guarded derivative pairing after actual e459 line 2570
cast failure. SOURCE ONLY: prospective 30fa derivative parent and this unit
both require native/TYPEAX qualification before any downstream consumption. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace LiebLiniger.FixedPeriod.Quantum
variable {X : Type} [MeasurableSpace X] (μ : Measure X)
  [SigmaFinite μ] [IsFiniteMeasure μ]

/-- Reflexive sector transport is the identity, regardless of equality proof. -/
private theorem q2024_sectorCast_self_clm (n : ℕ) (h : n = n) :
    (symmetricSectorCast μ h).toLinearIsometry.toContinuousLinearMap =
      ContinuousLinearMap.id ℂ (SymmetricSector μ n) := by
  cases Subsingleton.elim h rfl
  rfl

/-- A polarized matrix element is unchanged by equality-only sector casts. -/
private theorem q2024_cast_polarized {a b c d : ℕ}
    (hin : a = b) (hout : c = d)
    (T : SymmetricSector μ b →L[ℂ] SymmetricSector μ c) (v u : Lp ℂ 2 μ) :
    wickKernelPolarized μ
      ((symmetricSectorCast μ hout).toLinearIsometry.toContinuousLinearMap ∘L T ∘L
        (symmetricSectorCast μ hin).toLinearIsometry.toContinuousLinearMap) v u =
      wickKernelPolarized μ T v u := by
  subst b
  subst d
  rfl

/-- Equality-only transport of the complete source tensor contraction, including
both kernel slots. It preserves the same A and B and the same contraction order. -/
private theorem q2024_tensorContraction_cast {r r' j s s' : ℕ}
    (hr : r' = r) (hs : s' = s)
    (A : SymmetricSector μ (r + j) →L[ℂ] SymmetricSector μ 0)
    (B : SymmetricSector μ 0 →L[ℂ] SymmetricSector μ (j + s)) :
    tensorDerivativeContraction (j := j) μ
        (A ∘L (symmetricSectorCast μ (congrArg (fun n => n + j) hr)).toLinearIsometry.toContinuousLinearMap)
        ((symmetricSectorCast μ (congrArg (fun n => j + n) hs.symm)).toLinearIsometry.toContinuousLinearMap ∘L B) =
      (symmetricSectorCast μ (congrArg (fun n => 0 + n) hs.symm)).toLinearIsometry.toContinuousLinearMap ∘L
        tensorDerivativeContraction (j := j) μ A B ∘L
        (symmetricSectorCast μ (congrArg (fun n => n + 0) hr)).toLinearIsometry.toContinuousLinearMap := by
  cases hr
  cases hs
  simp only [q2024_sectorCast_self_clm, ContinuousLinearMap.id_comp,
    ContinuousLinearMap.comp_id]

/-- Original-degree guarded source contraction has exactly the earned ordered
embedding-pair scalar pairing, including p=0,q=0 and j=0. The only premise is
source admissibility of this order, not any derivative or product identity. -/
theorem sourceDerivativeContractionKernel_mixed_annihilation_creation_pairing
    (p q j : ℕ) (gs : Fin p → Lp ℂ 2 μ) (hs : Fin q → Lp ℂ 2 μ)
    (hj : j ≤ min p q) (v u : Lp ℂ 2 μ) :
    wickKernelPolarized μ (sourceDerivativeContractionKernel μ
        (InnerProductSpace.rankOne ℂ (pureSymmetricTensor μ 0 (0 : Lp ℂ 2 μ))
          (symmetricTensorContinuousMultilinear μ p gs))
        (InnerProductSpace.rankOne ℂ (symmetricTensorContinuousMultilinear μ q hs)
          (pureSymmetricTensor μ 0 (0 : Lp ℂ 2 μ))) j) v u =
      ∑ a : Fin j ↪ Fin p, ∑ b : Fin j ↪ Fin q,
        physicalUnusedProduct μ gs a u * conj (physicalUnusedProduct μ hs b v) *
          ∏ i : Fin j, inner ℂ (gs (a i)) (hs (b i)) := by
  have hdegrees : ∃ r s : ℕ, p = r + j ∧ q = j + s :=
    (contractionDegrees_coverage p q j).mp hj
  obtain ⟨r, s, hp, hq⟩ := hdegrees
  subst p
  subst q
  let R : ℕ := (r + j) - j
  let S : ℕ := (j + s) - j
  have hr : R = r := by dsimp [R]; omega
  have hs' : S = s := by dsimp [S]; omega
  let A : SymmetricSector μ (r + j) →L[ℂ] SymmetricSector μ 0 :=
    InnerProductSpace.rankOne ℂ (pureSymmetricTensor μ 0 (0 : Lp ℂ 2 μ))
      (symmetricTensorContinuousMultilinear μ (r + j) gs)
  let B : SymmetricSector μ 0 →L[ℂ] SymmetricSector μ (j + s) :=
    InnerProductSpace.rankOne ℂ (symmetricTensorContinuousMultilinear μ (j + s) hs)
      (pureSymmetricTensor μ 0 (0 : Lp ℂ 2 μ))
  rw [sourceDerivativeContractionKernel_available μ _ _ j hj]
  rw [q2024_cast_polarized]
  change wickKernelPolarized μ (tensorDerivativeContraction (j := j) μ
    (A ∘L (symmetricSectorCast μ (congrArg (fun n => n + j) hr)).toLinearIsometry.toContinuousLinearMap)
    ((symmetricSectorCast μ (congrArg (fun n => j + n) hs'.symm)).toLinearIsometry.toContinuousLinearMap ∘L B)) v u = _
  calc
    _ = wickKernelPolarized μ
        ((symmetricSectorCast μ (congrArg (fun n => 0 + n) hs'.symm)).toLinearIsometry.toContinuousLinearMap ∘L
          tensorDerivativeContraction (j := j) μ A B ∘L
          (symmetricSectorCast μ (congrArg (fun n => n + 0) hr)).toLinearIsometry.toContinuousLinearMap) v u :=
      congrArg (fun T : SymmetricSector μ (R + 0) →L[ℂ] SymmetricSector μ (0 + S) =>
        wickKernelPolarized μ T v u) (q2024_tensorContraction_cast μ hr hs' A B)
    _ = wickKernelPolarized μ (tensorDerivativeContraction (j := j) μ A B) v u :=
      q2024_cast_polarized μ (congrArg (fun n => n + 0) hr)
        (congrArg (fun n => 0 + n) hs'.symm) _ v u
    _ = _ := tensorDerivativeContraction_mixed_ordered_pairing μ r j s gs hs v u

end LiebLiniger.FixedPeriod.Quantum
end
