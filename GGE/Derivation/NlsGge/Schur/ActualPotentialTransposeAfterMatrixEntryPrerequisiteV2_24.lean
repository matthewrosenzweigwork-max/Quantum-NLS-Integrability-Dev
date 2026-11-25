import NlsGge.Schur.ActualCoordinateTransposeMatrixEntryV2_24

set_option autoImplicit false
noncomputable section
open scoped InnerProduct InnerProductSpace

namespace NlsGge.Schur
open NlsGge.Pilot

/-- The actual covered two-field potential is invariant under the physical
transpose. The proof uses the passed paired transpose matrix-entry theorem and
the unified actual entry formula, including the same-channel zero and the
distinct upper/lower Fourier fields. -/
theorem actualPairTransposeAfterMatrixEntryPrerequisiteV2_24_coveredPotential
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂)) (n : ℤ) :
    actualPairTransposeAfterCoordinate23 n
        (coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n) =
      coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n := by
  have hdense : Dense
      (↑(Submodule.span ℂ (Set.range (parityPairFourierBasis n))) : Set (ParityPair n)) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr
      (parityPairFourierBasis n).dense_span
  apply ContinuousLinearMap.ext_on hdense
  intro x hx
  rcases hx with ⟨j, rfl⟩
  have hj : parityPairFourierBasis n j = parityPairVector n j := by
    simp only [parityPairFourierBasis, HilbertBasis.coe_mkOfOrthogonalEqBot]
  rw [hj]
  apply (parityPairRepr n).injective
  apply lp.ext
  funext i
  change parityPairRepr n
      (actualPairTransposeAfterCoordinate23 n
        (coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n)
        (parityPairVector n j)) i =
    parityPairRepr n
      (coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n (parityPairVector n j)) i
  rw [parityPairRepr_inner n
      (actualPairTransposeAfterCoordinate23 n
        (coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n)
        (parityPairVector n j)) i,
    parityPairRepr_inner n
      (coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n (parityPairVector n j)) i]
  rw [actualPairTranspose24_single_matrix_entry_v2]
  rw [actualPotentialTranspose_pair_entry_formula24,
    actualPotentialTranspose_pair_entry_formula24]
  rcases i with ⟨bi, m⟩
  rcases j with ⟨bj, l⟩
  cases bi <;> cases bj
  · simp [actualPotentialTranspose_swapped_pair_index24]
  · simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, if_false, if_true]
    congr 1
    rw [Int.add_comm]
  · simp only [Bool.not_false, Bool.not_true, Bool.true_eq_false, Bool.false_eq_true,
      if_false, if_true]
    congr 1
    rw [Int.add_comm]
  · simp [actualPotentialTranspose_swapped_pair_index24]

end NlsGge.Schur
