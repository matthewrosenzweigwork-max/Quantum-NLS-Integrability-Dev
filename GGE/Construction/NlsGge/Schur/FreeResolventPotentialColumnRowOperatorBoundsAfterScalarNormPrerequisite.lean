import NlsGge.Schur.FreeResolventRankTwoProjectionPrerequisites
import NlsGge.Schur.FreeResolventPotentialResonantNormConsumersAfterScalarNormPrerequisite

set_option autoImplicit false
noncomputable section
open scoped InnerProduct InnerProductSpace

namespace NlsGge.Schur
open NlsGge.Pilot

/-- Actual `D V P` estimate from the two resonant columns, retaining the
independent source fields and the exact complex-disk denominator. -/
theorem freeResolventPotentialColumn_opNorm_bound_from_prerequisites
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (n : ℤ) (hn : n ≠ 0) (z : ℂ) (hz : z ∈ spectralDisk n) :
    ‖freeResolventPotentialColumn u₁ u₂ hu₁ hu₂ n z hz‖ ≤
      Real.sqrt ((2 / (n : ℝ) ^ 2) * ‖physicalSobolevL2 1 u₁ hu₁‖ ^ 2) +
        Real.sqrt ((2 / (n : ℝ) ^ 2) * ‖physicalSobolevL2 1 u₂ hu₂‖ ^ 2) := by
  let S := (freeResolventParityPair n z hz).comp
    (coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n)
  have hfactor : freeResolventPotentialColumn u₁ u₂ hu₁ hu₂ n z hz =
      S.comp (resonantParityPair n) := by
    ext x
    rfl
  have htrue : S (parityPairVector n (true, resonantIndex n)) =
      freeResolventPotentialColumn u₁ u₂ hu₁ hu₂ n z hz
        (parityPairVector n (true, resonantIndex n)) := by
    simp [S, freeResolventPotentialColumn, resonantParityPair_apply_basis]
  have hfalse : S (parityPairVector n (false, resonantIndex n)) =
      freeResolventPotentialColumn u₁ u₂ hu₁ hu₂ n z hz
        (parityPairVector n (false, resonantIndex n)) := by
    simp [S, freeResolventPotentialColumn, resonantParityPair_apply_basis]
  have htrue' :
      ‖S (parityPairVector n (true, resonantIndex n))‖ ≤
        Real.sqrt ((2 / (n : ℝ) ^ 2) * ‖physicalSobolevL2 1 u₂ hu₂‖ ^ 2) := by
    have hsq := freeResolventPotentialColumn_true_resonant_norm_sq_le_from_prerequisites
      u₁ u₂ hu₁ hu₂ n hn z hz
    rw [← htrue] at hsq
    calc
      _ = Real.sqrt (‖S (parityPairVector n (true, resonantIndex n))‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ _ := Real.sqrt_le_sqrt hsq
  have hfalse' :
      ‖S (parityPairVector n (false, resonantIndex n))‖ ≤
        Real.sqrt ((2 / (n : ℝ) ^ 2) * ‖physicalSobolevL2 1 u₁ hu₁‖ ^ 2) := by
    have hsq := freeResolventPotentialColumn_false_resonant_norm_sq_le_from_prerequisites
      u₁ u₂ hu₁ hu₂ n hn z hz
    rw [← hfalse] at hsq
    calc
      _ = Real.sqrt (‖S (parityPairVector n (false, resonantIndex n))‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ _ := Real.sqrt_le_sqrt hsq
  calc
    ‖freeResolventPotentialColumn u₁ u₂ hu₁ hu₂ n z hz‖ =
        ‖S.comp (resonantParityPair n)‖ := by rw [hfactor]
    _ ≤ ‖S (parityPairVector n (true, resonantIndex n))‖ +
        ‖S (parityPairVector n (false, resonantIndex n))‖ :=
      comp_resonantParityPair_opNorm_le_columns_prerequisite n S
    _ ≤ _ := add_le_add htrue' hfalse'
    _ = _ := add_comm _ _

/-- Actual `P V D` estimate from the two resonant rows. The row vectors are
the adjoints of this actual PVD map; no self-adjointness or conjugacy between
the two potential fields is used. -/
theorem resonantPotentialFreeResolventRow_opNorm_bound_from_prerequisites
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (n : ℤ) (hn : n ≠ 0) (z : ℂ) (hz : z ∈ spectralDisk n) :
    ‖resonantPotentialFreeResolventRow u₁ u₂ hu₁ hu₂ n z hz‖ ≤
      Real.sqrt ((2 / (n : ℝ) ^ 2) * ‖physicalSobolevL2 1 u₁ hu₁‖ ^ 2) +
        Real.sqrt ((2 / (n : ℝ) ^ 2) * ‖physicalSobolevL2 1 u₂ hu₂‖ ^ 2) := by
  let T := resonantPotentialFreeResolventRow u₁ u₂ hu₁ hu₂ n z hz
  let e₁ := parityPairVector n (true, resonantIndex n)
  let e₂ := parityPairVector n (false, resonantIndex n)
  let r₁ := T.adjoint e₁
  let r₂ := T.adjoint e₂
  have hrange (x : ParityPair n) : resonantParityPair n (T x) = T x := by
    apply (parityPairRepr n).injective
    change parityPairRepr n (resonantParityPair n (T x)) = parityPairRepr n (T x)
    ext i
    by_cases hi : i.2 = resonantIndex n
    · simp [T, resonantPotentialFreeResolventRow_repr_apply,
        resonantParityPair_repr_apply, hi]
    · simp [T, resonantPotentialFreeResolventRow_repr_apply,
        resonantParityPair_repr_apply, hi]
  have hcomp : (resonantParityPair n).comp T = T := by
    exact ContinuousLinearMap.ext (fun x => hrange x)
  have hrow₁ (x : ParityPair n) : inner ℂ e₁ (T x) = inner ℂ r₁ x := by
    exact (ContinuousLinearMap.adjoint_inner_left T x e₁).symm
  have hrow₂ (x : ParityPair n) : inner ℂ e₂ (T x) = inner ℂ r₂ x := by
    exact (ContinuousLinearMap.adjoint_inner_left T x e₂).symm
  have hr₁ : ‖r₁‖ ≤
      Real.sqrt ((2 / (n : ℝ) ^ 2) * ‖physicalSobolevL2 1 u₁ hu₁‖ ^ 2) := by
    have hsq := resonantPotentialFreeResolventRow_true_resonant_adjoint_norm_sq_le_from_prerequisites
      u₁ u₂ hu₁ hu₂ n hn z hz
    calc
      _ = Real.sqrt (‖(resonantPotentialFreeResolventRow u₁ u₂ hu₁ hu₂ n z hz).adjoint
          (parityPairVector n (true, resonantIndex n))‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ _ := Real.sqrt_le_sqrt hsq
  have hr₂ : ‖r₂‖ ≤
      Real.sqrt ((2 / (n : ℝ) ^ 2) * ‖physicalSobolevL2 1 u₂ hu₂‖ ^ 2) := by
    have hsq := resonantPotentialFreeResolventRow_false_resonant_adjoint_norm_sq_le_from_prerequisites
      u₁ u₂ hu₁ hu₂ n hn z hz
    calc
      _ = Real.sqrt (‖(resonantPotentialFreeResolventRow u₁ u₂ hu₁ hu₂ n z hz).adjoint
          (parityPairVector n (false, resonantIndex n))‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ _ := Real.sqrt_le_sqrt hsq
  calc
    ‖T‖ = ‖(resonantParityPair n).comp T‖ := by rw [hcomp]
    _ ≤ ‖r₁‖ + ‖r₂‖ :=
      resonantParityPair_comp_opNorm_le_rows_prerequisite n T r₁ r₂ hrow₁ hrow₂
    _ ≤ _ := add_le_add hr₁ hr₂

end NlsGge.Schur
