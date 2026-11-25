import NlsGge.Schur.ActualSchurCLMUnitMonoidParentTransportMinimumV3_34
import Mathlib.Algebra.Group.Units.Hom
import NlsGge.Schur.ActualComplementaryQVDJointInverseAndEqualDiagonalV5_30

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur

private abbrev ActualSchurCLMEndV2_35 (n : ℤ) :=
  ActualSchurCLMEndV3_34 n

private abbrev actualSchurSourceUnitV2_35 (n : ℤ) :=
  @Units (ActualSchurCLMEndV2_35 n)
    (actualSchurCLMSourceMonoidWithZeroV3_34 n).toMonoid

private abbrev actualSchurRingParentUnitV2_35 (n : ℤ) :=
  @Units (ActualSchurCLMEndV2_35 n)
    (actualSchurCLMRingMonoidWithZeroV3_34 n).toMonoid

/-- Map an actual source-parent CLM unit into the actual normed-ring parent. -/
noncomputable def actualSchurSourceUnitToRingParentV2_35 (n : ℤ)
    (u : actualSchurSourceUnitV2_35 n) : actualSchurRingParentUnitV2_35 n :=
  Units.map
    (actualSchurCLMSourceToRingParentMonoidWithZeroHomV3_34 n).toMonoidHom u

/-- Map an actual normed-ring-parent CLM unit back to the source parent. -/
noncomputable def actualSchurRingParentUnitToSourceV2_35 (n : ℤ)
    (u : actualSchurRingParentUnitV2_35 n) : actualSchurSourceUnitV2_35 n :=
  Units.map
    (actualSchurCLMRingParentToSourceMonoidWithZeroHomV3_34 n).toMonoidHom u

@[simp]
theorem actualSchurSourceUnitToRingParentV2_35_coe (n : ℤ)
    (u : actualSchurSourceUnitV2_35 n) :
    (actualSchurSourceUnitToRingParentV2_35 n u : ActualSchurCLMEndV2_35 n) =
      (u : ActualSchurCLMEndV2_35 n) := by
  simp [actualSchurSourceUnitToRingParentV2_35]

@[simp]
theorem actualSchurSourceUnitToRingParentV2_35_inv_coe (n : ℤ)
    (u : actualSchurSourceUnitV2_35 n) :
    (((actualSchurSourceUnitToRingParentV2_35 n u)⁻¹ : actualSchurRingParentUnitV2_35 n) :
      ActualSchurCLMEndV2_35 n) =
    ((u⁻¹ : actualSchurSourceUnitV2_35 n) : ActualSchurCLMEndV2_35 n) := by
  simpa [actualSchurSourceUnitToRingParentV2_35] using
    (Units.coe_map_inv
      (actualSchurCLMSourceToRingParentMonoidWithZeroHomV3_34 n).toMonoidHom u)

@[simp]
theorem actualSchurRingParentUnitToSourceV2_35_coe (n : ℤ)
    (u : actualSchurRingParentUnitV2_35 n) :
    (actualSchurRingParentUnitToSourceV2_35 n u : ActualSchurCLMEndV2_35 n) =
      (u : ActualSchurCLMEndV2_35 n) := by
  change
    (actualSchurCLMRingParentToSourceMonoidWithZeroHomV3_34 n).toMonoidHom
      (u : ActualSchurCLMEndV2_35 n) =
    (u : ActualSchurCLMEndV2_35 n)
  rfl

@[simp]
theorem actualSchurRingParentUnitToSourceV2_35_inv_coe (n : ℤ)
    (u : actualSchurRingParentUnitV2_35 n) :
    (((actualSchurRingParentUnitToSourceV2_35 n u)⁻¹ : actualSchurSourceUnitV2_35 n) :
      ActualSchurCLMEndV2_35 n) =
    ((u⁻¹ : actualSchurRingParentUnitV2_35 n) : ActualSchurCLMEndV2_35 n) := by
  change
    (actualSchurCLMRingParentToSourceMonoidWithZeroHomV3_34 n).toMonoidHom
      (↑(u⁻¹ : actualSchurRingParentUnitV2_35 n)) =
    ↑(u⁻¹ : actualSchurRingParentUnitV2_35 n)
  rfl

/-- The two actual total inverse functions agree on every CLM endomorphism.
The hypotheses name the two distinct MonoidWithZero parents from the passed
V3 coherence minimum. -/
theorem actualSchurParentedTotalInverseValueAgreementV2_35
    (n : ℤ) (T : ActualSchurCLMEndV2_35 n) :
    @Ring.inverse (ActualSchurCLMEndV2_35 n)
        (actualSchurCLMSourceMonoidWithZeroV3_34 n) T =
      @Ring.inverse (ActualSchurCLMEndV2_35 n)
        (actualSchurCLMRingMonoidWithZeroV3_34 n) T := by
  classical
  by_cases hT : @IsUnit (ActualSchurCLMEndV2_35 n)
      (actualSchurCLMSourceMonoidWithZeroV3_34 n).toMonoid T
  · obtain ⟨u, hu⟩ := hT
    have huMap :
        (actualSchurSourceUnitToRingParentV2_35 n u : ActualSchurCLMEndV2_35 n) = T := by
      simpa using hu
    calc
      @Ring.inverse (ActualSchurCLMEndV2_35 n)
          (actualSchurCLMSourceMonoidWithZeroV3_34 n) T =
          @Ring.inverse (ActualSchurCLMEndV2_35 n)
            (actualSchurCLMSourceMonoidWithZeroV3_34 n)
            (u : ActualSchurCLMEndV2_35 n) :=
        congrArg
          (fun X : ActualSchurCLMEndV2_35 n =>
            @Ring.inverse (ActualSchurCLMEndV2_35 n)
              (actualSchurCLMSourceMonoidWithZeroV3_34 n) X)
          hu.symm
      _ = ((u⁻¹ : actualSchurSourceUnitV2_35 n) : ActualSchurCLMEndV2_35 n) :=
        @Ring.inverse_unit (ActualSchurCLMEndV2_35 n)
          (actualSchurCLMSourceMonoidWithZeroV3_34 n) u
      _ = (((actualSchurSourceUnitToRingParentV2_35 n u)⁻¹ :
          actualSchurRingParentUnitV2_35 n) : ActualSchurCLMEndV2_35 n) :=
        (actualSchurSourceUnitToRingParentV2_35_inv_coe n u).symm
      _ = @Ring.inverse (ActualSchurCLMEndV2_35 n)
          (actualSchurCLMRingMonoidWithZeroV3_34 n)
          (actualSchurSourceUnitToRingParentV2_35 n u : ActualSchurCLMEndV2_35 n) :=
        (@Ring.inverse_unit (ActualSchurCLMEndV2_35 n)
          (actualSchurCLMRingMonoidWithZeroV3_34 n)
          (actualSchurSourceUnitToRingParentV2_35 n u)).symm
      _ = @Ring.inverse (ActualSchurCLMEndV2_35 n)
          (actualSchurCLMRingMonoidWithZeroV3_34 n) T :=
        congrArg
          (fun X : ActualSchurCLMEndV2_35 n =>
            @Ring.inverse (ActualSchurCLMEndV2_35 n)
              (actualSchurCLMRingMonoidWithZeroV3_34 n) X)
          huMap
  · have hNotRingParentUnit :
        ¬ @IsUnit (ActualSchurCLMEndV2_35 n)
          (actualSchurCLMRingMonoidWithZeroV3_34 n).toMonoid T := by
      intro h
      obtain ⟨u, hu⟩ := h
      have huBack :
          (actualSchurRingParentUnitToSourceV2_35 n u : ActualSchurCLMEndV2_35 n) = T := by
        simpa using hu
      exact hT ⟨actualSchurRingParentUnitToSourceV2_35 n u, huBack⟩
    calc
      @Ring.inverse (ActualSchurCLMEndV2_35 n)
          (actualSchurCLMSourceMonoidWithZeroV3_34 n) T = 0 :=
        @Ring.inverse_non_unit (ActualSchurCLMEndV2_35 n)
          (actualSchurCLMSourceMonoidWithZeroV3_34 n) T hT
      _ = @Ring.inverse (ActualSchurCLMEndV2_35 n)
          (actualSchurCLMRingMonoidWithZeroV3_34 n) T :=
        (@Ring.inverse_non_unit (ActualSchurCLMEndV2_35 n)
          (actualSchurCLMRingMonoidWithZeroV3_34 n) T hNotRingParentUnit).symm

/-- The original V5_30 Schur inverse is the same total inverse as the one
parented by the actual CLM normed ring. This is only a function-value bridge. -/
theorem actualSchurInverseV5_30EqualsRingParentInverseV2_35
    (n : ℤ) (x : ℂ × ActualH1PairJointSchurV5_30) :
    actualComplementaryQVDJointInverseV5_30 n x =
      @Ring.inverse (ActualSchurCLMEndV2_35 n)
        (actualSchurCLMRingMonoidWithZeroV3_34 n)
        (1 - actualComplementaryQVDJointParameterV5_30 n x) := by
  change @Ring.inverse (ActualSchurCLMEndV2_35 n)
      (actualSchurCLMSourceMonoidWithZeroV3_34 n)
      (1 - actualComplementaryQVDJointParameterV5_30 n x) = _
  exact actualSchurParentedTotalInverseValueAgreementV2_35 n
    (1 - actualComplementaryQVDJointParameterV5_30 n x)

end NlsGge.Schur
