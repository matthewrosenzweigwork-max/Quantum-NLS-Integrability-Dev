import NlsGge.Schur.FreeResolventComplementarySquareBoundAfterQDTransport
import NlsGge.Schur.FreeResolventComplementaryDQTransportAfterCoordinateRange
import NlsGge.Schur.ContinuousLinearMapSquareNeumannRangePrerequisite
import NlsGge.Schur.FreeResolventDVDOperatorNormActualPrerequisite
import NlsGge.Schur.FreeResolventPotentialOppositeFactorSquareFactorizationPrerequisite

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur
open NlsGge.Analysis NlsGge.Pilot

/-- Absolute `O(R)` constant for the actual complementary inverse factors. -/
def freeResolventComplementaryInverseUniformConstant22 : ℝ :=
  2 + 4 * physicalH1MultiplierConstant

/-- The actual opposite complementary factor `Q V D` on the paired physical
carrier. -/
def freeResolventComplementaryPotentialOppositeFactor22
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n) :
    ParityPair n →L[ℂ] ParityPair n :=
  (freeResolventComplementaryProjectionTransported n).comp
    ((coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n).comp
      (freeResolventParityPair n z hz))

/-- Idempotence of the actual transported complementary projection. -/
theorem freeResolventComplementaryProjectionTransported_idempotent_actual22
    (n : ℤ) :
    (freeResolventComplementaryProjectionTransported n).comp
      (freeResolventComplementaryProjectionTransported n) =
    freeResolventComplementaryProjectionTransported n := by
  let E := parityPairRepr n
  apply ContinuousLinearMap.ext
  intro x
  apply E.injective
  change E (E.symm (complementarySquare n
      (E (E.symm (complementarySquare n (E x)))))) =
    E (E.symm (complementarySquare n (E x)))
  simp only [E.apply_symm_apply]
  apply lp.ext
  funext i
  rw [complementarySquare_apply]
  by_cases hi : i.2 = resonantIndex n <;> simp [hi, complementarySquare_apply]

/-- The actual `Q V D` factor has square norm at most one half. This is the
opposite-order estimate `Q V D Q V D = Q V (D V D)`, using the actual right
support `D Q = D` and the actual Hilbert--Schmidt bound for `D V D`. -/
theorem freeResolventComplementaryPotentialOpposite_square_norm_le_half_actual22
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (R : ℝ) (hR : 1 ≤ R)
    (hball₁ : ‖physicalSobolevL2 1 u₁ hu₁‖ ≤ R)
    (hball₂ : ‖physicalSobolevL2 1 u₂ hu₂‖ ≤ R)
    (n : ℤ) (hn : 1 ≤ |(n : ℝ)|)
    (z : ℂ) (hz : z ∈ spectralDisk n)
    (hlarge : 4 * freeResolventSchurUniformConstant *
      physicalH1MultiplierConstant * R ^ 2 ≤ |(n : ℝ)|) :
    ‖(freeResolventComplementaryPotentialOppositeFactor22
        u₁ u₂ hu₁ hu₂ n z hz) *
      (freeResolventComplementaryPotentialOppositeFactor22
        u₁ u₂ hu₁ hu₂ n z hz)‖ ≤ (1 / 2 : ℝ) := by
  let D : ParityPair n →L[ℂ] ParityPair n := freeResolventParityPair n z hz
  let V : ParityPair n →L[ℂ] ParityPair n :=
    coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n
  let Q : ParityPair n →L[ℂ] ParityPair n :=
    freeResolventComplementaryProjectionTransported n
  let DVD : ParityPair n →L[ℂ] ParityPair n :=
    freeResolventPotentialFreeResolvent u₁ u₂ hu₁ hu₂ n z hz
  let A : ParityPair n →L[ℂ] ParityPair n := Q.comp (V.comp D)
  have hV : ‖V‖ ≤ 2 * physicalH1MultiplierConstant * R := by
    have hR0 : 0 ≤ R := le_trans (by norm_num) hR
    exact coveredH1ParityPairPotential_norm_bound u₁ u₂ hu₁ hu₂ n R hR0 hball₁ hball₂
  have hQ : ‖Q‖ ≤ 1 := freeResolventComplementaryProjectionTransported_norm_le_one n
  have hDVDop : ‖DVD‖ ≤
      freeResolventSchurUniformConstant * R / |(n : ℝ)| := by
    change ‖freeResolventPotentialFreeResolvent u₁ u₂ hu₁ hu₂ n z hz‖ ≤
      freeResolventSchurUniformConstant * R / |(n : ℝ)|
    exact freeResolventPotentialFreeResolvent_opNorm_le_actual22
      u₁ u₂ hu₁ hu₂ R hR hball₁ hball₂ n hn z hz
  have hden : 0 < |(n : ℝ)| := by
    have hn0 : n ≠ 0 := by
      intro h
      subst n
      norm_num at hn
    exact abs_pos.mpr (Int.cast_ne_zero.mpr hn0)
  have hscalar : 2 * freeResolventSchurUniformConstant *
      physicalH1MultiplierConstant * R ^ 2 / |(n : ℝ)| ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ hden).2
    nlinarith [hlarge]
  have hDQ : D.comp Q = D :=
    freeResolventParityPair_comp_complementaryProjection_right_afterCoordinateRange n z hz
  have hDVD : D.comp (V.comp D) = DVD := rfl
  have hfactor : A.comp A = Q.comp (V.comp DVD) := by
    exact continuousLinearMap_QVD_square_factorization Q V D DVD hDQ hDVD
  calc
    ‖(freeResolventComplementaryPotentialOppositeFactor22
        u₁ u₂ hu₁ hu₂ n z hz) *
      (freeResolventComplementaryPotentialOppositeFactor22
        u₁ u₂ hu₁ hu₂ n z hz)‖ = ‖A.comp A‖ := by
          change ‖A * A‖ = ‖A.comp A‖
          rw [ContinuousLinearMap.mul_def]
    _ = ‖Q.comp (V.comp DVD)‖ := by rw [hfactor]
    _ ≤ ‖Q‖ * ‖V.comp DVD‖ := Q.opNorm_comp_le _
    _ ≤ ‖Q‖ * (‖V‖ * ‖DVD‖) :=
      mul_le_mul_of_nonneg_left (V.opNorm_comp_le DVD) (norm_nonneg Q)
    _ ≤ 1 * (‖V‖ * ‖DVD‖) := by
      exact mul_le_mul_of_nonneg_right hQ
        (mul_nonneg (norm_nonneg V) (norm_nonneg DVD))
    _ ≤ 1 * ((2 * physicalH1MultiplierConstant * R) *
        (freeResolventSchurUniformConstant * R / |(n : ℝ)|)) := by
      have hCVR : 0 ≤ 2 * physicalH1MultiplierConstant * R :=
        physicalH1MultiplierConstant_radius_nonneg R hR
      have hmul := mul_le_mul hV hDVDop (norm_nonneg DVD) hCVR
      simpa only [one_mul] using hmul
    _ ≤ (1 / 2 : ℝ) := by
      rw [one_mul]
      have hrewrite :
          (2 * physicalH1MultiplierConstant * R) *
            (freeResolventSchurUniformConstant * R / |(n : ℝ)|) =
          2 * freeResolventSchurUniformConstant *
            physicalH1MultiplierConstant * R ^ 2 / |(n : ℝ)| := by ring
      rw [hrewrite]
      exact hscalar

/-- The `D V Q` inverse restricts to the actual complementary range with the
absolute `O(R)` bound. -/
theorem freeResolventComplementaryPotentialA_neumann_inverse_range_actual22
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (R : ℝ) (hR : 1 ≤ R)
    (hball₁ : ‖physicalSobolevL2 1 u₁ hu₁‖ ≤ R)
    (hball₂ : ‖physicalSobolevL2 1 u₂ hu₂‖ ≤ R)
    (n : ℤ) (hn : 1 ≤ |(n : ℝ)|)
    (z : ℂ) (hz : z ∈ spectralDisk n)
    (hlarge : 4 * freeResolventSchurUniformConstant *
      physicalH1MultiplierConstant * R ^ 2 ≤ |(n : ℝ)|) :
    ∃ S : ParityPair n →L[ℂ] ParityPair n,
      S * (1 - freeResolventComplementaryPotentialA u₁ u₂ hu₁ hu₂ n z hz) = 1 ∧
      (1 - freeResolventComplementaryPotentialA u₁ u₂ hu₁ hu₂ n z hz) * S = 1 ∧
      (freeResolventComplementaryProjectionTransported n).comp S =
        S.comp (freeResolventComplementaryProjectionTransported n) ∧
      (∀ x, freeResolventComplementaryProjectionTransported n x = x →
        freeResolventComplementaryProjectionTransported n (S x) = S x) ∧
      (∀ x, x ∈ Set.range (freeResolventComplementaryProjectionTransported n) →
        S x ∈ Set.range (freeResolventComplementaryProjectionTransported n)) ∧
      (∀ x, x ∈ Set.range (freeResolventComplementaryProjectionTransported n) ↔
        freeResolventComplementaryProjectionTransported n x = x) ∧
      ‖S‖ ≤ freeResolventComplementaryInverseUniformConstant22 * R := by
  let D : ParityPair n →L[ℂ] ParityPair n := freeResolventParityPair n z hz
  let V : ParityPair n →L[ℂ] ParityPair n :=
    coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n
  let Q : ParityPair n →L[ℂ] ParityPair n :=
    freeResolventComplementaryProjectionTransported n
  let A : ParityPair n →L[ℂ] ParityPair n := D.comp (V.comp Q)
  have hD : ‖D‖ ≤ 1 := by
    let E := parityPairRepr n
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    change ‖E.symm (freeResolventSquare n z hz (E x))‖ ≤ 1 * ‖x‖
    calc
      ‖E.symm (freeResolventSquare n z hz (E x))‖ =
          ‖freeResolventSquare n z hz (E x)‖ := E.symm.norm_map _
      _ ≤ ‖freeResolventSquare n z hz‖ * ‖E x‖ :=
        (freeResolventSquare n z hz).le_opNorm _
      _ ≤ 1 * ‖x‖ := by
        rw [E.norm_map]
        gcongr
        exact freeResolventSquare_norm_le_one n z hz
  have hV : ‖V‖ ≤ 2 * physicalH1MultiplierConstant * R := by
    have hR0 : 0 ≤ R := le_trans (by norm_num) hR
    exact coveredH1ParityPairPotential_norm_bound u₁ u₂ hu₁ hu₂ n R hR0 hball₁ hball₂
  have hQ : ‖Q‖ ≤ 1 := freeResolventComplementaryProjectionTransported_norm_le_one n
  have hA : ‖A‖ ≤ 2 * physicalH1MultiplierConstant * R := by
    calc
      ‖A‖ = ‖D.comp (V.comp Q)‖ := rfl
      _ ≤ ‖D‖ * ‖V.comp Q‖ := D.opNorm_comp_le _
      _ ≤ ‖D‖ * (‖V‖ * ‖Q‖) :=
        mul_le_mul_of_nonneg_left (V.opNorm_comp_le Q) (norm_nonneg D)
      _ ≤ 1 * (‖V‖ * ‖Q‖) := by
        exact mul_le_mul_of_nonneg_right hD
          (mul_nonneg (norm_nonneg V) (norm_nonneg Q))
      _ ≤ 1 * (‖V‖ * 1) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hQ (norm_nonneg V)) (by norm_num)
      _ ≤ 2 * physicalH1MultiplierConstant * R := by simpa using hV
  have hA2 : ‖A * A‖ ≤ (1 / 2 : ℝ) := by
    have hsquare := freeResolventComplementaryPotentialA_square_norm_le_half
      u₁ u₂ hu₁ hu₂ R hR hball₁ hball₂ n hn z hz hlarge
    change ‖A.comp A‖ ≤ (1 / 2 : ℝ)
    simpa only [A, D, V, Q, freeResolventComplementaryPotentialA] using hsquare
  have hB : 0 ≤ 2 * physicalH1MultiplierConstant * R :=
    physicalH1MultiplierConstant_radius_nonneg R hR
  letI : Nonempty (Bool × Sector n) := ⟨(true, resonantIndex n)⟩
  letI : Nontrivial (SectorSquare n) := nontrivial_of_ne
    (lp.single 2 (true, resonantIndex n) (1 : ℂ)) 0 (by
      intro hz0
      have hval := congrArg (fun f : SectorSquare n => f (true, resonantIndex n)) hz0
      simpa using hval)
  letI : Nontrivial (ParityPair n) :=
    (parityPairRepr n).toEquiv.nontrivial_congr.mpr inferInstance
  have hQ2 : Q.comp Q = Q :=
    freeResolventComplementaryProjectionTransported_idempotent_actual22 n
  have hQD : Q.comp D = D :=
    freeResolventComplementaryProjectionTransported_comp_freeResolventParityPair n z hz
  have hAQ : A.comp Q = A := by
    calc
      A.comp Q = D.comp (V.comp (Q.comp Q)) := by
        simp only [A, ContinuousLinearMap.comp_assoc]
      _ = A := by rw [hQ2]
  have hQA : Q.comp A = A := by
    calc
      Q.comp A = (Q.comp D).comp (V.comp Q) := by
        simp only [A, ContinuousLinearMap.comp_assoc]
      _ = A := by rw [hQD]
  have hbound : 2 * (1 + 2 * physicalH1MultiplierConstant * R) ≤
      freeResolventComplementaryInverseUniformConstant22 * R := by
    dsimp [freeResolventComplementaryInverseUniformConstant22]
    nlinarith [hR]
  obtain ⟨S, hright, hleft, hcomm, hfix, hrange, hrangeEq, hnorm⟩ :=
    continuousLinearMap_square_neumann_inverse_preserves_projection_range
      Q A (2 * physicalH1MultiplierConstant * R)
      (freeResolventComplementaryInverseUniformConstant22 * R)
      hQ2 hAQ hQA hB hA hA2 hbound
  refine ⟨S, ?_, ?_, hcomm, hfix, hrange, hrangeEq, hnorm⟩
  · simpa only [A, D, V, Q, freeResolventComplementaryPotentialA] using hright
  · simpa only [A, D, V, Q, freeResolventComplementaryPotentialA] using hleft

/-- The actual `Q V D` inverse also restricts to the same complementary
range and has the same absolute `O(R)` bound. -/
theorem freeResolventComplementaryPotentialOpposite_neumann_inverse_range_actual22
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (R : ℝ) (hR : 1 ≤ R)
    (hball₁ : ‖physicalSobolevL2 1 u₁ hu₁‖ ≤ R)
    (hball₂ : ‖physicalSobolevL2 1 u₂ hu₂‖ ≤ R)
    (n : ℤ) (hn : 1 ≤ |(n : ℝ)|)
    (z : ℂ) (hz : z ∈ spectralDisk n)
    (hlarge : 4 * freeResolventSchurUniformConstant *
      physicalH1MultiplierConstant * R ^ 2 ≤ |(n : ℝ)|) :
    ∃ S : ParityPair n →L[ℂ] ParityPair n,
      S * (1 - freeResolventComplementaryPotentialOppositeFactor22
        u₁ u₂ hu₁ hu₂ n z hz) = 1 ∧
      (1 - freeResolventComplementaryPotentialOppositeFactor22
        u₁ u₂ hu₁ hu₂ n z hz) * S = 1 ∧
      (freeResolventComplementaryProjectionTransported n).comp S =
        S.comp (freeResolventComplementaryProjectionTransported n) ∧
      (∀ x, freeResolventComplementaryProjectionTransported n x = x →
        freeResolventComplementaryProjectionTransported n (S x) = S x) ∧
      (∀ x, x ∈ Set.range (freeResolventComplementaryProjectionTransported n) →
        S x ∈ Set.range (freeResolventComplementaryProjectionTransported n)) ∧
      (∀ x, x ∈ Set.range (freeResolventComplementaryProjectionTransported n) ↔
        freeResolventComplementaryProjectionTransported n x = x) ∧
      ‖S‖ ≤ freeResolventComplementaryInverseUniformConstant22 * R := by
  let D : ParityPair n →L[ℂ] ParityPair n := freeResolventParityPair n z hz
  let V : ParityPair n →L[ℂ] ParityPair n :=
    coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n
  let Q : ParityPair n →L[ℂ] ParityPair n :=
    freeResolventComplementaryProjectionTransported n
  let A : ParityPair n →L[ℂ] ParityPair n := Q.comp (V.comp D)
  have hD : ‖D‖ ≤ 1 := by
    let E := parityPairRepr n
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    change ‖E.symm (freeResolventSquare n z hz (E x))‖ ≤ 1 * ‖x‖
    calc
      ‖E.symm (freeResolventSquare n z hz (E x))‖ =
          ‖freeResolventSquare n z hz (E x)‖ := E.symm.norm_map _
      _ ≤ ‖freeResolventSquare n z hz‖ * ‖E x‖ :=
        (freeResolventSquare n z hz).le_opNorm _
      _ ≤ 1 * ‖x‖ := by
        rw [E.norm_map]
        gcongr
        exact freeResolventSquare_norm_le_one n z hz
  have hV : ‖V‖ ≤ 2 * physicalH1MultiplierConstant * R := by
    have hR0 : 0 ≤ R := le_trans (by norm_num) hR
    exact coveredH1ParityPairPotential_norm_bound u₁ u₂ hu₁ hu₂ n R hR0 hball₁ hball₂
  have hQ : ‖Q‖ ≤ 1 := freeResolventComplementaryProjectionTransported_norm_le_one n
  have hA : ‖A‖ ≤ 2 * physicalH1MultiplierConstant * R := by
    calc
      ‖A‖ = ‖Q.comp (V.comp D)‖ := rfl
      _ ≤ ‖Q‖ * ‖V.comp D‖ := Q.opNorm_comp_le _
      _ ≤ ‖Q‖ * (‖V‖ * ‖D‖) :=
        mul_le_mul_of_nonneg_left (V.opNorm_comp_le D) (norm_nonneg Q)
      _ ≤ 1 * (‖V‖ * ‖D‖) := by
        exact mul_le_mul_of_nonneg_right hQ
          (mul_nonneg (norm_nonneg V) (norm_nonneg D))
      _ ≤ 1 * (‖V‖ * 1) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hD (norm_nonneg V))
          (by norm_num)
      _ ≤ 2 * physicalH1MultiplierConstant * R := by simpa using hV
  have hA2 : ‖A * A‖ ≤ (1 / 2 : ℝ) := by
    have hsquare := freeResolventComplementaryPotentialOpposite_square_norm_le_half_actual22
      u₁ u₂ hu₁ hu₂ R hR hball₁ hball₂ n hn z hz hlarge
    simpa only [A, D, V, Q, freeResolventComplementaryPotentialOppositeFactor22,
      ContinuousLinearMap.mul_def] using hsquare
  have hB : 0 ≤ 2 * physicalH1MultiplierConstant * R :=
    physicalH1MultiplierConstant_radius_nonneg R hR
  letI : Nonempty (Bool × Sector n) := ⟨(true, resonantIndex n)⟩
  letI : Nontrivial (SectorSquare n) := nontrivial_of_ne
    (lp.single 2 (true, resonantIndex n) (1 : ℂ)) 0 (by
      intro hz0
      have hval := congrArg (fun f : SectorSquare n => f (true, resonantIndex n)) hz0
      simpa using hval)
  letI : Nontrivial (ParityPair n) :=
    (parityPairRepr n).toEquiv.nontrivial_congr.mpr inferInstance
  have hQ2 : Q.comp Q = Q :=
    freeResolventComplementaryProjectionTransported_idempotent_actual22 n
  have hDQ : D.comp Q = D :=
    freeResolventParityPair_comp_complementaryProjection_right_afterCoordinateRange n z hz
  have hAQ : A.comp Q = A := by
    calc
      A.comp Q = Q.comp (V.comp (D.comp Q)) := by
        simp only [A, ContinuousLinearMap.comp_assoc]
      _ = A := by rw [hDQ]
  have hQA : Q.comp A = A := by
    calc
      Q.comp A = (Q.comp Q).comp (V.comp D) := by
        simp only [A, ContinuousLinearMap.comp_assoc]
      _ = A := by rw [hQ2]
  have hbound : 2 * (1 + 2 * physicalH1MultiplierConstant * R) ≤
      freeResolventComplementaryInverseUniformConstant22 * R := by
    dsimp [freeResolventComplementaryInverseUniformConstant22]
    nlinarith [hR]
  obtain ⟨S, hright, hleft, hcomm, hfix, hrange, hrangeEq, hnorm⟩ :=
    continuousLinearMap_square_neumann_inverse_preserves_projection_range
      Q A (2 * physicalH1MultiplierConstant * R)
      (freeResolventComplementaryInverseUniformConstant22 * R)
      hQ2 hAQ hQA hB hA hA2 hbound
  refine ⟨S, ?_, ?_, hcomm, hfix, hrange, hrangeEq, hnorm⟩
  · simpa only [A, D, V, Q, freeResolventComplementaryPotentialOppositeFactor22] using hright
  · simpa only [A, D, V, Q, freeResolventComplementaryPotentialOppositeFactor22] using hleft

end NlsGge.Schur
