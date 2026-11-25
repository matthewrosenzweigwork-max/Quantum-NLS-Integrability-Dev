import NlsGge.Schur.ActualSchurAlphaBoundAfterDextV6_32
import NlsGge.Schur.ActualSchurFGboundAfterResolventFactorizationV5_31
import NlsGge.Schur.FreeResolventComplementaryDQTransportAfterCoordinateRange

/-!
# F:eq:brem for the actual Schur effective matrix (NEW-F03.04, part)

Source: `paper/v2.tex` lines 1112-1116.  For the actual effective operator
`A_n = P V P + P V (D S) V P` (built from the radius-two `Dext` family and the
actual joint complementary inverse `S = (1 - Q V D)⁻¹`), the `(+,-)` entry
`b_n` satisfies `|b_n(λ) - (u₁)_n| ≤ C R^4 / n^2`, uniformly on the original
signed spectral disk `|λ - nπ| ≤ 1` and the two independent complex H¹ balls.

Proof (source order): `⟨e₊, P V P e₋⟩ = (u₁)_n`; the resolvent identity
`D S = D + D V D S` (from `(1 - QVD) S = 1` and `D Q = D`) splits the
correction; `P V D V P` is channel diagonal so its `(+,-)` entry vanishes; the
remaining factors `P V D`, `V`, `G_n = D S V P` are bounded by the checked
row, multiplier, and Green column estimates.
-/

set_option autoImplicit false
noncomputable section
open scoped InnerProduct InnerProductSpace
open NlsGge.Analysis NlsGge.Pilot

namespace NlsGge.Schur

/-- The actual free resolvent preserves vanishing of a channel component. -/
theorem freeResolventParityPair_component_zero38V1 (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralDisk n) (x : ParityPair n) (b : Bool)
    (hx : x b = 0) : freeResolventParityPair n z hz x b = 0 := by
  apply (scalarParityRepr n).injective
  rw [map_zero]
  apply lp.ext
  funext m
  let i : Bool × Sector n := (b, if b = true then m else negateIndex n m)
  have hmix : mixedIndex n i = m := by
    cases b <;> simp [i, mixedIndex]
  have h1 := parityPairRepr_apply n (freeResolventParityPair n z hz x) i
  have h2 := freeResolventParityPair_repr_apply n z hz x i
  have h3 := parityPairRepr_apply n x i
  rw [hmix] at h1 h3
  change scalarParityRepr n (freeResolventParityPair n z hz x b) m = 0
  rw [← h1, h2, h3]
  change freeResolventCoeff n z i.2 * scalarParityRepr n (x b) m = 0
  rw [hx, map_zero]
  simp

/-- The channel-diagonal factor `V D V` has zero `(+,-)` resonant entry. -/
theorem actualPotentialFreeResolventPotential_plusMinus_zero38V1
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n) :
    inner ℂ (parityPairVector n (true, resonantIndex n))
      (coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n
        (freeResolventParityPair n z hz
          (coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n
            (parityPairVector n (false, resonantIndex n))))) = 0 := by
  let V := coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n
  let D := freeResolventParityPair n z hz
  have hV0 : V (parityPairVector n (false, resonantIndex n)) false = 0 := by
    simp [V, parityPairVector]
  have hD0 : D (V (parityPairVector n (false, resonantIndex n))) false = 0 :=
    freeResolventParityPair_component_zero38V1 n z hz _ false hV0
  have hT : V (D (V (parityPairVector n (false, resonantIndex n)))) true = 0 := by
    change coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n
      (D (V (parityPairVector n (false, resonantIndex n)))) true = 0
    rw [coveredH1ParityPairPotential_apply_true, hD0, map_zero]
  change inner ℂ (parityPairVector n (true, resonantIndex n))
    (V (D (V (parityPairVector n (false, resonantIndex n))))) = 0
  rw [PiLp.inner_apply, Fintype.sum_bool, hT]
  simp [parityPairVector]

/-- Exact `(+,-)` resonant entry of the actual paired potential: `(u₁)_n`. -/
theorem actualPotential_plusMinus_resonant_entry38V1
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂)) (n : ℤ) :
    inner ℂ (parityPairVector n (true, resonantIndex n))
      (coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n
        (parityPairVector n (false, resonantIndex n))) =
      physicalFourier u₁ n := by
  rw [actualPotentialTranspose_pair_entry_formula24]
  have h : ((resonantIndex n).val + (resonantIndex n).val) / 2 = n := by
    simp only [resonantIndex]
    omega
  simp [h]

/-- The channel-diagonal factor `V D V` has zero `(-,+)` resonant entry. -/
theorem actualPotentialFreeResolventPotential_minusPlus_zero38V1
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n) :
    inner ℂ (parityPairVector n (false, resonantIndex n))
      (coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n
        (freeResolventParityPair n z hz
          (coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n
            (parityPairVector n (true, resonantIndex n))))) = 0 := by
  let V := coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n
  let D := freeResolventParityPair n z hz
  have hV0 : V (parityPairVector n (true, resonantIndex n)) true = 0 := by
    simp [V, parityPairVector]
  have hD0 : D (V (parityPairVector n (true, resonantIndex n))) true = 0 :=
    freeResolventParityPair_component_zero38V1 n z hz _ true hV0
  have hT : V (D (V (parityPairVector n (true, resonantIndex n)))) false = 0 := by
    change coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n
      (D (V (parityPairVector n (true, resonantIndex n)))) false = 0
    rw [coveredH1ParityPairPotential_apply_false, hD0, map_zero]
  change inner ℂ (parityPairVector n (false, resonantIndex n))
    (V (D (V (parityPairVector n (true, resonantIndex n))))) = 0
  rw [PiLp.inner_apply, Fintype.sum_bool, hT]
  simp [parityPairVector]

/-- Exact `(-,+)` resonant entry of the actual paired potential: `(u₂)_{-n}`. -/
theorem actualPotential_minusPlus_resonant_entry38V1
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂)) (n : ℤ) :
    inner ℂ (parityPairVector n (false, resonantIndex n))
      (coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n
        (parityPairVector n (true, resonantIndex n))) =
      physicalFourier u₂ (-n) := by
  rw [actualPotentialTranspose_pair_entry_formula24]
  have h : (-(resonantIndex n).val + -(resonantIndex n).val) / 2 = -n := by
    simp only [resonantIndex]
    omega
  simp [h]

set_option maxHeartbeats 400000 in
/-- F:eq:brem for the actual Dext-defined Schur effective operator: its
`(+,-)` coefficient `b_n(λ)` differs from the actual Fourier coefficient
`(u₁)_n` by at most `C R^4/n^2`, uniformly on the original signed spectral
disk and two independent complex H¹ balls of radius `R`. The constant is the
displayed product of the checked row, multiplier, inverse, and free-resolvent
constants; it does not depend on `n`, `z`, `R`, or the potential pair. -/
theorem actualSchurOffDiagonal_sub_fourier_bound38V1
    (R : ℝ) (hR : 1 ≤ R)
    (n : ℤ) (hn : 1 ≤ |(n : ℝ)|)
    (hlarge : 4 * freeResolventSchurUniformConstant *
      physicalH1MultiplierConstant * R ^ 2 ≤ |(n : ℝ)|)
    (z : ℂ) (p : ActualSchurEffectiveH1PairV3_30)
    (hz : z ∈ spectralDisk n) (hp₁ : ‖p.1‖ ≤ R) (hp₂ : ‖p.2‖ ≤ R) :
    ‖actualSchurCoefficientAfterDext31 n
        (true, resonantIndex n) (false, resonantIndex n) (z, p) -
      physicalFourier (physicalH1ComplexCarrierToL2Actual22 p.1) n‖ ≤
      2 * freeResolventSchurUniformConstant ^ 2 *
        freeResolventComplementaryInverseUniformConstant22 *
        physicalH1MultiplierConstant * R ^ 4 / |(n : ℝ)| ^ 2 := by
  let u₁ : PhysicalL2 := physicalH1ComplexCarrierToL2Actual22 p.1
  let u₂ : PhysicalL2 := physicalH1ComplexCarrierToL2Actual22 p.2
  let hu₁ : SobolevSquareSummable 1 (physicalFourier u₁) :=
    physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.1
  let hu₂ : SobolevSquareSummable 1 (physicalFourier u₂) :=
    physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.2
  let P : ParityPair n →L[ℂ] ParityPair n := resonantParityPair n
  let V : ParityPair n →L[ℂ] ParityPair n :=
    coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n
  let D : ParityPair n →L[ℂ] ParityPair n := freeResolventParityPair n z hz
  let Q : ParityPair n →L[ℂ] ParityPair n :=
    freeResolventComplementaryProjectionTransported n
  let K : ParityPair n →L[ℂ] ParityPair n :=
    actualComplementaryQVDJointParameterV5_30 n (z, p)
  let S : ParityPair n →L[ℂ] ParityPair n :=
    actualComplementaryQVDJointInverseV5_30 n (z, p)
  let e : ParityPair n := parityPairVector n (true, resonantIndex n)
  let f : ParityPair n := parityPairVector n (false, resonantIndex n)
  have hD : actualFreeResolventCenterExtensionV1_30 n z = D :=
    actualFreeResolventCenterExtension_eq_actualV1_30 n z hz
  have hV :
      actualParityPairPotentialParameterAfterScalarWrapperCLM23 n p = V := by
    dsimp [V, u₁, u₂, hu₁, hu₂]
    exact actualParityPairPotentialParameterAfterScalarWrapperCLM23_apply n p
  have hK : K = Q.comp (V.comp D) := by
    dsimp [K, actualComplementaryQVDJointParameterV5_30]
    rw [hV, hD]
  have hM : actualSchurEffectiveOperatorAfterDextV3_30 n (z, p) =
      P.comp (V.comp P) +
        P.comp (V.comp ((D.comp S).comp (V.comp P))) := by
    dsimp [actualSchurEffectiveOperatorAfterDextV3_30]
    rw [hV, hD]
    rfl
  have hPf : P f = f := by
    dsimp [P, f]
    simp [resonantParityPair_apply_basis]
  have hProw (x : ParityPair n) : inner ℂ e (P x) = inner ℂ e x := by
    calc
      inner ℂ e (P x) = parityPairRepr n (P x) (true, resonantIndex n) := by
        exact (parityPairRepr_inner n (P x)
          (true, resonantIndex n)).symm
      _ = parityPairRepr n x (true, resonantIndex n) := by
        simp [P, resonantParityPair_repr_apply]
      _ = inner ℂ e x := parityPairRepr_inner n x (true, resonantIndex n)
  -- Resolvent identity `D S w = D w + D V D S w`.
  have htwo := (actualComplementaryQVDJointInverseV5_30_twoSided
    R hR n hn hlarge z p hz hp₁ hp₂).2
  have hSw (w : ParityPair n) : S w = w + Q (V (D (S w))) := by
    have h := congrArg (fun T : ParityPair n →L[ℂ] ParityPair n => T w) htwo
    change (1 - K).comp S w = (1 : ParityPair n →L[ℂ] ParityPair n) w at h
    rw [hK] at h
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.one_apply] at h
    exact sub_eq_iff_eq_add.mp h
  have hDQ (x : ParityPair n) : D (Q x) = D x := by
    have h := freeResolventParityPair_comp_complementaryProjection_right_afterCoordinateRange
      n z hz
    exact congrArg (fun T : ParityPair n →L[ℂ] ParityPair n => T x) h
  have hDSw (w : ParityPair n) : D (S w) = D w + D (V (D (S w))) := by
    conv_lhs => rw [hSw w]
    rw [map_add, hDQ]
  let w : ParityPair n := V f
  let G : ParityPair n →L[ℂ] ParityPair n :=
    actualSchurGreenColumnV5_31 n z p hz
  have hGf : G f = D (S w) := by
    change D (S (V (P f))) = D (S w)
    rw [hPf]
  let row : ParityPair n →L[ℂ] ParityPair n := P.comp (V.comp D)
  have hzero : inner ℂ e (V (D w)) = 0 := by
    dsimp [e, V, D, w, f]
    exact actualPotentialFreeResolventPotential_plusMinus_zero38V1
      u₁ u₂ hu₁ hu₂ n z hz
  have hfirst : inner ℂ e ((P.comp (V.comp P)) f) =
      physicalFourier u₁ n := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hPf,
      hProw]
    exact actualPotential_plusMinus_resonant_entry38V1 u₁ u₂ hu₁ hu₂ n
  have hsecond : inner ℂ e
      ((P.comp (V.comp ((D.comp S).comp (V.comp P)))) f) =
      inner ℂ e (row (V (G f))) := by
    have h1 : (P.comp (V.comp ((D.comp S).comp (V.comp P)))) f =
        P (V (D (S w))) := by
      simp only [ContinuousLinearMap.comp_apply, hPf, w]
    rw [h1, hProw, hDSw w, map_add,
      actualParityPairComplexInnerAddRightMinimumV1_32, hzero, zero_add,
      hGf]
    dsimp [row]
    rw [hProw]
  have hentry : actualSchurCoefficientAfterDext31 n
      (true, resonantIndex n) (false, resonantIndex n) (z, p) =
      physicalFourier u₁ n + inner ℂ e (row (V (G f))) := by
    rw [actualSchurCoefficientAfterDext31]
    change inner ℂ e (actualSchurEffectiveOperatorAfterDextV3_30 n (z, p) f) = _
    rw [hM, ContinuousLinearMap.add_apply,
      actualParityPairComplexInnerAddRightMinimumV1_32, hfirst, hsecond]
  -- Norm estimates.
  have hball₁ : ‖physicalSobolevL2 1 u₁ hu₁‖ ≤ R := by
    rw [actualPhysicalH1Carrier_sobolev_normAfterScalar23]
    exact hp₁
  have hball₂ : ‖physicalSobolevL2 1 u₂ hu₂‖ ≤ R := by
    rw [actualPhysicalH1Carrier_sobolev_normAfterScalar23]
    exact hp₂
  have hrowPack := freeResolventPotential_uniform_bounds_on_h1_ball
    u₁ u₂ hu₁ hu₂ R hR hball₁ hball₂ n hn z hz
  have hrow : ‖row‖ ≤
      freeResolventSchurUniformConstant * R / |(n : ℝ)| := by
    change ‖resonantPotentialFreeResolventRow u₁ u₂ hu₁ hu₂ n z hz‖ ≤ _
    have hpack : ‖freeResolventPotentialColumn u₁ u₂ hu₁ hu₂ n z hz‖ +
        ‖resonantPotentialFreeResolventRow u₁ u₂ hu₁ hu₂ n z hz‖ ≤
        freeResolventSchurUniformConstant * R / |(n : ℝ)| := by
      exact hrowPack.1
    have hle : ‖resonantPotentialFreeResolventRow u₁ u₂ hu₁ hu₂ n z hz‖ ≤
        ‖freeResolventPotentialColumn u₁ u₂ hu₁ hu₂ n z hz‖ +
          ‖resonantPotentialFreeResolventRow u₁ u₂ hu₁ hu₂ n z hz‖ :=
      le_add_of_nonneg_left
        (norm_nonneg (freeResolventPotentialColumn u₁ u₂ hu₁ hu₂ n z hz))
    exact le_trans hle hpack
  have hVn : ‖V‖ ≤ 2 * physicalH1MultiplierConstant * R := by
    dsimp [V]
    exact coveredH1ParityPairPotential_norm_bound u₁ u₂ hu₁ hu₂ n R
      (le_trans (by norm_num) hR) hball₁ hball₂
  have hGn : ‖G‖ ≤ freeResolventComplementaryInverseUniformConstant22 *
      freeResolventSchurUniformConstant * R ^ 2 / |(n : ℝ)| :=
    actualSchurGreenColumn_boundV5_31 R hR n hn hlarge z p hz hp₁ hp₂
  have he_norm : ‖e‖ = 1 := by
    dsimp [e]
    rw [← (parityPairRepr n).norm_map, parityPairRepr_vector]
    simp
  have hf_norm : ‖f‖ = 1 := by
    dsimp [f]
    rw [← (parityPairRepr n).norm_map, parityPairRepr_vector]
    simp
  have hCpos : 0 < freeResolventSchurUniformConstant := by
    unfold freeResolventSchurUniformConstant
    positivity
  have hIpos : 0 < freeResolventComplementaryInverseUniformConstant22 :=
    freeResolventComplementaryInverseUniformConstant22_posV2_31
  have hMpos : 0 < physicalH1MultiplierConstant :=
    physicalH1MultiplierConstant_pos
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) hR
  have hnpos : 0 < |(n : ℝ)| := lt_of_lt_of_le (by norm_num) hn
  have hvec : ‖row (V (G f))‖ ≤ ‖row‖ * (‖V‖ * (‖G‖ * ‖f‖)) := by
    calc
      ‖row (V (G f))‖ ≤ ‖row‖ * ‖V (G f)‖ := row.le_opNorm _
      _ ≤ ‖row‖ * (‖V‖ * ‖G f‖) := by
        gcongr
        exact V.le_opNorm _
      _ ≤ ‖row‖ * (‖V‖ * (‖G‖ * ‖f‖)) := by
        gcongr
        exact G.le_opNorm _
  rw [hentry, add_sub_cancel_left]
  calc
    ‖inner ℂ e (row (V (G f)))‖ ≤ ‖e‖ * ‖row (V (G f))‖ :=
      parityPair_inner_norm_le_prerequisite n e _
    _ ≤ 1 * (‖row‖ * (‖V‖ * (‖G‖ * 1))) := by
      rw [he_norm]
      simpa only [hf_norm] using
        (mul_le_mul_of_nonneg_left hvec (by norm_num : (0 : ℝ) ≤ 1))
    _ ≤ 1 * ((freeResolventSchurUniformConstant * R / |(n : ℝ)|) *
        ((2 * physicalH1MultiplierConstant * R) *
          ((freeResolventComplementaryInverseUniformConstant22 *
            freeResolventSchurUniformConstant * R ^ 2 / |(n : ℝ)|) * 1))) := by
      gcongr
    _ = 2 * freeResolventSchurUniformConstant ^ 2 *
        freeResolventComplementaryInverseUniformConstant22 *
        physicalH1MultiplierConstant * R ^ 4 / |(n : ℝ)| ^ 2 := by
      field_simp

set_option maxHeartbeats 400000 in
/-- F:eq:brem for the actual Dext-defined Schur effective operator: its
`(-,+)` coefficient `c_n(λ)` differs from the actual Fourier coefficient
`(u₂)_{-n}` by at most `C R^4/n^2`, uniformly on the original signed spectral
disk and two independent complex H¹ balls of radius `R`. The constant is the
displayed product of the checked row, multiplier, inverse, and free-resolvent
constants; it does not depend on `n`, `z`, `R`, or the potential pair. -/
theorem actualSchurLowerOffDiagonal_sub_fourier_bound38V1
    (R : ℝ) (hR : 1 ≤ R)
    (n : ℤ) (hn : 1 ≤ |(n : ℝ)|)
    (hlarge : 4 * freeResolventSchurUniformConstant *
      physicalH1MultiplierConstant * R ^ 2 ≤ |(n : ℝ)|)
    (z : ℂ) (p : ActualSchurEffectiveH1PairV3_30)
    (hz : z ∈ spectralDisk n) (hp₁ : ‖p.1‖ ≤ R) (hp₂ : ‖p.2‖ ≤ R) :
    ‖actualSchurCoefficientAfterDext31 n
        (false, resonantIndex n) (true, resonantIndex n) (z, p) -
      physicalFourier (physicalH1ComplexCarrierToL2Actual22 p.2) (-n)‖ ≤
      2 * freeResolventSchurUniformConstant ^ 2 *
        freeResolventComplementaryInverseUniformConstant22 *
        physicalH1MultiplierConstant * R ^ 4 / |(n : ℝ)| ^ 2 := by
  let u₁ : PhysicalL2 := physicalH1ComplexCarrierToL2Actual22 p.1
  let u₂ : PhysicalL2 := physicalH1ComplexCarrierToL2Actual22 p.2
  let hu₁ : SobolevSquareSummable 1 (physicalFourier u₁) :=
    physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.1
  let hu₂ : SobolevSquareSummable 1 (physicalFourier u₂) :=
    physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.2
  let P : ParityPair n →L[ℂ] ParityPair n := resonantParityPair n
  let V : ParityPair n →L[ℂ] ParityPair n :=
    coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n
  let D : ParityPair n →L[ℂ] ParityPair n := freeResolventParityPair n z hz
  let Q : ParityPair n →L[ℂ] ParityPair n :=
    freeResolventComplementaryProjectionTransported n
  let K : ParityPair n →L[ℂ] ParityPair n :=
    actualComplementaryQVDJointParameterV5_30 n (z, p)
  let S : ParityPair n →L[ℂ] ParityPair n :=
    actualComplementaryQVDJointInverseV5_30 n (z, p)
  let e : ParityPair n := parityPairVector n (false, resonantIndex n)
  let f : ParityPair n := parityPairVector n (true, resonantIndex n)
  have hD : actualFreeResolventCenterExtensionV1_30 n z = D :=
    actualFreeResolventCenterExtension_eq_actualV1_30 n z hz
  have hV :
      actualParityPairPotentialParameterAfterScalarWrapperCLM23 n p = V := by
    dsimp [V, u₁, u₂, hu₁, hu₂]
    exact actualParityPairPotentialParameterAfterScalarWrapperCLM23_apply n p
  have hK : K = Q.comp (V.comp D) := by
    dsimp [K, actualComplementaryQVDJointParameterV5_30]
    rw [hV, hD]
  have hM : actualSchurEffectiveOperatorAfterDextV3_30 n (z, p) =
      P.comp (V.comp P) +
        P.comp (V.comp ((D.comp S).comp (V.comp P))) := by
    dsimp [actualSchurEffectiveOperatorAfterDextV3_30]
    rw [hV, hD]
    rfl
  have hPf : P f = f := by
    dsimp [P, f]
    simp [resonantParityPair_apply_basis]
  have hProw (x : ParityPair n) : inner ℂ e (P x) = inner ℂ e x := by
    calc
      inner ℂ e (P x) = parityPairRepr n (P x) (false, resonantIndex n) := by
        exact (parityPairRepr_inner n (P x)
          (false, resonantIndex n)).symm
      _ = parityPairRepr n x (false, resonantIndex n) := by
        simp [P, resonantParityPair_repr_apply]
      _ = inner ℂ e x := parityPairRepr_inner n x (false, resonantIndex n)
  -- Resolvent identity `D S w = D w + D V D S w`.
  have htwo := (actualComplementaryQVDJointInverseV5_30_twoSided
    R hR n hn hlarge z p hz hp₁ hp₂).2
  have hSw (w : ParityPair n) : S w = w + Q (V (D (S w))) := by
    have h := congrArg (fun T : ParityPair n →L[ℂ] ParityPair n => T w) htwo
    change (1 - K).comp S w = (1 : ParityPair n →L[ℂ] ParityPair n) w at h
    rw [hK] at h
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.one_apply] at h
    exact sub_eq_iff_eq_add.mp h
  have hDQ (x : ParityPair n) : D (Q x) = D x := by
    have h := freeResolventParityPair_comp_complementaryProjection_right_afterCoordinateRange
      n z hz
    exact congrArg (fun T : ParityPair n →L[ℂ] ParityPair n => T x) h
  have hDSw (w : ParityPair n) : D (S w) = D w + D (V (D (S w))) := by
    conv_lhs => rw [hSw w]
    rw [map_add, hDQ]
  let w : ParityPair n := V f
  let G : ParityPair n →L[ℂ] ParityPair n :=
    actualSchurGreenColumnV5_31 n z p hz
  have hGf : G f = D (S w) := by
    change D (S (V (P f))) = D (S w)
    rw [hPf]
  let row : ParityPair n →L[ℂ] ParityPair n := P.comp (V.comp D)
  have hzero : inner ℂ e (V (D w)) = 0 := by
    dsimp [e, V, D, w, f]
    exact actualPotentialFreeResolventPotential_minusPlus_zero38V1
      u₁ u₂ hu₁ hu₂ n z hz
  have hfirst : inner ℂ e ((P.comp (V.comp P)) f) =
      physicalFourier u₂ (-n) := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hPf,
      hProw]
    exact actualPotential_minusPlus_resonant_entry38V1 u₁ u₂ hu₁ hu₂ n
  have hsecond : inner ℂ e
      ((P.comp (V.comp ((D.comp S).comp (V.comp P)))) f) =
      inner ℂ e (row (V (G f))) := by
    have h1 : (P.comp (V.comp ((D.comp S).comp (V.comp P)))) f =
        P (V (D (S w))) := by
      simp only [ContinuousLinearMap.comp_apply, hPf, w]
    rw [h1, hProw, hDSw w, map_add,
      actualParityPairComplexInnerAddRightMinimumV1_32, hzero, zero_add,
      hGf]
    dsimp [row]
    rw [hProw]
  have hentry : actualSchurCoefficientAfterDext31 n
      (false, resonantIndex n) (true, resonantIndex n) (z, p) =
      physicalFourier u₂ (-n) + inner ℂ e (row (V (G f))) := by
    rw [actualSchurCoefficientAfterDext31]
    change inner ℂ e (actualSchurEffectiveOperatorAfterDextV3_30 n (z, p) f) = _
    rw [hM, ContinuousLinearMap.add_apply,
      actualParityPairComplexInnerAddRightMinimumV1_32, hfirst, hsecond]
  -- Norm estimates.
  have hball₁ : ‖physicalSobolevL2 1 u₁ hu₁‖ ≤ R := by
    rw [actualPhysicalH1Carrier_sobolev_normAfterScalar23]
    exact hp₁
  have hball₂ : ‖physicalSobolevL2 1 u₂ hu₂‖ ≤ R := by
    rw [actualPhysicalH1Carrier_sobolev_normAfterScalar23]
    exact hp₂
  have hrowPack := freeResolventPotential_uniform_bounds_on_h1_ball
    u₁ u₂ hu₁ hu₂ R hR hball₁ hball₂ n hn z hz
  have hrow : ‖row‖ ≤
      freeResolventSchurUniformConstant * R / |(n : ℝ)| := by
    change ‖resonantPotentialFreeResolventRow u₁ u₂ hu₁ hu₂ n z hz‖ ≤ _
    have hpack : ‖freeResolventPotentialColumn u₁ u₂ hu₁ hu₂ n z hz‖ +
        ‖resonantPotentialFreeResolventRow u₁ u₂ hu₁ hu₂ n z hz‖ ≤
        freeResolventSchurUniformConstant * R / |(n : ℝ)| := by
      exact hrowPack.1
    have hle : ‖resonantPotentialFreeResolventRow u₁ u₂ hu₁ hu₂ n z hz‖ ≤
        ‖freeResolventPotentialColumn u₁ u₂ hu₁ hu₂ n z hz‖ +
          ‖resonantPotentialFreeResolventRow u₁ u₂ hu₁ hu₂ n z hz‖ :=
      le_add_of_nonneg_left
        (norm_nonneg (freeResolventPotentialColumn u₁ u₂ hu₁ hu₂ n z hz))
    exact le_trans hle hpack
  have hVn : ‖V‖ ≤ 2 * physicalH1MultiplierConstant * R := by
    dsimp [V]
    exact coveredH1ParityPairPotential_norm_bound u₁ u₂ hu₁ hu₂ n R
      (le_trans (by norm_num) hR) hball₁ hball₂
  have hGn : ‖G‖ ≤ freeResolventComplementaryInverseUniformConstant22 *
      freeResolventSchurUniformConstant * R ^ 2 / |(n : ℝ)| :=
    actualSchurGreenColumn_boundV5_31 R hR n hn hlarge z p hz hp₁ hp₂
  have he_norm : ‖e‖ = 1 := by
    dsimp [e]
    rw [← (parityPairRepr n).norm_map, parityPairRepr_vector]
    simp
  have hf_norm : ‖f‖ = 1 := by
    dsimp [f]
    rw [← (parityPairRepr n).norm_map, parityPairRepr_vector]
    simp
  have hCpos : 0 < freeResolventSchurUniformConstant := by
    unfold freeResolventSchurUniformConstant
    positivity
  have hIpos : 0 < freeResolventComplementaryInverseUniformConstant22 :=
    freeResolventComplementaryInverseUniformConstant22_posV2_31
  have hMpos : 0 < physicalH1MultiplierConstant :=
    physicalH1MultiplierConstant_pos
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) hR
  have hnpos : 0 < |(n : ℝ)| := lt_of_lt_of_le (by norm_num) hn
  have hvec : ‖row (V (G f))‖ ≤ ‖row‖ * (‖V‖ * (‖G‖ * ‖f‖)) := by
    calc
      ‖row (V (G f))‖ ≤ ‖row‖ * ‖V (G f)‖ := row.le_opNorm _
      _ ≤ ‖row‖ * (‖V‖ * ‖G f‖) := by
        gcongr
        exact V.le_opNorm _
      _ ≤ ‖row‖ * (‖V‖ * (‖G‖ * ‖f‖)) := by
        gcongr
        exact G.le_opNorm _
  rw [hentry, add_sub_cancel_left]
  calc
    ‖inner ℂ e (row (V (G f)))‖ ≤ ‖e‖ * ‖row (V (G f))‖ :=
      parityPair_inner_norm_le_prerequisite n e _
    _ ≤ 1 * (‖row‖ * (‖V‖ * (‖G‖ * 1))) := by
      rw [he_norm]
      simpa only [hf_norm] using
        (mul_le_mul_of_nonneg_left hvec (by norm_num : (0 : ℝ) ≤ 1))
    _ ≤ 1 * ((freeResolventSchurUniformConstant * R / |(n : ℝ)|) *
        ((2 * physicalH1MultiplierConstant * R) *
          ((freeResolventComplementaryInverseUniformConstant22 *
            freeResolventSchurUniformConstant * R ^ 2 / |(n : ℝ)|) * 1))) := by
      gcongr
    _ = 2 * freeResolventSchurUniformConstant ^ 2 *
        freeResolventComplementaryInverseUniformConstant22 *
        physicalH1MultiplierConstant * R ^ 4 / |(n : ℝ)| ^ 2 := by
      field_simp

end NlsGge.Schur
