import NlsGge.Schur.ActualSchurOwnModeAssembly38V1
import NlsGge.Schur.ActualSchurOwnModeVariation38V1
import NlsGge.Schur.ActualSchurPotentialVariation38V1
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# NEW-F04: summable own-mode derivative (F:lem:diagonal)

Source: `paper/v2.tex` lines 1175-1221.  For `‖u_i‖_{H¹} ≤ R` and `|n| ≥ C R^3`
the derivative of the actual coordinate `q_n` with respect to `(u₁)_n`, keeping
`u₂` fixed, satisfies `|∂q_n/∂(u₁)_n - 1| ≤ C R^4/n^2`.

Steps (source order):
* F:eq:ownvariation: at fixed `λ`, `∂A_n = P H_n P + G̃ H_n G` (the cross terms
  vanish by F:eq:crosszero, using `Q G = G` and `D S Q = D S`);
* hence `|∂b_n - 1| + |∂α_n| ≤ 2 ‖G̃‖ ‖G‖`;
* differentiated center equation with `|∂_λ α_n| ≤ 1/4`;
* chain rule with `|∂_λ b_n| ≤ d`, and `d^2 ≤ d/4`.
-/

set_option autoImplicit false
noncomputable section
open scoped InnerProduct InnerProductSpace
open NlsGge.Analysis NlsGge.Pilot

namespace NlsGge.Schur

/-- The derivative scale `d_R = C_I^2 C_S^2 R^4 / n^2`. -/
def actualSchurOwnModeScale38 (R : ℝ) (n : ℤ) : ℝ :=
  freeResolventComplementaryInverseUniformConstant22 ^ 2 *
    freeResolventSchurUniformConstant ^ 2 * R ^ 4 / |(n : ℝ)| ^ 2

set_option maxHeartbeats 400000 in
/-- F:eq:ownvariation, entrywise: each resonant entry of
`(P + G̃) H_n (P + G)` is within `d` of the corresponding entry of `H_n`. -/
theorem actualSchurOwnModeVariation_entry_bound38
    (R : ℝ) (hR : 1 ≤ R)
    (n : ℤ) (hn : 1 ≤ |(n : ℝ)|)
    (hlarge : 4 * freeResolventSchurUniformConstant *
      physicalH1MultiplierConstant * R ^ 2 ≤ |(n : ℝ)|)
    (z : ℂ) (hz : z ∈ spectralDisk n)
    (p : ActualSchurEffectiveH1PairV3_30)
    (hp₁ : ‖p.1‖ ≤ R) (hp₂ : ‖p.2‖ ≤ R) (b c : Bool) :
    ‖actualSchurEntryFunctional31 n (b, resonantIndex n) (c, resonantIndex n)
        (((resonantParityPair n) + actualSchurGreenRowV5_31 n z p hz).comp
          ((actualParityPairPotentialParameterAfterScalarWrapperCLM23 n
              (actualH1ModeVector38 n, 0)).comp
            ((resonantParityPair n) + actualSchurGreenColumnV5_31 n z p hz))) -
      inner ℂ (parityPairVector n (b, resonantIndex n))
        (actualOwnModeVariation38 n (parityPairVector n (c, resonantIndex n)))‖ ≤
      actualSchurOwnModeScale38 R n := by
  let u₁ : PhysicalL2 := physicalH1ComplexCarrierToL2Actual22 p.1
  let u₂ : PhysicalL2 := physicalH1ComplexCarrierToL2Actual22 p.2
  let hu₁ : SobolevSquareSummable 1 (physicalFourier u₁) :=
    physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.1
  let hu₂ : SobolevSquareSummable 1 (physicalFourier u₂) :=
    physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.2
  let P : ParityPair n →L[ℂ] ParityPair n := resonantParityPair n
  let Q : ParityPair n →L[ℂ] ParityPair n := freeResolventComplementaryProjectionTransported n
  let V : ParityPair n →L[ℂ] ParityPair n := coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n
  let D : ParityPair n →L[ℂ] ParityPair n := freeResolventParityPair n z hz
  let S : ParityPair n →L[ℂ] ParityPair n := actualComplementaryQVDJointInverseV5_30 n (z, p)
  let H : ParityPair n →L[ℂ] ParityPair n := actualOwnModeVariation38 n
  let G : ParityPair n →L[ℂ] ParityPair n := actualSchurGreenColumnV5_31 n z p hz
  let Gt : ParityPair n →L[ℂ] ParityPair n := actualSchurGreenRowV5_31 n z p hz
  let e : ParityPair n := parityPairVector n (b, resonantIndex n)
  let f : ParityPair n := parityPairVector n (c, resonantIndex n)
  have hG : G = (D.comp S).comp (V.comp P) := rfl
  have hGt : Gt = P.comp (V.comp (D.comp S)) := rfl
  -- `Q D = D`, `D Q = D`, `S Q = Q S`
  have hQD : Q.comp D = D :=
    freeResolventParityPair_comp_complementaryProjection_afterCoordinateRange n z hz
  have hDQ : D.comp Q = D :=
    freeResolventParityPair_comp_complementaryProjection_right_afterCoordinateRange n z hz
  have hQQ : Q.comp Q = Q :=
    freeResolventComplementaryProjectionTransported_idempotent_actual22 n
  have hV : actualParityPairPotentialParameterAfterScalarWrapperCLM23 n p = V := by
    dsimp [V, u₁, u₂, hu₁, hu₂]
    exact actualParityPairPotentialParameterAfterScalarWrapperCLM23_apply n p
  have hK : actualComplementaryQVDJointParameterV5_30 n (z, p) = Q.comp (V.comp D) := by
    dsimp [actualComplementaryQVDJointParameterV5_30]
    rw [hV, actualFreeResolventCenterExtension_eq_actualV1_30 n z hz]
  have htwo := actualComplementaryQVDJointInverseV5_30_twoSided
    R hR n hn hlarge z p hz hp₁ hp₂
  have hSQ : S.comp Q = Q.comp S := by
    let K : ParityPair n →L[ℂ] ParityPair n := Q.comp (V.comp D)
    have hQK : Q.comp K = K := by
      change Q.comp (Q.comp (V.comp D)) = Q.comp (V.comp D)
      rw [← ContinuousLinearMap.comp_assoc, hQQ]
    have hKQ : K.comp Q = K := by
      change (Q.comp (V.comp D)).comp Q = Q.comp (V.comp D)
      rw [ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_assoc, hDQ]
    have h1 : S.comp (1 - K) = 1 := by
      have := htwo.1; rw [hK] at this; exact this
    have h2 : (1 - K).comp S = 1 := by
      have := htwo.2; rw [hK] at this; exact this
    have hcomm : Q.comp (1 - K) = (1 - K).comp Q := by
      rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp, hQK, hKQ,
        ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id,
        ContinuousLinearMap.id_comp]
    calc S.comp Q = (S.comp Q).comp ((1 - K).comp S) := by
          rw [h2, ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id]
      _ = S.comp ((Q.comp (1 - K)).comp S) := by
        simp only [ContinuousLinearMap.comp_assoc]
      _ = S.comp (((1 - K).comp Q).comp S) := by rw [hcomm]
      _ = (S.comp (1 - K)).comp (Q.comp S) := by
        simp only [ContinuousLinearMap.comp_assoc]
      _ = Q.comp S := by
          rw [h1, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]
  have hDSQ (y : ParityPair n) : D (S (Q y)) = D (S y) := by
    have h1 := congrArg (fun T : ParityPair n →L[ℂ] ParityPair n => T y) hSQ
    simp only [ContinuousLinearMap.comp_apply] at h1
    rw [h1]
    have h2 := congrArg (fun T : ParityPair n →L[ℂ] ParityPair n => T (S y)) hDQ
    simpa only [ContinuousLinearMap.comp_apply] using h2
  have hQy (y : ParityPair n) : Q (D y) = D y := by
    have := congrArg (fun T : ParityPair n →L[ℂ] ParityPair n => T y) hQD
    simpa only [ContinuousLinearMap.comp_apply] using this
  have hPHQ (y : ParityPair n) : P (H (Q y)) = 0 := by
    have := congrArg (fun T : ParityPair n →L[ℂ] ParityPair n => T y)
      (actualOwnModeVariation38_P_H_Q n)
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply] using this
  have hQHP (y : ParityPair n) : Q (H (P y)) = 0 := by
    have := congrArg (fun T : ParityPair n →L[ℂ] ParityPair n => T y)
      (actualOwnModeVariation38_Q_H_P n)
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply] using this
  have hPf : P f = f := by
    dsimp [P, f]; simp [resonantParityPair_apply_basis]
  have hProw (x : ParityPair n) : inner ℂ e (P x) = inner ℂ e x := by
    calc
      inner ℂ e (P x) = parityPairRepr n (P x) (b, resonantIndex n) :=
        (parityPairRepr_inner n (P x) (b, resonantIndex n)).symm
      _ = parityPairRepr n x (b, resonantIndex n) := by
        simp [P, resonantParityPair_repr_apply]
      _ = inner ℂ e x := parityPairRepr_inner n x (b, resonantIndex n)
  -- the two cross terms vanish
  have hGf : Q (G f) = G f := by
    change Q (D (S (V (P f)))) = D (S (V (P f)))
    exact hQy _
  have hcross1 : P (H (G f)) = 0 := by
    rw [← hGf]; exact hPHQ _
  have hcross2 : Gt (H f) = 0 := by
    change P (V (D (S (H f)))) = 0
    have h0 : D (S (H f)) = 0 := by
      rw [← hPf, ← hDSQ (H (P f)), hQHP, map_zero, map_zero]
    rw [h0, map_zero, map_zero]
  have hX : (P + Gt).comp ((actualParityPairPotentialParameterAfterScalarWrapperCLM23 n
      (actualH1ModeVector38 n, 0)).comp (P + G)) f =
      P (H f) + P (H (G f)) + Gt (H f) + Gt (H (G f)) := by
    change (P + Gt) (H ((P + G) f)) = _
    simp only [ContinuousLinearMap.add_apply, map_add, hPf]
    abel
  have hentry : actualSchurEntryFunctional31 n (b, resonantIndex n) (c, resonantIndex n)
      ((P + Gt).comp ((actualParityPairPotentialParameterAfterScalarWrapperCLM23 n
        (actualH1ModeVector38 n, 0)).comp (P + G))) =
      inner ℂ e (H f) + inner ℂ e (Gt (H (G f))) := by
    change inner ℂ e (((P + Gt).comp ((actualParityPairPotentialParameterAfterScalarWrapperCLM23 n
      (actualH1ModeVector38 n, 0)).comp (P + G))) f) = _
    rw [hX, hcross1, hcross2, add_zero, add_zero,
      actualParityPairComplexInnerAddRightMinimumV1_32, hProw]
  change ‖actualSchurEntryFunctional31 n (b, resonantIndex n) (c, resonantIndex n)
      ((P + Gt).comp ((actualParityPairPotentialParameterAfterScalarWrapperCLM23 n
        (actualH1ModeVector38 n, 0)).comp (P + G))) - inner ℂ e (H f)‖ ≤ _
  rw [hentry, add_sub_cancel_left]
  have he : ‖e‖ = 1 := by
    rw [← (parityPairRepr n).norm_map, parityPairRepr_vector]; simp
  have hf : ‖f‖ = 1 := by
    rw [← (parityPairRepr n).norm_map, parityPairRepr_vector]; simp
  have hHn : ‖H‖ ≤ 1 := actualOwnModeVariation38_norm_le_one n
  have hGn := actualSchurGreenColumn_boundV5_31 R hR n hn hlarge z p hz hp₁ hp₂
  have hGtn := actualSchurGreenRow_boundV5_31 R hR n hn hlarge z p hz hp₁ hp₂
  have hc0 : 0 ≤ freeResolventComplementaryInverseUniformConstant22 *
      freeResolventSchurUniformConstant * R ^ 2 / |(n : ℝ)| := by
    have hI : 0 < freeResolventComplementaryInverseUniformConstant22 :=
      freeResolventComplementaryInverseUniformConstant22_posV2_31
    have hS : 0 ≤ freeResolventSchurUniformConstant := by
      unfold freeResolventSchurUniformConstant; positivity
    positivity
  calc ‖inner ℂ e (Gt (H (G f)))‖ ≤ ‖e‖ * ‖Gt (H (G f))‖ :=
        parityPair_inner_norm_le_prerequisite n _ _
    _ ≤ 1 * (‖Gt‖ * (‖H‖ * (‖G‖ * 1))) := by
        rw [he]
        gcongr
        refine le_trans (Gt.le_opNorm _) ?_
        gcongr
        refine le_trans (H.le_opNorm _) ?_
        gcongr
        simpa [hf] using G.le_opNorm f
    _ ≤ 1 * ((freeResolventComplementaryInverseUniformConstant22 *
          freeResolventSchurUniformConstant * R ^ 2 / |(n : ℝ)|) *
        (1 * ((freeResolventComplementaryInverseUniformConstant22 *
          freeResolventSchurUniformConstant * R ^ 2 / |(n : ℝ)|) * 1))) := by
        gcongr
    _ = actualSchurOwnModeScale38 R n := by
        unfold actualSchurOwnModeScale38; ring

/-- Potential component of the joint derivative of an entry at `(σ_n(p), p)`:
it is the fixed-`λ` variation `⟪e_i, (P+G̃) V(h) (P+G) e_j⟫`. -/
theorem actualSchurCoefficientJointDeriv38_potential
    (R : ℝ) (hR : 1 ≤ R) (n : ℤ)
    (hthr : actualSchurCenterThresholdConstant38 * R ^ 3 ≤ |(n : ℝ)|)
    (i j : Bool × Sector n)
    (p : ActualSchurEffectiveH1PairV3_30) (hp₁ : ‖p.1‖ < R) (hp₂ : ‖p.2‖ < R)
    (hz : actualSchurCenter38 R n p ∈ spectralDisk n)
    (h : ActualSchurEffectiveH1PairV3_30) :
    actualSchurCoefficientJointDeriv38 R n i j p (0, h) =
      actualSchurEntryFunctional31 n i j
        (((resonantParityPair n) + actualSchurGreenRowV5_31 n (actualSchurCenter38 R n p) p hz).comp
          ((actualParityPairPotentialParameterAfterScalarWrapperCLM23 n h).comp
            ((resonantParityPair n) +
              actualSchurGreenColumnV5_31 n (actualSchurCenter38 R n p) p hz))) := by
  obtain ⟨hn, hlarge, -, -⟩ :=
    actualSchurCenterThresholdConstant38_consequences R hR n hthr
  set σ0 := actualSchurCenter38 R n p with hσ0
  have hJ := actualSchurCoefficient_hasFDerivAt_center38 R hR n hthr i j p hp₁ hp₂
  have hJ' : HasFDerivAt (actualSchurCoefficientAfterDext31 n i j)
      (actualSchurCoefficientJointDeriv38 R n i j p) (σ0, p + (0 : ℂ) • h) := by
    rw [zero_smul, add_zero]; exact hJ
  have hline : HasDerivAt (fun t : ℂ => ((σ0, p + t • h) : ℂ × ActualSchurEffectiveH1PairV3_30))
      ((0 : ℂ), h) 0 := by
    have h2 : HasDerivAt (fun t : ℂ => p + t • h) h 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const h).const_add p
    exact (hasDerivAt_const (0 : ℂ) σ0).prodMk h2
  have hc := HasFDerivAt.comp_hasDerivAt
    (f := fun t : ℂ => ((σ0, p + t • h) : ℂ × ActualSchurEffectiveH1PairV3_30)) (0 : ℂ) hJ' hline
  have hT := actualSchurCoefficient_hasDerivAt_potentialVariation38V1 R hR n hn hlarge σ0 hz p
    hp₁.le hp₂.le h i j
  exact hc.unique hT

/-- NEW-F04, F:lem:diagonal (F:eq:diagonal): for `‖p.i‖_{H¹} ≤ R` and
`|n| ≥ C (2R)^3`, the complex derivative of the actual auxiliary coordinate
`q_n` (holomorphy radius `2R`) in the own-mode direction `(δ_n, 0)` — the
derivative with respect to `(u₁)_n` at fixed `u₂` — is within
`2 C_I^2 C_S^2 (2R)^4/n^2` of `1`. -/
theorem actualSchurQn38_ownMode_derivative
    (R : ℝ) (hR : 1 ≤ R) (n : ℤ)
    (hthr : actualSchurCenterThresholdConstant38 * (2 * R) ^ 3 ≤ |(n : ℝ)|)
    (p : ActualSchurEffectiveH1PairV3_30) (hp₁ : ‖p.1‖ ≤ R) (hp₂ : ‖p.2‖ ≤ R) :
    ‖fderiv ℂ (actualSchurQn38 (2 * R) n) p (actualH1ModeVector38 n, 0) - 1‖ ≤
      2 * actualSchurOwnModeScale38 (2 * R) n := by
  have h2R : 1 ≤ 2 * R := by linarith
  have hp₁' : ‖p.1‖ < 2 * R := by linarith
  have hp₂' : ‖p.2‖ < 2 * R := by linarith
  obtain ⟨hn, hlarge, -, h14⟩ :=
    actualSchurCenterThresholdConstant38_consequences (2 * R) h2R n hthr
  set d := actualSchurOwnModeScale38 (2 * R) n with hd
  have hd14 : d ≤ 1 / 4 := h14
  have hd0 : 0 ≤ d := by
    have hI : 0 < freeResolventComplementaryInverseUniformConstant22 :=
      freeResolventComplementaryInverseUniformConstant22_posV2_31
    rw [hd]; unfold actualSchurOwnModeScale38; positivity
  obtain ⟨hσb, -⟩ := actualSchurCenter38_spec (2 * R) h2R n hthr p hp₁'.le hp₂'.le
  have hz : actualSchurCenter38 (2 * R) n p ∈ spectralDisk n :=
    closedBall_half_subset_spectralDisk38 n hσb
  set h : ActualSchurEffectiveH1PairV3_30 := (actualH1ModeVector38 n, 0) with hh
  set a := actualSchurCoefficientJointDeriv38 (2 * R) n
    (true, resonantIndex n) (true, resonantIndex n) p with ha
  set β := actualSchurCoefficientJointDeriv38 (2 * R) n
    (true, resonantIndex n) (false, resonantIndex n) p with hβ
  set s := fderiv ℂ (actualSchurCenter38 (2 * R) n) p h with hs
  -- potential components
  have ha0 : ‖a (0, h)‖ ≤ d := by
    rw [ha, actualSchurCoefficientJointDeriv38_potential (2 * R) h2R n hthr _ _ p hp₁' hp₂' hz h]
    have hb := actualSchurOwnModeVariation_entry_bound38 (2 * R) h2R n hn hlarge
      (actualSchurCenter38 (2 * R) n p) hz p hp₁'.le hp₂'.le true true
    rw [actualOwnModeVariation38_resonant_other n true true (by simp), sub_zero] at hb
    exact hb
  have hβ0 : ‖β (0, h) - 1‖ ≤ d := by
    rw [hβ, actualSchurCoefficientJointDeriv38_potential (2 * R) h2R n hthr _ _ p hp₁' hp₂' hz h]
    have hb := actualSchurOwnModeVariation_entry_bound38 (2 * R) h2R n hn hlarge
      (actualSchurCenter38 (2 * R) n p) hz p hp₁'.le hp₂'.le true false
    rw [actualOwnModeVariation38_resonant_plusMinus] at hb
    exact hb
  -- spectral components
  have hspec : ∀ i j : Bool × Sector n,
      ‖actualSchurCoefficientJointDeriv38 (2 * R) n i j p (1, 0)‖ ≤ d := by
    intro i j
    rw [actualSchurCoefficientJointDeriv38_spectral (2 * R) h2R n hthr i j p hp₁' hp₂' hz]
    refine le_trans (actualSchurEntryFunctional31_apply_norm_le38V1 n _ _ _) ?_
    rw [ContinuousLinearMap.opNorm_neg]
    exact actualSchurGreenDerivativeProduct_boundV3_31 (2 * R) h2R n hn hlarge _ p hz
      hp₁'.le hp₂'.le
  have ha1 := hspec (true, resonantIndex n) (true, resonantIndex n)
  have hβ1 := hspec (true, resonantIndex n) (false, resonantIndex n)
  -- center derivative
  have hcen := actualSchurCenter38_fderiv_equation (2 * R) h2R n hthr p hp₁' hp₂' h
  rw [← ha, ← hs] at hcen
  have hden : 3 / 4 ≤ ‖1 - a (1, 0)‖ := by
    have := norm_sub_norm_le (1 : ℂ) (a (1, 0))
    rw [norm_one] at this
    linarith
  have hsb : ‖s‖ ≤ 4 / 3 * d := by
    have h1 : ‖1 - a (1, 0)‖ * ‖s‖ = ‖a (0, h)‖ := by
      rw [← norm_mul, hcen]
    have h2 : 3 / 4 * ‖s‖ ≤ d := by
      calc 3 / 4 * ‖s‖ ≤ ‖1 - a (1, 0)‖ * ‖s‖ :=
            mul_le_mul_of_nonneg_right hden (norm_nonneg _)
        _ = ‖a (0, h)‖ := h1
        _ ≤ d := ha0
    linarith
  -- chain rule
  have hch := actualSchurQn38_fderiv_chain (2 * R) h2R n hthr p hp₁' hp₂' h
  rw [← hβ, ← hs] at hch
  rw [hch]
  have hsplit : β (1, 0) * s + β (0, h) - 1 = β (1, 0) * s + (β (0, h) - 1) := by ring
  rw [hsplit]
  calc ‖β (1, 0) * s + (β (0, h) - 1)‖ ≤ ‖β (1, 0)‖ * ‖s‖ + ‖β (0, h) - 1‖ := by
        refine le_trans (norm_add_le _ _) ?_
        rw [norm_mul]
    _ ≤ d * (4 / 3 * d) + d := by
        gcongr
    _ ≤ 2 * d := by nlinarith

end NlsGge.Schur
