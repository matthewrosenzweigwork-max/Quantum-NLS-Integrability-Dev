import NlsGge.Schur.ActualSchurRealTypeSymmetry38V1

/-!
# Equal diagonals in coefficient form and the real-type determinant factorization

Source: `paper/v2.tex` lines 1100-1106 (equal diagonals; on the real subspace
`α_n ∈ ℝ`, `c_n = conj b_n`) and 1158-1162.  For real `λ` in the disk and a
real-type pair `(u, ū)`, the Schur determinant factors as
`det((λ-nπ) - A_n(λ)) = (F(λ) - |b_n(λ)|)(F(λ) + |b_n(λ)|)`,
`F(λ) = λ - nπ - α_n(λ)` (real).
-/

set_option autoImplicit false
noncomputable section
open scoped InnerProduct InnerProductSpace
open NlsGge.Analysis NlsGge.Pilot

namespace NlsGge.Schur

/-- The 2×2 Schur determinant `det((z - nπ) - A_n(z))`. -/
def actualSchurDet38 (n : ℤ) (p : ActualSchurEffectiveH1PairV3_30) (z : ℂ) : ℂ :=
  (z - spectralCenter n -
      actualSchurCoefficientAfterDext31 n (true, resonantIndex n) (true, resonantIndex n) (z, p)) *
    (z - spectralCenter n -
      actualSchurCoefficientAfterDext31 n (false, resonantIndex n) (false, resonantIndex n) (z, p)) -
  actualSchurCoefficientAfterDext31 n (true, resonantIndex n) (false, resonantIndex n) (z, p) *
    actualSchurCoefficientAfterDext31 n (false, resonantIndex n) (true, resonantIndex n) (z, p)

/-- Equal diagonals of the actual Dext-defined coefficients. -/
theorem actualSchurCoefficient_equal_diagonal38
    (R : ℝ) (hR : 1 ≤ R) (n : ℤ) (hn : 1 ≤ |(n : ℝ)|)
    (hlarge : 4 * freeResolventSchurUniformConstant *
      physicalH1MultiplierConstant * R ^ 2 ≤ |(n : ℝ)|)
    (z : ℂ) (p : ActualSchurEffectiveH1PairV3_30)
    (hz : z ∈ spectralDisk n) (hp₁ : ‖p.1‖ ≤ R) (hp₂ : ‖p.2‖ ≤ R) :
    actualSchurCoefficientAfterDext31 n (false, resonantIndex n) (false, resonantIndex n) (z, p) =
      actualSchurCoefficientAfterDext31 n (true, resonantIndex n) (true, resonantIndex n) (z, p) := by
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
  let S : ParityPair n →L[ℂ] ParityPair n :=
    Ring.inverse (1 - freeResolventComplementaryPotentialOppositeFactor22
      u₁ u₂ hu₁ hu₂ n z hz)
  have hD : actualFreeResolventCenterExtensionV1_30 n z = D :=
    actualFreeResolventCenterExtension_eq_actualV1_30 n z hz
  have hS : Ring.inverse
      (1 - actualComplementaryQVDJointParameterV5_30 n (z, p)) = S := by
    change actualComplementaryQVDJointInverseV5_30 n (z, p) = S
    exact actualComplementaryQVDJointInverse_eq_proofIndexedFormulaV5_30 n z p hz
  have hV :
      actualParityPairPotentialParameterAfterScalarWrapperCLM23 n p = V := by
    dsimp [V, u₁, u₂, hu₁, hu₂]
    exact actualParityPairPotentialParameterAfterScalarWrapperCLM23_apply n p
  have hM : actualSchurEffectiveOperatorAfterDextV3_30 n (z, p) =
      P.comp (V.comp P) + P.comp (V.comp ((D.comp S).comp (V.comp P))) := by
    dsimp [actualSchurEffectiveOperatorAfterDextV3_30]
    rw [hV, hD, hS]
  have heq := actualSchurEffective_equal_diagonal_jointV5_30 R hR n hn hlarge z p hz hp₁ hp₂
  simp only at heq
  unfold actualSchurCoefficientAfterDext31
  change inner ℂ (parityPairVector n (false, resonantIndex n))
      (actualSchurEffectiveOperatorAfterDextV3_30 n (z, p)
        (parityPairVector n (false, resonantIndex n))) =
    inner ℂ (parityPairVector n (true, resonantIndex n))
      (actualSchurEffectiveOperatorAfterDextV3_30 n (z, p)
        (parityPairVector n (true, resonantIndex n)))
  rw [hM]
  exact heq.symm

/-- Real-type factorization of the Schur determinant on the real segment of the
disk: `det = (F - |b|)(F + |b|)` with `F = λ - nπ - Re α_n(λ)`. -/
theorem actualSchurDet38_realType_factor
    (R : ℝ) (hR : 1 ≤ R) (n : ℤ)
    (hthr : actualSchurCenterThresholdConstant38 * R ^ 3 ≤ |(n : ℝ)|)
    (x : ℝ) (hx : (x : ℂ) ∈ spectralDisk n)
    (w : WeightedHilbert (sobolevModeWeight (1 : ℝ))) (hw : ‖w‖ ≤ R) :
    actualSchurDet38 n (w, actualH1Conj38 w) x =
      (((x - Real.pi * n - (actualSchurAlpha38 n (w, actualH1Conj38 w) x).re -
          ‖actualSchurCoefficientAfterDext31 n (true, resonantIndex n) (false, resonantIndex n)
            ((x : ℂ), (w, actualH1Conj38 w))‖) *
        (x - Real.pi * n - (actualSchurAlpha38 n (w, actualH1Conj38 w) x).re +
          ‖actualSchurCoefficientAfterDext31 n (true, resonantIndex n) (false, resonantIndex n)
            ((x : ℂ), (w, actualH1Conj38 w))‖) : ℝ) : ℂ) := by
  obtain ⟨hn, hlarge, -, -⟩ :=
    actualSchurCenterThresholdConstant38_consequences R hR n hthr
  let p : ActualSchurEffectiveH1PairV3_30 := (w, actualH1Conj38 w)
  have hp₂ : ‖p.2‖ ≤ R := by
    change ‖actualH1Conj38 w‖ ≤ R
    rw [actualH1Conj38_norm]; exact hw
  have hdiag := actualSchurCoefficient_equal_diagonal38 R hR n hn hlarge x p hx hw hp₂
  have hc := actualSchurOffDiagonal_star_realType38 R hR n hthr x hx w hw
  have him := actualSchurAlpha38_im_eq_zero_realType38 R hR n hthr x hx w hw
  set α := actualSchurAlpha38 n p x with hα
  set b := actualSchurCoefficientAfterDext31 n (true, resonantIndex n) (false, resonantIndex n)
    ((x : ℂ), p) with hb
  have hαdef : actualSchurCoefficientAfterDext31 n (true, resonantIndex n)
      (true, resonantIndex n) ((x : ℂ), p) = α := rfl
  have hαR : α = ((α.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [him]
  have hbb : b * star b = ((‖b‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  unfold actualSchurDet38
  change (_ - _ - actualSchurCoefficientAfterDext31 n (true, resonantIndex n)
      (true, resonantIndex n) ((x : ℂ), p)) * (_ - _ - actualSchurCoefficientAfterDext31 n
      (false, resonantIndex n) (false, resonantIndex n) ((x : ℂ), p)) - b *
      actualSchurCoefficientAfterDext31 n (false, resonantIndex n) (true, resonantIndex n)
        ((x : ℂ), p) = _
  rw [hdiag, hαdef, hc, hbb]
  have hcR : spectralCenter n = ((Real.pi * n : ℝ) : ℂ) := by
    simp [spectralCenter]; ring
  rw [hcR, hαR]
  push_cast
  simp only [Complex.ofReal_re]
  ring

end NlsGge.Schur
