import NlsGge.Schur.ActualSchurCenterContraction38V1
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Real-type symmetry of the Schur effective matrix

Source: `paper/v2.tex` lines 1105-1106: on the real subspace `(u₁,u₂)=(u,ū)` and
for real `λ`, self-adjointness gives `α_n ∈ ℝ` and `c_n = conj b_n`.

Conventions.  `physicalFourier u k = ∫ e^{-2πikx} u(x)`, so the Fourier
coefficient of `ū` at `k` is `conj (u_{-k})`; `actualH1Conj38` is this map on the
complex `H¹` Fourier carrier, and `physicalH1_conj38` shows it matches the
complex-conjugation `star` on `PhysicalL2` under
`physicalH1ComplexCarrierToL2Actual22`.

Nothing is assumed: self-adjointness of the concrete operators `P`, `Q`, `D(λ)`
(real `λ`), `V(u,ū)` is proved, and the effective operator
`P V P + P V D S V P` with `S = (1 - Q V D)⁻¹` (`Ring.inverse` of the
unit established by the existing contraction estimate) is shown to be
self-adjoint through the intertwining `(1 - D V Q) D = D (1 - Q V D)`.
-/

set_option autoImplicit false
noncomputable section
open scoped InnerProduct InnerProductSpace
open MeasureTheory
open NlsGge.Analysis NlsGge.Pilot

namespace NlsGge.Schur


section Abstract
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem effectiveSelfAdjointAbstract38
    (P Q D V : E →L[ℂ] E)
    (hP : ContinuousLinearMap.adjoint P = P) (hQ : ContinuousLinearMap.adjoint Q = Q)
    (hD : ContinuousLinearMap.adjoint D = D) (hV : ContinuousLinearMap.adjoint V = V)
    (hQD : Q.comp D = D) (hDQ : D.comp Q = D)
    (hunit : IsUnit (1 - Q.comp (V.comp D))) :
    ContinuousLinearMap.adjoint
      (P.comp (V.comp P) +
        P.comp (V.comp ((D.comp (Ring.inverse (1 - Q.comp (V.comp D)))).comp (V.comp P)))) =
      P.comp (V.comp P) +
        P.comp (V.comp ((D.comp (Ring.inverse (1 - Q.comp (V.comp D)))).comp (V.comp P))) := by
  set Y : E →L[ℂ] E := 1 - Q.comp (V.comp D) with hYdef
  set X : E →L[ℂ] E := 1 - D.comp (V.comp Q) with hXdef
  set S : E →L[ℂ] E := Ring.inverse Y with hSdef
  have hSright : Y.comp S = 1 := by
    change Y * Ring.inverse Y = 1
    exact Ring.mul_inverse_cancel Y hunit
  have hY : ContinuousLinearMap.adjoint Y = X := by
    rw [hYdef, hXdef, map_sub, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
      hQ, hV, hD]
    simp [ContinuousLinearMap.comp_assoc, ContinuousLinearMap.adjoint_one]
  have hq : ∀ x, Q (D x) = D x := fun x => by simpa using congrArg (fun T => T x) hQD
  have hd : ∀ x, D (Q x) = D x := fun x => by simpa using congrArg (fun T => T x) hDQ
  have h1 : ∀ y, ContinuousLinearMap.adjoint S (X y) = y := by
    intro y
    have h := congrArg (fun T => T y)
      (congrArg ContinuousLinearMap.adjoint hSright)
    rw [ContinuousLinearMap.adjoint_comp, hY, ContinuousLinearMap.adjoint_one] at h
    simpa using h
  have h2 : ∀ x, Y (S x) = x := fun x => by simpa using congrArg (fun T => T x) hSright
  have h3 : ∀ y, X (D y) = D (Y y) := by
    intro y
    simp [hXdef, hYdef, hq, hd]
  have hshift : (ContinuousLinearMap.adjoint S).comp D = D.comp S := by
    apply ContinuousLinearMap.ext
    intro x
    have : D (S x) = ContinuousLinearMap.adjoint S (D x) := by
      calc D (S x) = ContinuousLinearMap.adjoint S (X (D (S x))) := (h1 _).symm
        _ = ContinuousLinearMap.adjoint S (D (Y (S x))) := by rw [h3]
        _ = _ := by rw [h2]
    exact this.symm
  have hR : ContinuousLinearMap.adjoint (D.comp S) = D.comp S := by
    rw [ContinuousLinearMap.adjoint_comp, hD, hshift]
  generalize D.comp S = R at hR ⊢
  simp only [map_add, ContinuousLinearMap.adjoint_comp, hP, hV, hR,
    ContinuousLinearMap.comp_assoc]

end Abstract


theorem diagonalSquare_adjoint38 {I : Type} (T : SquareSequence I →L[ℂ] SquareSequence I)
    (c : I → ℂ) (hT : ∀ x i, T x i = c i * x i) (hc : ∀ i, star (c i) = c i) :
    ContinuousLinearMap.adjoint T = T := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro i
  rw [hT, hT]
  simp only [RCLike.inner_apply, map_mul]
  have := hc i
  simp only [Complex.star_def] at this
  rw [this]
  ring

theorem transportedAdjoint38 {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace H] [CompleteSpace K]
    (e : H ≃ₗᵢ[ℂ] K) (T : K →L[ℂ] K) (hT : ContinuousLinearMap.adjoint T = T) :
    ContinuousLinearMap.adjoint
      ((e.toContinuousLinearEquiv.symm.toContinuousLinearMap).comp
        (T.comp e.toContinuousLinearEquiv.toContinuousLinearMap)) =
    (e.toContinuousLinearEquiv.symm.toContinuousLinearMap).comp
        (T.comp e.toContinuousLinearEquiv.toContinuousLinearMap) := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  have hT' : ∀ a b, inner ℂ (T a) b = inner ℂ a (T b) := fun a b => by
    have := (ContinuousLinearMap.eq_adjoint_iff T T).mp hT.symm a b
    exact this
  change inner ℂ (e.symm (T (e x))) y = inner ℂ x (e.symm (T (e y)))
  rw [← e.inner_map_map, ← e.inner_map_map x]
  simp only [LinearIsometryEquiv.apply_symm_apply]
  exact hT' _ _


theorem resonantParityPair_adjoint38 (n : ℤ) :
    ContinuousLinearMap.adjoint (resonantParityPair n) = resonantParityPair n := by
  unfold resonantParityPair
  apply transportedAdjoint38 (parityPairRepr n) (resonantSquare n)
  refine diagonalSquare_adjoint38 _ (fun i => if i.2 = resonantIndex n then 1 else 0) ?_ ?_
  · intro x i
    rw [resonantSquare_apply]
    split_ifs <;> simp
  · intro i
    split_ifs <;> simp

theorem complementaryProjectionTransported_adjoint38 (n : ℤ) :
    ContinuousLinearMap.adjoint (freeResolventComplementaryProjectionTransported n) =
      freeResolventComplementaryProjectionTransported n := by
  unfold freeResolventComplementaryProjectionTransported
  apply transportedAdjoint38 (parityPairRepr n) (complementarySquare n)
  refine diagonalSquare_adjoint38 _ (fun i => if i.2 = resonantIndex n then 0 else 1) ?_ ?_
  · intro x i
    rw [complementarySquare_apply]
    split_ifs <;> simp
  · intro i
    split_ifs <;> simp

theorem freeResolventCoeff_star_real38 (n : ℤ) (x : ℝ) (m : Sector n) :
    star (freeResolventCoeff n (x : ℂ) m) = freeResolventCoeff n (x : ℂ) m := by
  unfold freeResolventCoeff
  split_ifs
  · simp
  · have : (x : ℂ) - spectralCenter m.val = ((x - (m.val : ℝ) * Real.pi : ℝ) : ℂ) := by
      simp [spectralCenter]
    rw [this, ← Complex.ofReal_inv]
    exact Complex.conj_ofReal _

theorem freeResolventParityPair_adjoint_real38 (n : ℤ) (x : ℝ)
    (hx : (x : ℂ) ∈ spectralDisk n) :
    ContinuousLinearMap.adjoint (freeResolventParityPair n (x : ℂ) hx) =
      freeResolventParityPair n (x : ℂ) hx := by
  unfold freeResolventParityPair
  apply transportedAdjoint38 (parityPairRepr n) (freeResolventSquare n (x : ℂ) hx)
  exact diagonalSquare_adjoint38 _ (fun i => freeResolventCoeff n (x : ℂ) i.2)
    (fun y i => freeResolventSquare_apply n (x : ℂ) hx y i)
    (fun i => freeResolventCoeff_star_real38 n x i.2)



theorem sobolevModeWeight_neg38 (r : ℝ) (k : ℤ) :
    sobolevModeWeight r (-k) = sobolevModeWeight r k := by
  unfold sobolevModeWeight japaneseBracket
  simp

/-- The conjugation `u ↦ ū` on the complex `H¹` Fourier carrier: the Fourier
coefficient of `ū` at `k` is `conj (u_{-k})`. -/
def actualH1Conj38 (x : WeightedHilbert (sobolevModeWeight (1 : ℝ))) :
    WeightedHilbert (sobolevModeWeight (1 : ℝ)) :=
  ⟨fun k => star ((x : ℤ → ℂ) (-k)), by
    change Memℓp (weightedCoordinates (sobolevModeWeight (1 : ℝ))
      (fun k => star ((x : ℤ → ℂ) (-k)))) 2
    rw [weightedCoordinates_mem_l2_iff _
      (fun n => ((sobolevModeWeightPositive 1).out n).le)]
    have hs := (weightedHilbert_hasSum (sobolevModeWeight (1 : ℝ)) x).summable
    have h2 := (Equiv.neg ℤ).summable_iff.mpr hs
    refine h2.congr (fun k => ?_)
    simp [Function.comp, sobolevModeWeight_neg38]⟩

@[simp] theorem actualH1Conj38_apply (x : WeightedHilbert (sobolevModeWeight (1 : ℝ))) (k : ℤ) :
    (actualH1Conj38 x : ℤ → ℂ) k = star ((x : ℤ → ℂ) (-k)) := rfl

theorem actualH1Conj38_norm (x : WeightedHilbert (sobolevModeWeight (1 : ℝ))) :
    ‖actualH1Conj38 x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [weightedHilbert_norm_sq, weightedHilbert_norm_sq]
  rw [← (Equiv.neg ℤ).tsum_eq (fun n : ℤ => sobolevModeWeight (1 : ℝ) n * ‖(x : ℤ → ℂ) n‖ ^ 2)]
  apply tsum_congr
  intro k
  simp [sobolevModeWeight_neg38]

theorem physicalFourier_star38 (u : PhysicalL2) (k : ℤ) :
    physicalFourier (star u : PhysicalL2) k = star (physicalFourier u (-k)) := by
  unfold physicalFourier fourierCoeff
  have h1 : ∫ t, (fourier (-k) t) • (star u : PhysicalL2) t ∂AddCircle.haarAddCircle
      = ∫ t, (fourier (-k) t) • star (u t) ∂AddCircle.haarAddCircle := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_star u] with t ht
    rw [ht]
    rfl
  rw [h1, neg_neg, Complex.star_def, ← integral_conj]
  apply integral_congr_ae
  filter_upwards with t
  rw [fourier_neg, smul_eq_mul, smul_eq_mul]
  simp

theorem physicalH1_conj38 (x : WeightedHilbert (sobolevModeWeight (1 : ℝ))) :
    physicalH1ComplexCarrierToL2Actual22 (actualH1Conj38 x) =
      star (physicalH1ComplexCarrierToL2Actual22 x) := by
  apply physicalFourierL2.injective
  apply lp.ext
  funext k
  rw [physicalFourierL2_apply, physicalFourierL2_apply, physicalFourier_star38,
    physicalH1ComplexCarrierToL2Actual22_fourier, physicalH1ComplexCarrierToL2Actual22_fourier]
  rfl


theorem naturalPhysicalCoverH1Bounded_star38 (u v : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u))
    (hv : SobolevSquareSummable 1 (physicalFourier v)) (h : v = star u) :
    (naturalPhysicalCoverH1Bounded v hv : SpectralCircle → ℂ) =ᵐ[spectralHaar]
      fun x => star (naturalPhysicalCoverH1Bounded u hu x) := by
  subst h
  have h1 := naturalPhysicalCoverH1Bounded_ae (star u) hv
  have h2 := naturalPhysicalCoverH1Bounded_ae u hu
  have h3 := naturalPhysicalCover_preserving.quasiMeasurePreserving.ae_eq_comp
    (Lp.coeFn_star u)
  filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
  rw [hx1, hx2]
  exact hx3

theorem coveredH1SpectralMultiplier_inner_star38 (u v : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u))
    (hv : SobolevSquareSummable 1 (physicalFourier v)) (h : v = star u)
    (f g : SpectralScalarL2) :
    inner ℂ (coveredH1SpectralMultiplier v hv f) g =
      inner ℂ f (coveredH1SpectralMultiplier u hu g) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coveredH1SpectralMultiplier_ae v hv f, coveredH1SpectralMultiplier_ae u hu g,
    naturalPhysicalCoverH1Bounded_star38 u v hu hv h] with x hf hg ha
  rw [hf, hg, ha]
  simp only [RCLike.inner_apply, map_mul, Complex.star_def, Complex.conj_conj]
  ring

theorem coveredH1ParityPairPotential_adjoint_of_star38 (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂)) (h : u₂ = star u₁) (n : ℤ) :
    ContinuousLinearMap.adjoint (coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n) =
      coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  have h' : u₁ = star u₂ := by rw [h, star_star]
  rw [PiLp.inner_apply, PiLp.inner_apply, Fintype.sum_bool, Fintype.sum_bool]
  simp only [coveredH1ParityPairPotential_apply_true, coveredH1ParityPairPotential_apply_false,
    Submodule.coe_inner]
  have e1 := coveredH1SpectralMultiplier_inner_star38 u₂ u₁ hu₂ hu₁ h'
    (x false).val (y true).val
  have e2 := coveredH1SpectralMultiplier_inner_star38 u₁ u₂ hu₁ hu₂ h
    (x true).val (y false).val
  rw [coveredH1ScalarParityMultiplier_coe_apply, coveredH1ScalarParityMultiplier_coe_apply,
    coveredH1ScalarParityMultiplier_coe_apply, coveredH1ScalarParityMultiplier_coe_apply, e1, e2,
    add_comm]


set_option maxRecDepth 4096 in
/-- The concrete effective Schur operator is self-adjoint on the real-type
potential pair `(w, conj w)` at real spectral parameter in the spectral disk. -/
theorem actualSchurEffectiveOperator_selfAdjoint_realType38
    (R : ℝ) (hR : 1 ≤ R) (n : ℤ)
    (hthr : actualSchurCenterThresholdConstant38 * R ^ 3 ≤ |(n : ℝ)|)
    (x : ℝ) (hx : (x : ℂ) ∈ spectralDisk n)
    (w : WeightedHilbert (sobolevModeWeight (1 : ℝ))) (hw : ‖w‖ ≤ R) :
    ContinuousLinearMap.adjoint
      (actualSchurEffectiveOperatorAfterDextV3_30 n ((x : ℂ), (w, actualH1Conj38 w))) =
    actualSchurEffectiveOperatorAfterDextV3_30 n ((x : ℂ), (w, actualH1Conj38 w)) := by
  obtain ⟨hn, hlarge, -, -⟩ :=
    actualSchurCenterThresholdConstant38_consequences R hR n hthr
  have hw' : ‖actualH1Conj38 w‖ ≤ R := by rw [actualH1Conj38_norm]; exact hw
  have hDe : actualFreeResolventCenterExtensionV1_30 n (x : ℂ) =
      freeResolventParityPair n (x : ℂ) hx :=
    actualFreeResolventCenterExtension_eq_actualV1_30 n (x : ℂ) hx
  have hVe : actualParityPairPotentialParameterAfterScalarWrapperCLM23 n (w, actualH1Conj38 w) =
      coveredH1ParityPairPotential
        (physicalH1ComplexCarrierToL2Actual22 w)
        (physicalH1ComplexCarrierToL2Actual22 (actualH1Conj38 w))
        (physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable w)
        (physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable (actualH1Conj38 w)) n :=
    actualParityPairPotentialParameterAfterScalarWrapperCLM23_apply n (w, actualH1Conj38 w)
  have hunit := actualComplementaryQVDJointOneSubIsUnitV5_30 R hR n hn hlarge (x : ℂ)
    (w, actualH1Conj38 w) hx hw hw'
  have hDad : ContinuousLinearMap.adjoint (actualFreeResolventCenterExtensionV1_30 n (x : ℂ)) =
      actualFreeResolventCenterExtensionV1_30 n (x : ℂ) := by
    rw [hDe]; exact freeResolventParityPair_adjoint_real38 n x hx
  have hVad : ContinuousLinearMap.adjoint
      (actualParityPairPotentialParameterAfterScalarWrapperCLM23 n (w, actualH1Conj38 w)) =
      actualParityPairPotentialParameterAfterScalarWrapperCLM23 n (w, actualH1Conj38 w) := by
    rw [hVe]
    exact coveredH1ParityPairPotential_adjoint_of_star38 _ _ _ _
      (physicalH1_conj38 w) n
  have hQD : (freeResolventComplementaryProjectionTransported n).comp
      (actualFreeResolventCenterExtensionV1_30 n (x : ℂ)) =
      actualFreeResolventCenterExtensionV1_30 n (x : ℂ) := by
    rw [hDe]; exact freeResolventParityPair_comp_complementaryProjection_afterCoordinateRange n _ hx
  have hDQ : (actualFreeResolventCenterExtensionV1_30 n (x : ℂ)).comp
      (freeResolventComplementaryProjectionTransported n) =
      actualFreeResolventCenterExtensionV1_30 n (x : ℂ) := by
    rw [hDe]
    exact freeResolventParityPair_comp_complementaryProjection_right_afterCoordinateRange n _ hx
  exact effectiveSelfAdjointAbstract38 (resonantParityPair n)
    (freeResolventComplementaryProjectionTransported n)
    (actualFreeResolventCenterExtensionV1_30 n (x : ℂ))
    (actualParityPairPotentialParameterAfterScalarWrapperCLM23 n (w, actualH1Conj38 w))
    (resonantParityPair_adjoint38 n) (complementaryProjectionTransported_adjoint38 n)
    hDad hVad hQD hDQ hunit

/-- Hermitian symmetry of every matrix entry of a self-adjoint operator. -/
theorem actualSchurCoefficient_star_of_selfAdjoint38 (n : ℤ)
    (z : ℂ) (p : ActualSchurEffectiveH1PairV3_30)
    (hA : ContinuousLinearMap.adjoint (actualSchurEffectiveOperatorAfterDextV3_30 n (z, p)) =
      actualSchurEffectiveOperatorAfterDextV3_30 n (z, p))
    (i j : Bool × Sector n) :
    actualSchurCoefficientAfterDext31 n i j (z, p) =
      star (actualSchurCoefficientAfterDext31 n j i (z, p)) := by
  have e1 : actualSchurCoefficientAfterDext31 n i j (z, p) =
      inner ℂ (parityPairVector n i)
        (actualSchurEffectiveOperatorAfterDextV3_30 n (z, p) (parityPairVector n j)) := rfl
  have e2 : actualSchurCoefficientAfterDext31 n j i (z, p) =
      inner ℂ (parityPairVector n j)
        (actualSchurEffectiveOperatorAfterDextV3_30 n (z, p) (parityPairVector n i)) := rfl
  rw [e1, e2]
  set A := actualSchurEffectiveOperatorAfterDextV3_30 n (z, p) with hAdef
  conv_lhs => rw [← hA]
  rw [ContinuousLinearMap.adjoint_inner_right, Complex.star_def]
  exact (inner_conj_symm (𝕜 := ℂ) _ _).symm

/-- The diagonal Schur coefficient `α_n` is real on the real-type subspace. -/
theorem actualSchurAlpha38_im_eq_zero_realType38
    (R : ℝ) (hR : 1 ≤ R) (n : ℤ)
    (hthr : actualSchurCenterThresholdConstant38 * R ^ 3 ≤ |(n : ℝ)|)
    (x : ℝ) (hx : (x : ℂ) ∈ spectralDisk n)
    (w : WeightedHilbert (sobolevModeWeight (1 : ℝ))) (hw : ‖w‖ ≤ R) :
    (actualSchurAlpha38 n (w, actualH1Conj38 w) (x : ℂ)).im = 0 := by
  have h := actualSchurCoefficient_star_of_selfAdjoint38 n (x : ℂ) (w, actualH1Conj38 w)
    (actualSchurEffectiveOperator_selfAdjoint_realType38 R hR n hthr x hx w hw)
    (true, resonantIndex n) (true, resonantIndex n)
  change actualSchurCoefficientAfterDext31 n (true, resonantIndex n) (true, resonantIndex n)
    ((x : ℂ), (w, actualH1Conj38 w)) = _ at h
  have h' : (starRingEnd ℂ)
      (actualSchurAlpha38 n (w, actualH1Conj38 w) (x : ℂ)) =
      actualSchurAlpha38 n (w, actualH1Conj38 w) (x : ℂ) := h.symm
  exact Complex.conj_eq_iff_im.mp h'

/-- The off-diagonal Schur coefficients satisfy `c_n = conj b_n` on the
real-type subspace (`b_n` is the `(true,false)` entry in source order, `c_n`
the `(false,true)` entry). -/
theorem actualSchurOffDiagonal_star_realType38
    (R : ℝ) (hR : 1 ≤ R) (n : ℤ)
    (hthr : actualSchurCenterThresholdConstant38 * R ^ 3 ≤ |(n : ℝ)|)
    (x : ℝ) (hx : (x : ℂ) ∈ spectralDisk n)
    (w : WeightedHilbert (sobolevModeWeight (1 : ℝ))) (hw : ‖w‖ ≤ R) :
    actualSchurCoefficientAfterDext31 n (false, resonantIndex n) (true, resonantIndex n)
        ((x : ℂ), (w, actualH1Conj38 w)) =
      star (actualSchurCoefficientAfterDext31 n (true, resonantIndex n) (false, resonantIndex n)
        ((x : ℂ), (w, actualH1Conj38 w))) :=
  actualSchurCoefficient_star_of_selfAdjoint38 n (x : ℂ) (w, actualH1Conj38 w)
    (actualSchurEffectiveOperator_selfAdjoint_realType38 R hR n hthr x hx w hw) _ _

end NlsGge.Schur
