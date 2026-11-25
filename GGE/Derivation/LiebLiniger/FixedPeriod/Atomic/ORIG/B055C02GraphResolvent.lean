import NlsGge.Schur.ActualSchurFGboundAfterResolventFactorizationV5_31
import NlsGge.Schur.ActualSchurEffectiveDerivativeSupportV1_32
import NlsGge.Schur.ActualSchurElimination38V1
import NlsGge.Schur.SourcePhysicalFreeResolventRealizationV1

/-! ORIGINAL record NEW-F03, clause B055.C02 (paper/v2.tex 1085-1090, `F:eq:Rn`).

The helper `sourceFreeDiracGraphB055C02` and the headline
`actualSchurComplementaryGraphResolventB055C02` are the independently reviewed
(SOL-STMTB055-20261111, APPROVABLE_AS_STATED) frozen commands of
`AuthOrig-20261111/STATEMENTS_B055C02.md`, copied byte-for-byte from the elaborated
probe `probe-AllSAOrigB055C02Probe.lean`.

New supporting results (all proved here, no hypothesis beyond the stated ones):
* (i) `sourceFreeDiracGraphB055C02_coord`, `sourceFreeDiracGraphB055C02_domain`,
  `sourceFreeDiracGraphB055C02_of_domain`: graph/domain/action identification
  (`g(b,m) = mπ y(b,m)` in both reflected channels, zero modes retained);
* (ii) `actualSchurGraphRightInverseB055C02`, `actualSchurGraphLeftInverseB055C02`:
  the inhomogeneous perturbed inverse equations on the actual graph domain;
* (iii) `actualSchurResolventFamily_analyticOnNhdB055C02`: joint analyticity of `Dext ∘ S`;
* (iv) `actualSchurUnitsB055C02`, `actualSchurFactorizationsB055C02`,
  `actualSchurResolventZeroExtensionB055C02`: both units, both factorizations, the
  V5_31 binding and both `P` annihilations. -/

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur
open NlsGge.Analysis NlsGge.Pilot

/-- Graph of the actual source free Dirac operator `L₀ = diag(-i∂ₓ, i∂ₓ)` (reflected
convention F:eq:Dirac) with the twisted boundary condition `f(1) = (-1)^n f(0)`:
`(y, g)` lies in the graph iff, in each source channel, the actual L²(0,1] component
of `y` has the actual twisted weak derivative `(if upper then i else -i) • g_upper`,
i.e. `-i y₊' = g₊` and `i y₋' = g₋`. -/
def sourceFreeDiracGraphB055C02 (n : ℤ) (y g : SectorSquare n) : Prop :=
  ∀ upper : Bool, SourceTwistedWeakDerivative n (sourceCoordinateComponent n y upper)
    ((if upper then Complex.I else -Complex.I) • sourceCoordinateComponent n g upper)

/-! ### (i) Graph/domain/action identification -/

lemma sourceScalarCoefficient_smul_applyB055C02 (n : ℤ) (c : ℂ) (F : SourceIntervalL2)
    (m : Sector n) :
    sourceScalarCoefficient n (c • F) m = c * sourceScalarCoefficient n F m := by
  unfold sourceScalarCoefficient
  rw [map_smul, map_smul]
  rfl

/-- The actual weak-derivative graph forces `g(b,m) = mπ · y(b,m)` in both reflected
channels, for every sector index (zero mode included). -/
theorem sourceFreeDiracGraphB055C02_coord (n : ℤ) (y g : SectorSquare n)
    (h : sourceFreeDiracGraphB055C02 n y g) (i : Bool × Sector n) :
    g i = spectralCenter i.2.val * y i := by
  obtain ⟨b, m⟩ := i
  have hw := sourceTwistedWeakDerivative_fourier_coefficients n _ _ (h b) (mixedIndex n (b, m))
  rw [sourceScalarCoefficient_smul_applyB055C02, sourceCoordinateComponent_scalarCoefficient,
    sourceCoordinateComponent_scalarCoefficient] at hw
  cases b
  · have hc : spectralCenter (mixedIndex n (false, m)).val = -spectralCenter m.val := by
      simp only [mixedIndex, Bool.false_eq_true, if_false, negateIndex_val,
        spectralCenter_neg_identity]
    rw [hc] at hw
    simp only [Bool.false_eq_true, if_false] at hw
    linear_combination Complex.I * hw +
      (g (false, m) - spectralCenter m.val * y (false, m)) * Complex.I_mul_I
  · have hc : (mixedIndex n (true, m)) = m := by
      simp only [mixedIndex, if_true]
    rw [hc] at hw
    simp only [if_true] at hw
    linear_combination (-Complex.I) * hw +
      (g (true, m) - spectralCenter m.val * y (true, m)) * Complex.I_mul_I

/-- Graph membership puts `y` in the actual free domain and identifies `g` as the
free coordinate Dirac action on `y`. -/
theorem sourceFreeDiracGraphB055C02_domain (n : ℤ) (y g : SectorSquare n)
    (h : sourceFreeDiracGraphB055C02 n y g) :
    ∃ hy : y ∈ freeWeightedDomainPointwise n, freeCoordinateDirac n ⟨y, hy⟩ = g := by
  have he : freeWeightedCoordinates n y = (g : Bool × Sector n → ℂ) := by
    funext i
    exact (sourceFreeDiracGraphB055C02_coord n y g h i).symm
  have hy : y ∈ freeWeightedDomainPointwise n := by
    change Memℓp (freeWeightedCoordinates n y) 2
    rw [he]
    exact lp.memℓp g
  refine ⟨hy, ?_⟩
  apply lp.ext
  exact he

/-- Conversely every free-domain vector is in the graph with its free Dirac action. -/
theorem sourceFreeDiracGraphB055C02_of_domain (n : ℤ) (y : SectorSquare n)
    (hy : y ∈ freeWeightedDomainPointwise n) :
    sourceFreeDiracGraphB055C02 n y (freeCoordinateDirac n ⟨y, hy⟩) := by
  intro upper
  exact sourceFreeDomain_has_twisted_weak_derivative n y hy upper

/-! ### Transport helpers -/

lemma toSq_zeroB055C02 (n : ℤ) :
    actualSchurEndomorphismToSquareV5_30 n (0 : ParityPair n →L[ℂ] ParityPair n) = 0 := by
  ext x : 1
  simp [toSq_apply38]

lemma toSq_injectiveB055C02 (n : ℤ) {A B : ParityPair n →L[ℂ] ParityPair n}
    (h : actualSchurEndomorphismToSquareV5_30 n A = actualSchurEndomorphismToSquareV5_30 n B) :
    A = B := by
  ext1 f
  have hf := congrArg
    (fun T : SectorSquare n →L[ℂ] SectorSquare n =>
      (parityPairRepr n).symm (T (parityPairRepr n f))) h
  simpa [toSq_apply38] using hf

lemma resonant_comp_freeResolventParityPairB055C02 (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n) :
    (resonantParityPair n).comp (freeResolventParityPair n z hz) = 0 := by
  apply toSq_injectiveB055C02
  rw [toSq_comp38, toSq_resonant38, toSq_freeResolvent38, toSq_zeroB055C02]
  exact freeResolventSquare_resonant_left n z hz

lemma freeResolventParityPair_comp_resonantB055C02 (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n) :
    (freeResolventParityPair n z hz).comp (resonantParityPair n) = 0 := by
  apply toSq_injectiveB055C02
  rw [toSq_comp38, toSq_resonant38, toSq_freeResolvent38, toSq_zeroB055C02]
  exact freeResolventSquare_resonant_right n z hz

lemma jointParameter_eqB055C02 (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n)
    (p : ActualH1PairJointSchurV5_30) :
    actualComplementaryQVDJointParameterV5_30 n (z, p) =
      (freeResolventComplementaryProjectionTransported n).comp
        ((actualParityPairPotentialParameterAfterScalarWrapperCLM23 n p).comp
          (freeResolventParityPair n z hz)) := by
  dsimp [actualComplementaryQVDJointParameterV5_30]
  rw [actualFreeResolventCenterExtension_eq_actualV1_30 n z hz]

lemma resolventFamily_eqB055C02 (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n)
    (p : ActualH1PairJointSchurV5_30) :
    actualSchurResolventFamilyAfterDextV3_32 n p z =
      (freeResolventParityPair n z hz).comp
        (Ring.inverse (1 - (freeResolventComplementaryProjectionTransported n).comp
          ((actualParityPairPotentialParameterAfterScalarWrapperCLM23 n p).comp
            (freeResolventParityPair n z hz)))) := by
  show (actualFreeResolventCenterExtensionV1_30 n z).comp
      (Ring.inverse (1 - actualComplementaryQVDJointParameterV5_30 n (z, p))) = _
  rw [actualFreeResolventCenterExtension_eq_actualV1_30 n z hz, jointParameter_eqB055C02 n z hz p]

/-! ### (iv) Units, factorizations, binding, zero extension -/

section Pointwise

variable (R : ℝ) (hR : 1 ≤ R) (n : ℤ) (hn : 1 ≤ |(n : ℝ)|)
    (hlarge : 4 * freeResolventSchurUniformConstant *
      physicalH1MultiplierConstant * R ^ 2 ≤ |(n : ℝ)|)
    (z : ℂ) (hz : z ∈ spectralDisk n) (p : ActualH1PairJointSchurV5_30)
    (hp₁ : ‖p.1‖ ≤ R) (hp₂ : ‖p.2‖ ≤ R)

include hR hn hlarge hz hp₁ hp₂ in
theorem actualSchurUnitsB055C02 :
    IsUnit (1 - (freeResolventComplementaryProjectionTransported n).comp
        ((actualParityPairPotentialParameterAfterScalarWrapperCLM23 n p).comp
          (freeResolventParityPair n z hz))) ∧
    IsUnit (1 - (freeResolventParityPair n z hz).comp
        ((actualParityPairPotentialParameterAfterScalarWrapperCLM23 n p).comp
          (freeResolventComplementaryProjectionTransported n))) := by
  constructor
  · have h := actualComplementaryQVDJointOneSubIsUnitV5_30 R hR n hn hlarge z p hz hp₁ hp₂
    rwa [jointParameter_eqB055C02 n z hz p] at h
  · have hball₁ : ‖physicalSobolevL2 1 (physicalH1ComplexCarrierToL2Actual22 p.1)
        (physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.1)‖ ≤ R := by
      rw [actualPhysicalH1Carrier_sobolev_normAfterScalar23]
      exact hp₁
    have hball₂ : ‖physicalSobolevL2 1 (physicalH1ComplexCarrierToL2Actual22 p.2)
        (physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.2)‖ ≤ R := by
      rw [actualPhysicalH1Carrier_sobolev_normAfterScalar23]
      exact hp₂
    have hsquare := freeResolventComplementaryPotentialA_square_norm_le_half
      _ _ _ _ R hR hball₁ hball₂ n hn z hz hlarge
    rw [actualParityPairPotentialParameterAfterScalarWrapperCLM23_apply]
    exact continuousLinearMap_one_sub_isUnit_of_square_norm_lt_one23 _
      (lt_of_le_of_lt hsquare (by norm_num))

include hR hn hlarge hz hp₁ hp₂ in
theorem actualSchurFactorizationsB055C02 :
    actualSchurResolventFamilyAfterDextV3_32 n p z = actualSchurResolventFactorizedV5_31 n z p hz ∧
    actualSchurResolventFamilyAfterDextV3_32 n p z =
      (freeResolventParityPair n z hz).comp
        (Ring.inverse (1 - (freeResolventComplementaryProjectionTransported n).comp
          ((actualParityPairPotentialParameterAfterScalarWrapperCLM23 n p).comp
            (freeResolventParityPair n z hz)))) ∧
    actualSchurResolventFamilyAfterDextV3_32 n p z =
      (Ring.inverse (1 - (freeResolventParityPair n z hz).comp
          ((actualParityPairPotentialParameterAfterScalarWrapperCLM23 n p).comp
            (freeResolventComplementaryProjectionTransported n)))).comp
        (freeResolventParityPair n z hz) := by
  set D : ParityPair n →L[ℂ] ParityPair n := freeResolventParityPair n z hz with hD
  set V : ParityPair n →L[ℂ] ParityPair n :=
    actualParityPairPotentialParameterAfterScalarWrapperCLM23 n p with hV
  set Q : ParityPair n →L[ℂ] ParityPair n :=
    freeResolventComplementaryProjectionTransported n with hQ
  obtain ⟨hunitB, hunitA⟩ := actualSchurUnitsB055C02 R hR n hn hlarge z hz p hp₁ hp₂
  have hfirst := resolventFamily_eqB055C02 n z hz p
  refine ⟨?_, hfirst, ?_⟩
  · show (actualFreeResolventCenterExtensionV1_30 n z).comp
        (actualComplementaryQVDJointInverseV5_30 n (z, p)) = _
    rw [actualFreeResolventCenterExtension_eq_actualV1_30 n z hz]
    rfl
  · let Sleft : ParityPair n →L[ℂ] ParityPair n := Ring.inverse (1 - D.comp (V.comp Q))
    let Sright : ParityPair n →L[ℂ] ParityPair n := Ring.inverse (1 - Q.comp (V.comp D))
    have hleft : Sleft.comp (1 - D.comp (V.comp Q)) = 1 := by
      simpa only [Sleft, ContinuousLinearMap.mul_def] using
        Ring.inverse_mul_cancel (1 - D.comp (V.comp Q)) hunitA
    have hright : (1 - D.comp (V.comp Q)).comp Sleft = 1 := by
      simpa only [Sleft, ContinuousLinearMap.mul_def] using
        Ring.mul_inverse_cancel (1 - D.comp (V.comp Q)) hunitA
    have hSrightLeft : Sright.comp (1 - Q.comp (V.comp D)) = 1 := by
      simpa only [Sright, ContinuousLinearMap.mul_def] using
        Ring.inverse_mul_cancel (1 - Q.comp (V.comp D)) hunitB
    have hSrightRight : (1 - Q.comp (V.comp D)).comp Sright = 1 := by
      simpa only [Sright, ContinuousLinearMap.mul_def] using
        Ring.mul_inverse_cancel (1 - Q.comp (V.comp D)) hunitB
    have hQD : Q.comp D = D :=
      freeResolventParityPair_comp_complementaryProjection_afterCoordinateRange n z hz
    have hDQ : D.comp Q = D :=
      freeResolventParityPair_comp_complementaryProjection_right_afterCoordinateRange n z hz
    have hcanonical := freeResolventSchurCanonicalFormula_afterMonoid_actual22
      D V Q Sleft Sleft Sright Sright hQD hDQ
      hleft hright hleft hright hSrightLeft hSrightRight hSrightLeft hSrightRight
    rw [hfirst]
    exact hcanonical.1.symm

include hR hn hlarge hz hp₁ hp₂ in
theorem actualSchurResolventZeroExtensionB055C02 :
    (actualSchurResolventFamilyAfterDextV3_32 n p z).comp (resonantParityPair n) = 0 ∧
    (resonantParityPair n).comp (actualSchurResolventFamilyAfterDextV3_32 n p z) = 0 := by
  obtain ⟨-, hB3, hB4⟩ := actualSchurFactorizationsB055C02 R hR n hn hlarge z hz p hp₁ hp₂
  constructor
  · rw [hB4, ContinuousLinearMap.comp_assoc, freeResolventParityPair_comp_resonantB055C02,
      ContinuousLinearMap.comp_zero]
  · rw [hB3, ← ContinuousLinearMap.comp_assoc, resonant_comp_freeResolventParityPairB055C02,
      ContinuousLinearMap.zero_comp]

/-! ### (ii) Inhomogeneous inverse equations on the actual graph domain -/

include hR hn hlarge hz hp₁ hp₂ in
lemma actualSchurTransportedInverseB055C02 :
    actualSchurEndomorphismToSquareV5_30 n (actualSchurResolventFamilyAfterDextV3_32 n p z) =
      (freeResolventSquare n z hz).comp
        (actualSchurEndomorphismToSquareV5_30 n (actualComplementaryQVDJointInverseV5_30 n (z, p))) ∧
    ((1 : SectorSquare n →L[ℂ] SectorSquare n) -
      (complementarySquare n).comp
        ((actualSchurCoordinatePotential38 n p).comp (freeResolventSquare n z hz))).comp
      (actualSchurEndomorphismToSquareV5_30 n (actualComplementaryQVDJointInverseV5_30 n (z, p))) = 1 ∧
    (actualSchurEndomorphismToSquareV5_30 n (actualComplementaryQVDJointInverseV5_30 n (z, p))).comp
      ((1 : SectorSquare n →L[ℂ] SectorSquare n) -
      (complementarySquare n).comp
        ((actualSchurCoordinatePotential38 n p).comp (freeResolventSquare n z hz))) = 1 := by
  have htwo := actualComplementaryQVDJointInverseV5_30_twoSided
    R hR n hn hlarge z p hz hp₁ hp₂
  rw [jointParameter_eqB055C02 n z hz p] at htwo
  obtain ⟨htwo1, htwo2⟩ := htwo
  refine ⟨?_, ?_, ?_⟩
  · show actualSchurEndomorphismToSquareV5_30 n ((actualFreeResolventCenterExtensionV1_30 n z).comp
        (actualComplementaryQVDJointInverseV5_30 n (z, p))) = _
    rw [actualFreeResolventCenterExtension_eq_actualV1_30 n z hz, toSq_comp38, toSq_freeResolvent38]
  · have h := congrArg (actualSchurEndomorphismToSquareV5_30 n) htwo2
    rw [toSq_comp38, toSq_sub38, toSq_one38, toSq_comp38, toSq_comp38, toSq_complementary38,
      toSq_freeResolvent38] at h
    exact h
  · have h := congrArg (actualSchurEndomorphismToSquareV5_30 n) htwo1
    rw [toSq_comp38, toSq_sub38, toSq_one38, toSq_comp38, toSq_comp38, toSq_complementary38,
      toSq_freeResolvent38] at h
    exact h

include hR hn hlarge hz hp₁ hp₂ in
/-- Right inverse: `𝖱_n x` is in the complementary actual graph domain and
`(λ - Q(𝖫₀ + 𝒱)Q) 𝖱_n x = Q x`. -/
theorem actualSchurGraphRightInverseB055C02 (x : SectorSquare n) :
    resonantSquare n (actualSchurEndomorphismToSquareV5_30 n
        (actualSchurResolventFamilyAfterDextV3_32 n p z) x) = 0 ∧
    ∃ g : SectorSquare n, sourceFreeDiracGraphB055C02 n (actualSchurEndomorphismToSquareV5_30 n
        (actualSchurResolventFamilyAfterDextV3_32 n p z) x) g ∧
      z • actualSchurEndomorphismToSquareV5_30 n
          (actualSchurResolventFamilyAfterDextV3_32 n p z) x -
        complementarySquare n g -
        complementarySquare n (actualSchurCoordinatePotential38 n p
          (actualSchurEndomorphismToSquareV5_30 n
            (actualSchurResolventFamilyAfterDextV3_32 n p z) x)) =
      complementarySquare n x := by
  obtain ⟨hRs, hS1, -⟩ := actualSchurTransportedInverseB055C02 R hR n hn hlarge z hz p hp₁ hp₂
  rw [hRs]
  set Ssq := actualSchurEndomorphismToSquareV5_30 n
    (actualComplementaryQVDJointInverseV5_30 n (z, p)) with hSsq
  set Vs := actualSchurCoordinatePotential38 n p with hVs
  set Dsq := freeResolventSquare n z hz with hDsq
  set Qsq := complementarySquare n with hQsq
  set w : SectorSquare n := Ssq x with hw
  have hy := freeResolventSquare_mem_freeWeightedDomain n z hz w
  have hrinv := freeShiftedCoordinateDirac_right_inverse_complement n z hz w
  have hshift : z • Dsq w - freeCoordinateDirac n ⟨Dsq w, hy⟩ = Qsq w := by
    rw [← hrinv]
    rfl
  have hQy : Qsq (Dsq w) = Dsq w := complementarySquare_freeResolventSquare38 n z hz w
  have hx : x = ((1 : SectorSquare n →L[ℂ] SectorSquare n) - Qsq.comp (Vs.comp Dsq)) w := by
    have h := congrArg (fun T : SectorSquare n →L[ℂ] SectorSquare n => T x) hS1
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] using h.symm
  refine ⟨freeResolventSquare_resonant38 n z hz w, freeCoordinateDirac n ⟨Dsq w, hy⟩,
    sourceFreeDiracGraphB055C02_of_domain n (Dsq w) hy, ?_⟩
  show z • Dsq w - Qsq (freeCoordinateDirac n ⟨Dsq w, hy⟩) - Qsq (Vs (Dsq w)) = Qsq x
  have hlhs : z • Dsq w - Qsq (freeCoordinateDirac n ⟨Dsq w, hy⟩) =
      Qsq (z • Dsq w - freeCoordinateDirac n ⟨Dsq w, hy⟩) := by
    rw [map_sub, map_smul, hQy]
  rw [hlhs, hshift, hx]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.comp_apply, map_sub, hQsq, complementarySquare_idem38]

include hR hn hlarge hz hp₁ hp₂ in
/-- Left inverse on the complementary actual graph domain:
`𝖱_n (λ - Q(𝖫₀ + 𝒱)Q) y = y`. -/
theorem actualSchurGraphLeftInverseB055C02 (y g : SectorSquare n)
    (hPy : resonantSquare n y = 0) (hgraph : sourceFreeDiracGraphB055C02 n y g) :
    actualSchurEndomorphismToSquareV5_30 n (actualSchurResolventFamilyAfterDextV3_32 n p z)
      (z • y - complementarySquare n g -
        complementarySquare n (actualSchurCoordinatePotential38 n p y)) = y := by
  obtain ⟨hRs, -, hS2⟩ := actualSchurTransportedInverseB055C02 R hR n hn hlarge z hz p hp₁ hp₂
  obtain ⟨hy, hg⟩ := sourceFreeDiracGraphB055C02_domain n y g hgraph
  rw [hRs]
  set Ssq := actualSchurEndomorphismToSquareV5_30 n
    (actualComplementaryQVDJointInverseV5_30 n (z, p)) with hSsq
  set Vs := actualSchurCoordinatePotential38 n p with hVs
  set Dsq := freeResolventSquare n z hz with hDsq
  set Qsq := complementarySquare n with hQsq
  have hQy : Qsq y = y := by
    have h := resonantSquare_add_complementarySquare38 n y
    rw [hPy, zero_add] at h
    exact h
  set h : SectorSquare n := freeShiftedCoordinateDirac n z ⟨y, hy⟩ with hh
  have hhval : h = z • y - g := by
    rw [hh, ← hg]
    rfl
  have hDh : Dsq (Qsq h) = y := by
    rw [hDsq, hQsq, freeResolventSquare_complementarySquare38,
      freeShiftedCoordinateDirac_left_inverse_complement]
    exact hQy
  have harg : z • y - Qsq g - Qsq (Vs y) =
      ((1 : SectorSquare n →L[ℂ] SectorSquare n) - Qsq.comp (Vs.comp Dsq)) (Qsq h) := by
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hDh, hhval,
      map_sub, map_smul, hQy]
  rw [harg, ContinuousLinearMap.comp_apply]
  have h2 := congrArg (fun T : SectorSquare n →L[ℂ] SectorSquare n => T (Qsq h)) hS2
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] at h2
  rw [h2, hDh]

end Pointwise

/-! ### (iii) Joint analyticity of the total family `Dext ∘ S` -/

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem actualSchurResolventFamily_analyticOnNhdB055C02
    (R : ℝ) (hR : 1 ≤ R)
    (n : ℤ) (hn : 1 ≤ |(n : ℝ)|)
    (hlarge : 4 * freeResolventSchurUniformConstant *
      physicalH1MultiplierConstant * R ^ 2 ≤ |(n : ℝ)|) :
    AnalyticOnNhd ℂ
      (fun x : ℂ × ActualH1PairJointSchurV5_30 =>
        actualSchurResolventFamilyAfterDextV3_32 n x.2 x.1)
      {x : ℂ × ActualH1PairJointSchurV5_30 |
        x.1 ∈ spectralDisk n ∧ ‖x.2.1‖ ≤ R ∧ ‖x.2.2‖ ≤ R} := by
  let Sdom : Set (ℂ × ActualSchurEffectiveH1PairV3_30) :=
    {x | x.1 ∈ spectralDisk n ∧ ‖x.2.1‖ ≤ R ∧ ‖x.2.2‖ ≤ R}
  let D : ℂ → ParityPair n →L[ℂ] ParityPair n :=
    actualFreeResolventCenterExtensionV1_30 n
  let S : (ℂ × ActualSchurEffectiveH1PairV3_30) → ParityPair n →L[ℂ] ParityPair n :=
    fun x => Ring.inverse (1 - actualComplementaryQVDJointParameterV5_30 n x)
  have hDbase : AnalyticOnNhd ℂ D (Metric.ball (spectralCenter n) 2) := by
    exact actualFreeResolventCenterExtension_analyticOnNhdV1_30 n
  have hfst : AnalyticOnNhd ℂ
      (fun x : ℂ × ActualSchurEffectiveH1PairV3_30 => x.1) Sdom :=
    analyticOnNhd_fst
  have hfstMaps : Set.MapsTo
      (fun x : ℂ × ActualSchurEffectiveH1PairV3_30 => x.1) Sdom
      (Metric.ball (spectralCenter n) 2) := by
    intro x hx
    change x.1 ∈ spectralDisk n ∧ ‖x.2.1‖ ≤ R ∧ ‖x.2.2‖ ≤ R at hx
    rcases hx with ⟨hz, -, -⟩
    have hz : ‖x.1 - spectralCenter n‖ ≤ 1 := by
      change ‖x.1 - spectralCenter n‖ ≤ 1 at hz
      exact hz
    rw [Metric.mem_ball, dist_eq_norm]
    change ‖x.1 - spectralCenter n‖ < 2
    linarith
  have hDclm : AnalyticOnNhd ℂ (fun x : ℂ × ActualSchurEffectiveH1PairV3_30 => D x.1) Sdom :=
    hDbase.comp hfst hfstMaps
  have hSclm : AnalyticOnNhd ℂ S Sdom := by
    simpa only [S] using
      (analyticOnNhd_actualComplementaryQVDJointInverseAfterDextV5_30
        R hR n hn hlarge)
  have hDictFactors := actualQVDProductAnalyticTargetDictionaryMinimumV3_30 R n
  letI : NormedRing (ParityPair n →L[ℂ] ParityPair n) :=
    ContinuousLinearMap.toNormedRing
  letI : NonUnitalNormedRing (ParityPair n →L[ℂ] ParityPair n) :=
    NormedRing.toNonUnitalNormedRing
  letI : NormedAddCommGroup (ParityPair n →L[ℂ] ParityPair n) :=
    NonUnitalNormedRing.toNormedAddCommGroup
  letI : NormedAlgebra ℂ (ParityPair n →L[ℂ] ParityPair n) :=
    ContinuousLinearMap.toNormedAlgebra
  letI : NormedSpace ℂ (ParityPair n →L[ℂ] ParityPair n) :=
    NormedAlgebra.toNormedSpace (ParityPair n →L[ℂ] ParityPair n)
  have hDring : AnalyticOnNhd ℂ (fun x : ℂ × ActualSchurEffectiveH1PairV3_30 => D x.1) Sdom := by
    have hactual :
        (letI : NormedAddCommGroup (ParityPair n →L[ℂ] ParityPair n) :=
          ContinuousLinearMap.toNormedAddCommGroup;
         letI : NormedSpace ℂ (ParityPair n →L[ℂ] ParityPair n) :=
          ContinuousLinearMap.toNormedSpace;
         AnalyticOnNhd ℂ
          (fun x : ℂ × ActualSchurEffectiveH1PairV3_30 => D x.1) Sdom) := by
      exact hDclm
    exact Eq.mp hDictFactors.1 hactual
  have hSdict :
      (letI : NormedAddCommGroup (ParityPair n →L[ℂ] ParityPair n) :=
        ContinuousLinearMap.toNormedAddCommGroup;
       letI : NormedSpace ℂ (ParityPair n →L[ℂ] ParityPair n) :=
        ContinuousLinearMap.toNormedSpace;
       AnalyticOnNhd ℂ S Sdom) =
      (letI : NormedRing (ParityPair n →L[ℂ] ParityPair n) :=
        ContinuousLinearMap.toNormedRing;
       letI : NonUnitalNormedRing (ParityPair n →L[ℂ] ParityPair n) :=
        NormedRing.toNonUnitalNormedRing;
       letI : NormedAddCommGroup (ParityPair n →L[ℂ] ParityPair n) :=
        NonUnitalNormedRing.toNormedAddCommGroup;
       letI : NormedAlgebra ℂ (ParityPair n →L[ℂ] ParityPair n) :=
        ContinuousLinearMap.toNormedAlgebra;
       letI : NormedSpace ℂ (ParityPair n →L[ℂ] ParityPair n) :=
        NormedAlgebra.toNormedSpace (ParityPair n →L[ℂ] ParityPair n);
       AnalyticOnNhd ℂ S Sdom) := by
    have hgroup := actualQVDPairEndNormedAddCommGroupDictionary_eqV3_30 n
    have hspace := actualQVDPairEndNormedSpaceDictionary_eqV3_30 n
    cases hgroup
    cases hspace
    rfl
  have hSring : AnalyticOnNhd ℂ S Sdom := Eq.mp hSdict hSclm
  have hDS : AnalyticOnNhd ℂ
      (fun x : ℂ × ActualSchurEffectiveH1PairV3_30 => D x.1 * S x) Sdom := by
    intro x hx
    exact (hDring x hx).mul (hSring x hx)
  have hFamDict :
      (letI : NormedAddCommGroup (ParityPair n →L[ℂ] ParityPair n) :=
        ContinuousLinearMap.toNormedAddCommGroup;
       letI : NormedSpace ℂ (ParityPair n →L[ℂ] ParityPair n) :=
        ContinuousLinearMap.toNormedSpace;
       AnalyticOnNhd ℂ
        (fun x : ℂ × ActualSchurEffectiveH1PairV3_30 =>
          actualSchurResolventFamilyAfterDextV3_32 n x.2 x.1) Sdom) =
      (letI : NormedRing (ParityPair n →L[ℂ] ParityPair n) :=
        ContinuousLinearMap.toNormedRing;
       letI : NonUnitalNormedRing (ParityPair n →L[ℂ] ParityPair n) :=
        NormedRing.toNonUnitalNormedRing;
       letI : NormedAddCommGroup (ParityPair n →L[ℂ] ParityPair n) :=
        NonUnitalNormedRing.toNormedAddCommGroup;
       letI : NormedAlgebra ℂ (ParityPair n →L[ℂ] ParityPair n) :=
        ContinuousLinearMap.toNormedAlgebra;
       letI : NormedSpace ℂ (ParityPair n →L[ℂ] ParityPair n) :=
        NormedAlgebra.toNormedSpace (ParityPair n →L[ℂ] ParityPair n);
       AnalyticOnNhd ℂ
        (fun x : ℂ × ActualSchurEffectiveH1PairV3_30 =>
          actualSchurResolventFamilyAfterDextV3_32 n x.2 x.1) Sdom) := by
    have hgroup := actualQVDPairEndNormedAddCommGroupDictionary_eqV3_30 n
    have hspace := actualQVDPairEndNormedSpaceDictionary_eqV3_30 n
    cases hgroup
    cases hspace
    rfl
  have hFamRing :
      (letI : NormedRing (ParityPair n →L[ℂ] ParityPair n) :=
        ContinuousLinearMap.toNormedRing;
       letI : NonUnitalNormedRing (ParityPair n →L[ℂ] ParityPair n) :=
        NormedRing.toNonUnitalNormedRing;
       letI : NormedAddCommGroup (ParityPair n →L[ℂ] ParityPair n) :=
        NonUnitalNormedRing.toNormedAddCommGroup;
       letI : NormedAlgebra ℂ (ParityPair n →L[ℂ] ParityPair n) :=
        ContinuousLinearMap.toNormedAlgebra;
       letI : NormedSpace ℂ (ParityPair n →L[ℂ] ParityPair n) :=
        NormedAlgebra.toNormedSpace (ParityPair n →L[ℂ] ParityPair n);
       AnalyticOnNhd ℂ
        (fun x : ℂ × ActualSchurEffectiveH1PairV3_30 =>
          actualSchurResolventFamilyAfterDextV3_32 n x.2 x.1) Sdom) := by
    exact hDS
  exact Eq.mpr hFamDict hFamRing

/-! ### Headline -/

/-- B055.C02 (F:eq:Rn, v2 lines 1085-1090): approved frozen statement. -/
theorem actualSchurComplementaryGraphResolventB055C02 :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R → ∀ n : ℤ, C * R ^ 2 ≤ |(n : ℝ)| →
      AnalyticOnNhd ℂ
        (fun x : ℂ × ActualH1PairJointSchurV5_30 =>
          actualSchurResolventFamilyAfterDextV3_32 n x.2 x.1)
        {x : ℂ × ActualH1PairJointSchurV5_30 |
          x.1 ∈ spectralDisk n ∧ ‖x.2.1‖ ≤ R ∧ ‖x.2.2‖ ≤ R} ∧
      ∀ (z : ℂ) (hz : z ∈ spectralDisk n) (p : ActualH1PairJointSchurV5_30),
        ‖p.1‖ ≤ R → ‖p.2‖ ≤ R →
        let P : ParityPair n →L[ℂ] ParityPair n := resonantParityPair n
        let Q : ParityPair n →L[ℂ] ParityPair n :=
          freeResolventComplementaryProjectionTransported n
        let D : ParityPair n →L[ℂ] ParityPair n := freeResolventParityPair n z hz
        let V : ParityPair n →L[ℂ] ParityPair n :=
          actualParityPairPotentialParameterAfterScalarWrapperCLM23 n p
        let Rn : ParityPair n →L[ℂ] ParityPair n :=
          actualSchurResolventFamilyAfterDextV3_32 n p z
        let Rs : SectorSquare n →L[ℂ] SectorSquare n :=
          actualSchurEndomorphismToSquareV5_30 n Rn
        let Vs : SectorSquare n →L[ℂ] SectorSquare n :=
          actualSchurCoordinatePotential38 n p
        IsUnit (1 - Q.comp (V.comp D)) ∧
        IsUnit (1 - D.comp (V.comp Q)) ∧
        Rn = actualSchurResolventFactorizedV5_31 n z p hz ∧
        Rn = D.comp (Ring.inverse (1 - Q.comp (V.comp D))) ∧
        Rn = (Ring.inverse (1 - D.comp (V.comp Q))).comp D ∧
        Rn.comp P = 0 ∧
        P.comp Rn = 0 ∧
        (∀ x : SectorSquare n,
          resonantSquare n (Rs x) = 0 ∧
          ∃ g : SectorSquare n, sourceFreeDiracGraphB055C02 n (Rs x) g ∧
            z • Rs x - complementarySquare n g - complementarySquare n (Vs (Rs x)) =
              complementarySquare n x) ∧
        (∀ y g : SectorSquare n, resonantSquare n y = 0 →
          sourceFreeDiracGraphB055C02 n y g →
          Rs (z • y - complementarySquare n g - complementarySquare n (Vs y)) = y) := by
  refine ⟨max 1 (4 * freeResolventSchurUniformConstant * physicalH1MultiplierConstant),
    lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro R hR n hnC
  have hR2 : 1 ≤ R ^ 2 := by nlinarith
  have hn : 1 ≤ |(n : ℝ)| :=
    le_trans (one_le_mul_of_one_le_of_one_le (le_max_left _ _) hR2) hnC
  have hlarge : 4 * freeResolventSchurUniformConstant *
      physicalH1MultiplierConstant * R ^ 2 ≤ |(n : ℝ)| :=
    le_trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg R)) hnC
  refine ⟨actualSchurResolventFamily_analyticOnNhdB055C02 R hR n hn hlarge, ?_⟩
  intro z hz p hp₁ hp₂
  intro P Q D V Rn Rs Vs
  obtain ⟨hU1, hU2⟩ := actualSchurUnitsB055C02 R hR n hn hlarge z hz p hp₁ hp₂
  obtain ⟨hF1, hF2, hF3⟩ :=
    actualSchurFactorizationsB055C02 R hR n hn hlarge z hz p hp₁ hp₂
  obtain ⟨hZ1, hZ2⟩ :=
    actualSchurResolventZeroExtensionB055C02 R hR n hn hlarge z hz p hp₁ hp₂
  exact ⟨hU1, hU2, hF1, hF2, hF3, hZ1, hZ2,
    fun x => actualSchurGraphRightInverseB055C02 R hR n hn hlarge z hz p hp₁ hp₂ x,
    fun y g hPy hg =>
      actualSchurGraphLeftInverseB055C02 R hR n hn hlarge z hz p hp₁ hp₂ y g hPy hg⟩

end NlsGge.Schur
