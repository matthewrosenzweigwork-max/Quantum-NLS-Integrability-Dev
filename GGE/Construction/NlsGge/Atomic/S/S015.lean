import Mathlib
import NlsGge.ThirdConsultation.S.SShared06
import NlsGge.Schur.ActualSchurRealTypeSymmetry38V1
import NlsGge.Schur.ActualComplementaryQVDJointInverseAndEqualDiagonalV5_30
import NlsGge.Schur.ActualFreeResolventCenterExtensionV1_30
import NlsGge.Schur.ActualParityPairPotentialParameterAfterScalarWrapper23
import NlsGge.Schur.FreeResolventComplementaryQDTransportAfterCoordinateRange
import NlsGge.Schur.FreeResolventComplementaryDQTransportAfterCoordinateRange

                                                                                                                      
                                                                                                                           
                                                                                              
                                                   
                                                                                                      
                                                                                                                                        
                                                                                                                                          
                                                                                                                     
                                                                                                              
                                                                                                          
                                                                                       
                                                                                                                       
                                                                                                                    
                                                                                                       
                                                                                                  
                                                                                                                     
                                                                                                              
                                                                                                                  
set_option autoImplicit false
noncomputable section
open NlsGge.Pilot NlsGge.Analysis NlsGge.Schur
namespace NlsGge.ThirdConsultation.S

/-- Concrete (`ParityPair n`) form of the resolvent self-adjointness: for `S = (1 - Q V D)⁻¹` with `Q D = D`,
`D Q = D`, self-adjoint `Q, D, V` and a unit `1 - Q V D`, `D S` is self-adjoint. Same argument as the internal
`hR` step of `NlsGge.Schur.effectiveSelfAdjointAbstract38`. -/
theorem s015_resolvent_adjoint_concrete (n : ℤ)
    (Q D V : ParityPair n →L[ℂ] ParityPair n)
    (hQ : ContinuousLinearMap.adjoint Q = Q)
    (hD : ContinuousLinearMap.adjoint D = D) (hV : ContinuousLinearMap.adjoint V = V)
    (hQD : Q.comp D = D) (hDQ : D.comp Q = D)
    (hunit : IsUnit (1 - Q.comp (V.comp D))) :
    ContinuousLinearMap.adjoint (D.comp (Ring.inverse (1 - Q.comp (V.comp D)))) =
      D.comp (Ring.inverse (1 - Q.comp (V.comp D))) := by
  set Y : ParityPair n →L[ℂ] ParityPair n := 1 - Q.comp (V.comp D) with hYdef
  set X : ParityPair n →L[ℂ] ParityPair n := 1 - D.comp (V.comp Q) with hXdef
  set S : ParityPair n →L[ℂ] ParityPair n := Ring.inverse Y with hSdef
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
  have hRad : ContinuousLinearMap.adjoint (D.comp S) = D.comp S := by
    rw [ContinuousLinearMap.adjoint_comp, hD, hshift]
  exact hRad

/-- Concrete (`ParityPair n`) form of the effective self-adjointness with the R^2-level unit hypothesis; the proof
is that of `NlsGge.Schur.effectiveSelfAdjointAbstract38`, whose internal resolvent step is the lemma above. -/
theorem s015_effective_adjoint_concrete (n : ℤ)
    (P Q D V : ParityPair n →L[ℂ] ParityPair n)
    (hP : ContinuousLinearMap.adjoint P = P) (hQ : ContinuousLinearMap.adjoint Q = Q)
    (hD : ContinuousLinearMap.adjoint D = D) (hV : ContinuousLinearMap.adjoint V = V)
    (hQD : Q.comp D = D) (hDQ : D.comp Q = D)
    (hunit : IsUnit (1 - Q.comp (V.comp D))) :
    ContinuousLinearMap.adjoint
      (P.comp (V.comp P) +
        P.comp (V.comp ((D.comp (Ring.inverse (1 - Q.comp (V.comp D)))).comp (V.comp P)))) =
      P.comp (V.comp P) +
        P.comp (V.comp ((D.comp (Ring.inverse (1 - Q.comp (V.comp D)))).comp (V.comp P))) := by
  have hR := s015_resolvent_adjoint_concrete n Q D V hQ hD hV hQD hDQ hunit
  generalize D.comp (Ring.inverse (1 - Q.comp (V.comp D))) = R at hR ⊢
  simp only [map_add, ContinuousLinearMap.adjoint_comp, hP, hV, hR, ContinuousLinearMap.comp_assoc]

/-- Unfolding of the effective operator at the real-type pair (by definition; checked by `rfl`). -/
theorem s015_effective_unfold (n : ℤ) (x : ℂ) (w : WeightedHilbert (sobolevModeWeight (1 : ℝ))) :
    actualSchurEffectiveOperatorAfterDextV3_30 n (x, (w, actualH1Conj38 w)) =
      (resonantParityPair n).comp
          ((actualParityPairPotentialParameterAfterScalarWrapperCLM23 n (w, actualH1Conj38 w)).comp
            (resonantParityPair n)) +
        (resonantParityPair n).comp
          ((actualParityPairPotentialParameterAfterScalarWrapperCLM23 n (w, actualH1Conj38 w)).comp
            (((actualFreeResolventCenterExtensionV1_30 n x).comp
              (Ring.inverse (1 - (freeResolventComplementaryProjectionTransported n).comp
                ((actualParityPairPotentialParameterAfterScalarWrapperCLM23 n (w, actualH1Conj38 w)).comp
                  (actualFreeResolventCenterExtensionV1_30 n x))))).comp
              ((actualParityPairPotentialParameterAfterScalarWrapperCLM23 n (w, actualH1Conj38 w)).comp
                (resonantParityPair n)))) := rfl

/-- Self-adjointness of the effective operator and of the resolvent family on the real-type pair
`(w, conj w)` at real spectral parameter `x` in the spectral disk, under the R^2 threshold only. -/
theorem s015_realType_selfAdjoint (R : ℝ) (hR : 1 ≤ R) (n : ℤ) (hn : 1 ≤ |(n : ℝ)|)
    (hlarge : 4 * freeResolventSchurUniformConstant *
      physicalH1MultiplierConstant * R ^ 2 ≤ |(n : ℝ)|)
    (x : ℝ) (hx : (x : ℂ) ∈ spectralDisk n)
    (w : WeightedHilbert (sobolevModeWeight (1 : ℝ))) (hw : ‖w‖ ≤ R) :
    ContinuousLinearMap.adjoint
      (actualSchurEffectiveOperatorAfterDextV3_30 n ((x : ℂ), (w, actualH1Conj38 w))) =
      actualSchurEffectiveOperatorAfterDextV3_30 n ((x : ℂ), (w, actualH1Conj38 w)) ∧
    ContinuousLinearMap.adjoint (resolventFamily n (x : ℂ) (schurRealPair w)) =
      resolventFamily n (x : ℂ) (schurRealPair w) := by
  have hw' : ‖actualH1Conj38 w‖ ≤ R := by rw [actualH1Conj38_norm]; exact hw
  have hDe : actualFreeResolventCenterExtensionV1_30 n (x : ℂ) =
      freeResolventParityPair n (x : ℂ) hx :=
    actualFreeResolventCenterExtension_eq_actualV1_30 n (x : ℂ) hx
  have hunit := actualComplementaryQVDJointOneSubIsUnitV5_30 R hR n hn hlarge (x : ℂ)
    (w, actualH1Conj38 w) hx hw hw'
  have hDad : ContinuousLinearMap.adjoint (actualFreeResolventCenterExtensionV1_30 n (x : ℂ)) =
      actualFreeResolventCenterExtensionV1_30 n (x : ℂ) := by
    rw [hDe]; exact freeResolventParityPair_adjoint_real38 n x hx
  have hVad : ContinuousLinearMap.adjoint
      (actualParityPairPotentialParameterAfterScalarWrapperCLM23 n (w, actualH1Conj38 w)) =
      actualParityPairPotentialParameterAfterScalarWrapperCLM23 n (w, actualH1Conj38 w) := by
    rw [actualParityPairPotentialParameterAfterScalarWrapperCLM23_apply]
    exact coveredH1ParityPairPotential_adjoint_of_star38 _ _ _ _ (physicalH1_conj38 w) n
  have hQD : (freeResolventComplementaryProjectionTransported n).comp
      (actualFreeResolventCenterExtensionV1_30 n (x : ℂ)) =
      actualFreeResolventCenterExtensionV1_30 n (x : ℂ) := by
    rw [hDe]; exact freeResolventParityPair_comp_complementaryProjection_afterCoordinateRange n _ hx
  have hDQ : (actualFreeResolventCenterExtensionV1_30 n (x : ℂ)).comp
      (freeResolventComplementaryProjectionTransported n) =
      actualFreeResolventCenterExtensionV1_30 n (x : ℂ) := by
    rw [hDe]
    exact freeResolventParityPair_comp_complementaryProjection_right_afterCoordinateRange n _ hx
  constructor
  · rw [s015_effective_unfold n (x : ℂ) w]
    exact s015_effective_adjoint_concrete n (resonantParityPair n)
      (freeResolventComplementaryProjectionTransported n)
      (actualFreeResolventCenterExtensionV1_30 n (x : ℂ))
      (actualParityPairPotentialParameterAfterScalarWrapperCLM23 n (w, actualH1Conj38 w))
      (resonantParityPair_adjoint38 n) (complementaryProjectionTransported_adjoint38 n)
      hDad hVad hQD hDQ hunit
  · exact s015_resolvent_adjoint_concrete n (freeResolventComplementaryProjectionTransported n)
      (actualFreeResolventCenterExtensionV1_30 n (x : ℂ))
      (actualParityPairPotentialParameterAfterScalarWrapperCLM23 n (w, actualH1Conj38 w))
      (complementaryProjectionTransported_adjoint38 n) hDad hVad hQD hDQ hunit

theorem effective_realType :
    ∃ K : ℝ, 0 < K ∧ ∀ (R : ℝ) (n : ℤ) (r : ℝ) (w : SchurH1),
      schurParameterDomain K R n (r : ℂ) (schurRealPair w) →
      (alphaAt n r (schurRealPair w)).im = 0 ∧
      cAt n r (schurRealPair w) = star (bAt n r (schurRealPair w)) ∧
      ContinuousLinearMap.adjoint (resolventFamily n r (schurRealPair w)) =
        resolventFamily n r (schurRealPair w) := by
  refine ⟨|4 * freeResolventSchurUniformConstant * physicalH1MultiplierConstant| + 1, by positivity, ?_⟩
  intro R n r w hdom
  unfold schurParameterDomain at hdom
  obtain ⟨hR, hn0, hK, hz, hp₁, hp₂⟩ := hdom
  have hn : 1 ≤ |(n : ℝ)| := by
    have h1 : (1 : ℤ) ≤ |n| := Int.one_le_abs hn0
    exact_mod_cast h1
  have hlarge : 4 * freeResolventSchurUniformConstant * physicalH1MultiplierConstant * R ^ 2 ≤
      |(n : ℝ)| := by
    have hle := le_abs_self (4 * freeResolventSchurUniformConstant * physicalH1MultiplierConstant)
    have hR2 : 0 ≤ R ^ 2 := sq_nonneg R
    have h2 : 4 * freeResolventSchurUniformConstant * physicalH1MultiplierConstant * R ^ 2 ≤
        (|4 * freeResolventSchurUniformConstant * physicalH1MultiplierConstant| + 1) * R ^ 2 := by
      nlinarith
    linarith
  obtain ⟨hA, hRes⟩ := s015_realType_selfAdjoint R hR n hn hlarge r hz w hp₁
  refine ⟨?_, ?_, hRes⟩
  · have h := actualSchurCoefficient_star_of_selfAdjoint38 n (r : ℂ) (w, actualH1Conj38 w) hA
      (true, resonantIndex n) (true, resonantIndex n)
    have h' : (starRingEnd ℂ) (alphaAt n r (schurRealPair w)) =
        alphaAt n r (schurRealPair w) := h.symm
    exact Complex.conj_eq_iff_im.mp h'
  · exact actualSchurCoefficient_star_of_selfAdjoint38 n (r : ℂ) (w, actualH1Conj38 w) hA
      (false, resonantIndex n) (true, resonantIndex n)

end NlsGge.ThirdConsultation.S
