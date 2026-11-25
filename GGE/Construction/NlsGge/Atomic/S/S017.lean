import Mathlib
import NlsGge.ThirdConsultation.S.SShared06
import NlsGge.Schur.ActualSchurEffectiveDerivativeActual38V1
import NlsGge.Schur.ActualSchurGreenProductBoundV3_31
import NlsGge.Schur.RootActualSchurResolventAfterDextHasFDerivAtNegativeSquareMinimum36V8
import NlsGge.Schur.ActualFreeResolventCenterExtensionV1_30
import NlsGge.Schur.ActualParityPairPotentialParameterAfterScalarWrapper23

                                                                                                                   
                                                                                            
                                                                                                            
                                                                              
                                                                                                               
                                                                                                                
                                                                                                                
                                                           
set_option autoImplicit false
noncomputable section
open NlsGge.Pilot NlsGge.Analysis NlsGge.Schur
namespace NlsGge.ThirdConsultation.S

private theorem s017_green_column_eq (n : ℤ) (z : ℂ) (p : SchurPair) (hz : z ∈ spectralDisk n) :
    greenColumn n z p = actualSchurGreenColumnV5_31 n z p hz := by
  unfold greenColumn resolventFamily actualSchurResolventFamilyAfterDextV3_32 potentialAt
  rw [actualParityPairPotentialParameterAfterScalarWrapperCLM23_apply,
    actualFreeResolventCenterExtension_eq_actualV1_30 n z hz]
  rfl

private theorem s017_green_row_eq (n : ℤ) (z : ℂ) (p : SchurPair) (hz : z ∈ spectralDisk n) :
    greenRow n z p = actualSchurGreenRowV5_31 n z p hz := by
  unfold greenRow resolventFamily actualSchurResolventFamilyAfterDextV3_32 potentialAt
  rw [actualParityPairPotentialParameterAfterScalarWrapperCLM23_apply,
    actualFreeResolventCenterExtension_eq_actualV1_30 n z hz]
  rfl

/-- Generic (abstract normed space over an abstract nontrivially normed field): a derivative of the form
`toSpanSingleton 𝕜 v` at `x` gives `HasDerivAt f v x`. -/
theorem s017_hasDerivAt_of_hasFDerivAt {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {f : 𝕜 → E} {v : E} {x : 𝕜}
    (h : HasFDerivAt f (ContinuousLinearMap.toSpanSingleton 𝕜 v) x) : HasDerivAt f v x := by
  have h1 := h.hasDerivAt
  rwa [ContinuousLinearMap.toSpanSingleton_apply, one_smul] at h1

/-- Generic transport: equal functions and equal derivatives carry a `HasDerivAt` statement. -/
theorem s017_transport {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {f g : 𝕜 → E} {v w : E} {x : 𝕜}
    (hf : f = g) (hv : v = w) (h : HasDerivAt f v x) : HasDerivAt g w x := by
  subst hf
  subst hv
  exact h

/-- Generic real bound: `X ≤ A R^4/N^2` gives `X ≤ (|A|+1) R^4/N^2`. -/
theorem s017_bound_of_le {A X R N : ℝ} (hX : X ≤ A * R ^ 4 / N ^ 2) :
    X ≤ (|A| + 1) * R ^ 4 / N ^ 2 := by
  have hA : A ≤ |A| + 1 := by linarith [le_abs_self A]
  refine hX.trans ?_
  gcongr

theorem schur_spectral_derivative :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (R : ℝ) (n : ℤ) (z : ℂ) (p : SchurPair),
        schurParameterDomain K R n z p →
        HasDerivAt (fun t : ℂ => resolventFamily n t p)
          (-(resolventFamily n z p).comp (resolventFamily n z p)) z ∧
        HasDerivAt (fun t : ℂ => effectiveAt n t p)
          (-(greenRow n z p).comp (greenColumn n z p)) z ∧
        ‖(greenRow n z p).comp (greenColumn n z p)‖ ≤
          C * R ^ 4 / |(n : ℝ)| ^ 2 := by
  refine ⟨|freeResolventComplementaryInverseUniformConstant22 ^ 2 * freeResolventSchurUniformConstant ^ 2| + 1,
    |4 * freeResolventSchurUniformConstant * physicalH1MultiplierConstant| + 1, by positivity, by positivity,
    ?_⟩
  intro R n z p hdom
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
  have hD := rootActualSchurResolventFamilyAfterDext_hasFDerivAt_negativeSquareMinimum36V8
    R hR n hn hlarge p z hz hp₁ hp₂
  have hE := actualSchurEffective_hasFDerivAt_actualResolvent38V1
    R hR n hn hlarge p z hz hp₁ hp₂
  have hB := actualSchurGreenDerivativeProduct_boundV3_31 R hR n hn hlarge z p hz hp₁ hp₂
  have hrow := s017_green_row_eq n z p hz
  have hcol := s017_green_column_eq n z p hz
  -- conjunct 1 data: derivative of the computational resolvent family
  have hD1 : HasDerivAt (actualSchurResolventFamilyAfterDextV3_32 n p)
      (-((actualSchurResolventFamilyAfterDextV3_32 n p z).comp
        (actualSchurResolventFamilyAfterDextV3_32 n p z))) z :=
    s017_hasDerivAt_of_hasFDerivAt (𝕜 := ℂ) (E := ParityPair n →L[ℂ] ParityPair n) hD
  -- conjunct 2 data: derivative of the effective operator on the spectral line
  have hE1 : HasDerivAt (actualSchurEffectiveSpectralLineV3_32 n p)
      (-(actualSchurGreenDerivativeProductV3_31 n z p hz)) z :=
    s017_hasDerivAt_of_hasFDerivAt (𝕜 := ℂ) (E := ParityPair n →L[ℂ] ParityPair n) hE
  have hvE2 : -(actualSchurGreenDerivativeProductV3_31 n z p hz) =
      -((greenRow n z p).comp (greenColumn n z p)) := by
    rw [hrow, hcol]
    rfl
  -- conjunct 3 data: the norm of the product, identified with the production product
  have hX : ‖(greenRow n z p).comp (greenColumn n z p)‖ =
      ‖actualSchurGreenDerivativeProductV3_31 n z p hz‖ := by
    rw [hrow, hcol]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · exact s017_transport (𝕜 := ℂ) (E := ParityPair n →L[ℂ] ParityPair n)
      (f := actualSchurResolventFamilyAfterDextV3_32 n p)
      (g := fun t : ℂ => resolventFamily n t p)
      (v := -((actualSchurResolventFamilyAfterDextV3_32 n p z).comp
        (actualSchurResolventFamilyAfterDextV3_32 n p z)))
      (w := -((resolventFamily n z p).comp (resolventFamily n z p)))
      (x := z) rfl rfl hD1
  · exact s017_transport (𝕜 := ℂ) (E := ParityPair n →L[ℂ] ParityPair n)
      (f := actualSchurEffectiveSpectralLineV3_32 n p)
      (g := fun t : ℂ => effectiveAt n t p)
      (v := -(actualSchurGreenDerivativeProductV3_31 n z p hz))
      (w := -((greenRow n z p).comp (greenColumn n z p)))
      (x := z) rfl hvE2 hE1
  · rw [hX]
    exact s017_bound_of_le hB

end NlsGge.ThirdConsultation.S
