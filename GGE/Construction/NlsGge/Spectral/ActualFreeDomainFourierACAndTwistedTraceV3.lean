import NlsGge.Schur.SourceFreeDomainWeakDerivativeForwardV1
import NlsGge.Schur.FreeDomainContinuousL2AfterReflectedPrerequisite
import NlsGge.Schur.SourceSubintervalIntegralPairingCLMV5

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Interval

namespace NlsGge.Schur

local instance : IsProbabilityMeasure spectralHaar := by
  unfold spectralHaar
  infer_instance

/-- The continuous Fourier representative of an actual free weighted-domain
vector is the integral of its actual free-coordinate derivative class, in
both reflected channels. The same representative has the actual twisted
endpoint trace. This is only the free diagonal domain statement; it does not
assert a perturbed L²-potential ODE theorem. -/
theorem freeDomainContinuousComponent_integral_and_twistedTrace
    (n : ℤ) (x : SectorSquare n) (hx : x ∈ freeWeightedDomainPointwise n)
    (upper : Bool) :
    (∀ t ∈ Set.Icc (0 : ℝ) 1,
      freeDomainContinuousComponent n x upper ((t : ℝ) : SpectralCircle) =
        freeDomainContinuousComponent n x upper ((0 : ℝ) : SpectralCircle) +
          ∫ s in (0 : ℝ)..t, sourceFreeCoordinateDerivative n x hx upper s) ∧
      freeDomainContinuousComponent n x upper ((1 : ℝ) : SpectralCircle) =
        spectralSign n * freeDomainContinuousComponent n x upper ((0 : ℝ) : SpectralCircle) := by
  constructor
  · intro t ht
    let a : Sector n → ℂ := fun m => x (upper,m)
    have hstate (r : ℝ) :
        Tendsto
          (fun S : Finset (Sector n) =>
            sourceFiniteCharacter n upper S a r)
          atTop
          (nhds (freeDomainContinuousComponent n x upper
            ((r : ℝ) : SpectralCircle))) := by
      simpa only [HasSum, SummationFilter.unconditional, sourceFiniteCharacter, a] using
        freeDomainContinuousComponent_hasSum_eval n x hx upper
          ((r : ℝ) : SpectralCircle)
    have hstateT := hstate t
    have hstate0 := hstate 0
    have hderivIntegral :
        Tendsto
          (fun S : Finset (Sector n) =>
            ∫ s in (0 : ℝ)..t,
              scalarParityRestrict n
                (sourceFiniteParityFourier n upper S
                  (sourceFiniteDerivativeCoefficients n upper a)) s)
          atTop
          (nhds (∫ s in (0 : ℝ)..t,
            sourceFreeCoordinateDerivative n x hx upper s)) := by
      simpa only [Function.comp_def, sourceSubintervalIntegralCLM_apply] using
        (((sourceSubintervalIntegralCLM t ht).continuous.tendsto
          (sourceFreeCoordinateDerivative n x hx upper)).comp
          (sourceFreeCoordinateDerivative_finite_tendsto n x hx upper))
    have hfinite (S : Finset (Sector n)) :
        sourceFiniteCharacter n upper S a t =
          sourceFiniteCharacter n upper S a 0 +
            ∫ s in (0 : ℝ)..t,
              scalarParityRestrict n
                (sourceFiniteParityFourier n upper S
                  (sourceFiniteDerivativeCoefficients n upper a)) s := by
      have hchar := sourceFiniteParityFourier_ae_character n upper S
        (sourceFiniteDerivativeCoefficients n upper a)
      have hsubset : Set.Ioc (0 : ℝ) t ⊆ Set.Ioc (0 : ℝ) 1 := by
        intro s hs
        exact ⟨hs.1, hs.2.trans ht.2⟩
      have hchar_t :
          scalarParityRestrict n
              (sourceFiniteParityFourier n upper S
                (sourceFiniteDerivativeCoefficients n upper a)) =ᵐ[
                volume.restrict (Set.Ioc (0 : ℝ) t)]
            sourceFiniteCharacterDerivative n upper S a :=
        (hchar.filter_mono
          (ae_mono (Measure.restrict_mono_set volume hsubset))).trans
          (Filter.Eventually.of_forall fun s =>
            congrFun (sourceFiniteCharacter_derivative_coefficients n upper S a) s)
      have hI :
          (∫ s in (0 : ℝ)..t,
            scalarParityRestrict n
              (sourceFiniteParityFourier n upper S
                (sourceFiniteDerivativeCoefficients n upper a)) s) =
          ∫ s in (0 : ℝ)..t, sourceFiniteCharacterDerivative n upper S a s := by
        rw [intervalIntegral.integral_of_le ht.1,
          intervalIntegral.integral_of_le ht.1]
        exact integral_congr_ae hchar_t
      have hFTC :
          (∫ s in (0 : ℝ)..t, sourceFiniteCharacterDerivative n upper S a s) =
            sourceFiniteCharacter n upper S a t -
              sourceFiniteCharacter n upper S a 0 :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun s _ => sourceFiniteCharacter_hasDerivAt n upper S a s)
          ((sourceFiniteCharacterDerivative_continuous n upper S a).intervalIntegrable
            0 t)
      calc
        sourceFiniteCharacter n upper S a t =
            sourceFiniteCharacter n upper S a 0 +
              ∫ s in (0 : ℝ)..t, sourceFiniteCharacterDerivative n upper S a s := by
          rw [hFTC]
          ring
        _ = sourceFiniteCharacter n upper S a 0 +
              ∫ s in (0 : ℝ)..t,
                scalarParityRestrict n
                  (sourceFiniteParityFourier n upper S
                    (sourceFiniteDerivativeCoefficients n upper a)) s := by
          rw [← hI]
    have hright :
        Tendsto
          (fun S : Finset (Sector n) =>
            sourceFiniteCharacter n upper S a 0 +
              ∫ s in (0 : ℝ)..t,
                scalarParityRestrict n
                  (sourceFiniteParityFourier n upper S
                    (sourceFiniteDerivativeCoefficients n upper a)) s)
          atTop
          (nhds (freeDomainContinuousComponent n x upper
              ((0 : ℝ) : SpectralCircle) +
            ∫ s in (0 : ℝ)..t,
              sourceFreeCoordinateDerivative n x hx upper s)) :=
      hstate0.add hderivIntegral
    have hright' := hright.congr fun S => (hfinite S).symm
    exact tendsto_nhds_unique hstateT hright'
  · exact freeDomainContinuousComponent_endpoint_parity n x hx upper

/-- The continuous Fourier representative is identified with the actual
weighted-domain vector in the spectral L² carrier. -/
theorem freeDomainContinuousComponent_toLp_actualClass
    (n : ℤ) (x : SectorSquare n) (hx : x ∈ freeWeightedDomainPointwise n)
    (upper : Bool) :
    ContinuousMap.toLp 2 spectralHaar ℂ (freeDomainContinuousComponent n x upper) =
      (((parityPairRepr n).symm x upper : scalarParity n) : SpectralScalarL2) :=
  freeDomainContinuousComponent_toLp n x hx upper

end NlsGge.Schur

end
