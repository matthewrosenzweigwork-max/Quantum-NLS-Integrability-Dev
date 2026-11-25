import Mathlib

import NlsGge.Atomic.PhysicalSobolev
import NlsGge.Hierarchy.RiccatiSobolevIteratedDerivativeL2CLMRecovery30First
import NlsGge.Hierarchy.RiccatiSobolevLowerJetContinuousRepresentativeCLMRecovery30Eighth
import NlsGge.Sobolev.SourceReflection
import NlsGge.GK38.PairVolterra
import NlsGge.Hierarchy.RiccatiPhysicalFourierL2SymmCoefficientsSecond
import NlsGge.Hierarchy.RiccatiPhysicalH1CanonicalAndDerivativeCLMAfterDerivativeClassLinearityPrerequisite
import NlsGge.Analysis.NaturalCover
import NlsGge.Analysis.H1Fourier

set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory
open scoped ENNReal
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.GK38
open NlsGge.HierarchyRiccati.Core

namespace NlsGge.Atomic.Common

-- This converts the HOUSE reflected completion coordinate to the ordinary
-- Fourier coordinate expected by the existing Riccati derivative constructors.
def ordinarySobolevCarrier38 (m : ℕ) (u : PhysicalSobolev38 (m : ℝ)) :
    SobolevHilbert (m : ℝ) :=
  let z := physicalSobolevFourierEquiv38 (m : ℝ) u
  ofCarrier38 (m : ℝ)
    (carrierMk38 (m : ℝ) (fun n : ℤ => -carrierCoe38 (m : ℝ) z (-n))
      ((mem_seqSobolev38_iff (m : ℝ) _).2
        (sobolevSquareSummable_reflection (m : ℝ) (carrierCoe38 (m : ℝ) z)
          ((mem_seqSobolev38_iff (m : ℝ) _).1
            (carrierCoe38_mem (m : ℝ) z)))))

-- No zero fallback, arbitrary inverse, new construction axiom, or assumed
-- Fourier derivative conclusion appears in this body.
def physicalSobolevDerivative38 (N : ℕ)
    (u : PhysicalSobolev38 (N : ℝ)) : PhysicalL2 :=
  riccatiSobolevIteratedDerivativeL2CLMRecovery30First N N (Nat.le_refl N)
    (ordinarySobolevCarrier38 N u)

-- The canonical continuous representative is used only when 1 ≤ m.
def physicalSobolevContinuous38 (m : ℕ) (hm : 1 ≤ m)
    (u : PhysicalSobolev38 (m : ℝ)) : C(PhysicalCircle, ℂ) :=
  riccatiSobolevLowerJetContinuousRepresentativeCLMRecovery30Eighth m 0
    (by simpa using hm) (ordinarySobolevCarrier38 m u)

end NlsGge.Atomic.Common

namespace NlsGge.GKDefinitionDesign

def sequenceSobolevEmbed (m : ℕ) (z : SobolevCarrier38 (m : ℝ)) :
    lp (fun _ : ℤ => ℂ) 2 :=
  let z0 : SobolevCarrier38 0 :=
    carrierIncl38 (r := 0) (s := (m : ℝ)) (Nat.cast_nonneg m) z
  seqToLp38 (carrierCoe38 0 z0) (carrierCoe38_mem 0 z0)

def physicalSobolevEmbed (m : ℕ)
    (u : PhysicalSobolev38 (m : ℝ)) : PhysicalL2 :=
  reflectedFourierL2.symm
    (sequenceSobolevEmbed m (physicalSobolevFourierEquiv38 (m : ℝ) u))

-- Explicit real-line evaluation: canonical continuous Sobolev representative
-- when available; the existing real-line L2 representative for m=0.
def sobolevPointValue (m : ℕ) (u : PhysicalSobolev38 (m : ℝ)) (x : ℝ) : ℂ :=
  if hm : 1 ≤ m then physicalSobolevContinuous38 m hm u (x : PhysicalCircle)
  else coverRep38 (physicalSobolevEmbed m u) x

end NlsGge.GKDefinitionDesign


local instance : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure
  infer_instance

namespace NlsGge.GKDefinitionDesign

theorem physicalSobolevEmbed_fourier (m : ℕ)
    (u : PhysicalSobolev38 (m : ℝ)) (n : ℤ) :
  fourierSeq38 (physicalSobolevEmbed m u) n =
    carrierCoe38 (m : ℝ) (physicalSobolevFourierEquiv38 (m : ℝ) u) n := by
  unfold fourierSeq38 physicalSobolevEmbed
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact congrFun (carrierCoe38_incl38 (Nat.cast_nonneg m) _) n

theorem ordinarySobolevCarrier38_fourier (m : ℕ)
    (u : PhysicalSobolev38 (m : ℝ)) (n : ℤ) :
  (show WeightedHilbert (sobolevModeWeight (m : ℝ)) from
      ordinarySobolevCarrier38 m u) n =
    physicalFourier (physicalSobolevEmbed m u) n := by
  have h1 := fourierSeq38_apply (physicalSobolevEmbed m u) (-n)
  rw [neg_neg, physicalSobolevEmbed_fourier] at h1
  have h2 : physicalFourier (physicalSobolevEmbed m u) n =
      -carrierCoe38 (m : ℝ) (physicalSobolevFourierEquiv38 (m : ℝ) u) (-n) := by
    rw [h1]; ring
  rw [h2]
  rfl

theorem physicalSobolevDerivative38_fourier (N : ℕ)
    (u : PhysicalSobolev38 (N : ℝ)) (n : ℤ) :
  physicalFourier (physicalSobolevDerivative38 N u) n =
    (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) ^ N *
      physicalFourier (physicalSobolevEmbed N u) n := by
  unfold physicalSobolevDerivative38
  rw [riccatiSobolevIteratedDerivativeL2CLMRecovery30First_fourier]
  change fourierMultiplier n ^ N * _ = _
  rw [ordinarySobolevCarrier38_fourier]
  rfl

theorem physicalSobolevDerivative38_reflected (N : ℕ)
    (u : PhysicalSobolev38 (N : ℝ)) (n : ℤ) :
  fourierSeq38 (physicalSobolevDerivative38 N u) n =
    (-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) ^ N *
      carrierCoe38 (N : ℝ) (physicalSobolevFourierEquiv38 (N : ℝ) u) n := by
  rw [fourierSeq38_apply, physicalSobolevDerivative38_fourier]
  have h1 := fourierSeq38_apply (physicalSobolevEmbed N u) n
  rw [physicalSobolevEmbed_fourier] at h1
  have h2 : physicalFourier (physicalSobolevEmbed N u) (-n) =
      -carrierCoe38 (N : ℝ) (physicalSobolevFourierEquiv38 (N : ℝ) u) n := by
    rw [h1]; ring
  rw [h2]
  have h4 : (2 * (Real.pi : ℂ) * Complex.I * ((-n : ℤ) : ℂ)) =
      (-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) := by
    push_cast; ring
  rw [h4]; ring


theorem physicalSobolevContinuous38_toLp (m : ℕ) (hm : 1 ≤ m)
    (u : PhysicalSobolev38 (m : ℝ)) :
  ContinuousMap.toLp 2 spatialMeasure ℂ (physicalSobolevContinuous38 m hm u) =
    physicalSobolevEmbed m u := by
  unfold physicalSobolevContinuous38
  unfold riccatiSobolevLowerJetContinuousRepresentativeCLMRecovery30Eighth
  change ContinuousMap.toLp 2 spatialMeasure ℂ
    (physicalH1CanonicalContinuousRepresentativeCLM _) = _
  rw [physicalH1CanonicalContinuousRepresentativeCLM_apply]
  unfold physicalH1CarrierContinuousAfterAcceptedCoordinate
  rw [NlsGge.Analysis.physicalH1Continuous_toLp]
  apply physicalFourierL2.injective
  apply lp.ext
  funext n
  rw [physicalFourierL2_apply, physicalFourierL2_apply,
    physicalH1CarrierToL2AfterAcceptedCoordinate_fourier]
  rw [← ordinarySobolevCarrier38_fourier]
  change fourierMultiplier n ^ 0 *
    (show WeightedHilbert (sobolevModeWeight (m : ℝ)) from ordinarySobolevCarrier38 m u) n = _
  rw [pow_zero, one_mul]

theorem ae_real_of_ae_physical {p : PhysicalCircle → Prop}
    (h : ∀ᵐ y ∂spatialMeasure, p y) : ∀ᵐ t : ℝ, p (t : PhysicalCircle) := by
  have h1 : ∀ᵐ x ∂NlsGge.Schur.spectralHaar, p (NlsGge.Analysis.naturalPhysicalCover x) :=
    NlsGge.Analysis.naturalPhysicalCover_preserving.quasiMeasurePreserving.ae h
  have h2 := ae_real_of_ae_spectral h1
  simpa only [NlsGge.Analysis.naturalPhysicalCover_coe] using h2

theorem sobolevPointValue_ae (m : ℕ)
    (u : PhysicalSobolev38 (m : ℝ)) :
  (fun x : ℝ => sobolevPointValue m u x) =ᵐ[volume]
    coverRep38 (physicalSobolevEmbed m u) := by
  by_cases hm : 1 ≤ m
  · have hc : ∀ᵐ y ∂spatialMeasure,
        (physicalSobolevEmbed m u : PhysicalCircle → ℂ) y =
          physicalSobolevContinuous38 m hm u y := by
      have := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) spatialMeasure
        (physicalSobolevContinuous38 m hm u)
      rw [physicalSobolevContinuous38_toLp] at this
      exact this
    have h1 := ae_real_of_ae_physical hc
    filter_upwards [h1, coverRep38_ae_phys (physicalSobolevEmbed m u)] with t ht1 ht2
    simp only [sobolevPointValue, hm, dite_true]
    rw [ht2, ht1]
  · exact Filter.EventuallyEq.of_eq (by funext x; simp [sobolevPointValue, hm])

end NlsGge.GKDefinitionDesign

