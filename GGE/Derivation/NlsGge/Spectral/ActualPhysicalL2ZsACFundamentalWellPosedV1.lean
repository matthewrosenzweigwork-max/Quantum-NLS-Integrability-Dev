import NlsGge.Spectral.ActualPhysicalL2ZsVolterraSolutionIdentificationV3
import NlsGge.Spectral.ActualPhysicalL2ZsDysonAEODEV2
import NlsGge.Spectral.ComplexAbsolutelyContinuousAEODEIntegralIdentityV1
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-- The actual Dyson matrix realizes the normalized rough-field fundamental
solution: initial identity, entrywise absolute continuity and the genuine
ZS equation almost everywhere on the doubled interval. -/
theorem actualPhysicalL2ZsDysonTsum_is_AC_fundamental
    (u : PhysicalL2) (z : ℂ) :
    actualComplexZsDysonTsum
      (fun x => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (x : SpectralCircle)) z 0 = 1 ∧
    (∀ i j : Fin 2, AbsolutelyContinuousOnInterval (fun t => actualComplexZsDysonTsum
      (fun x => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (x : SpectralCircle)) z t i j) 0 2) ∧
    (∀ i j : Fin 2, ∀ᵐ t ∂volume, t ∈ Set.uIcc (0 : ℝ) 2 →
      HasDerivAt (fun s => actualComplexZsDysonTsum
        (fun x => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (x : SpectralCircle)) z s i j)
        ((zsCoefficientComplex
          (fun x => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (x : SpectralCircle)) z t *
          actualComplexZsDysonTsum
            (fun x => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (x : SpectralCircle))
            z t) i j) t) := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    exact actualPhysicalL2ZsDysonTsum_initial_entry u z i j
  · exact fun i j => absolutelyContinuous_actualPhysicalL2ZsDysonTsum_entry u z i j
  · exact fun i j => actualPhysicalL2ZsDysonTsum_ae_hasDerivAt_entry u z i j

/-- Every normalized AC solution of the actual rough-L² ZS system agrees
with the constructed Dyson matrix on the full doubled interval. Its initial
condition, regularity and AE equation are explicit hypotheses, all realized
by the preceding theorem. No spectral geometry conclusion is assumed. -/
theorem actualPhysicalL2Zs_AC_fundamental_eq_Dyson
    (u : PhysicalL2) (z : ℂ)
    (F : ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (hinit : F 0 = 1)
    (hAC : ∀ i j : Fin 2, AbsolutelyContinuousOnInterval (fun t => F t i j) 0 2)
    (hODE : ∀ i j : Fin 2, ∀ᵐ t ∂volume, t ∈ Set.uIcc (0 : ℝ) 2 →
      HasDerivAt (fun s => F s i j)
        ((zsCoefficientComplex
          (fun x => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (x : SpectralCircle))
          z t * F t) i j) t) :
    ∀ t ∈ Set.Icc (0 : ℝ) 2,
      F t = actualComplexZsDysonTsum
        (fun x => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (x : SpectralCircle)) z t := by
  have hF : ContinuousOn F (Set.Icc (0 : ℝ) 2) := by
    apply continuousOn_pi.2
    intro i
    apply continuousOn_pi.2
    intro j
    simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using (hAC i j).continuousOn
  apply actualPhysicalL2ZsVolterraSolution_eq_Dyson u z F hF
  intro t ht i j
  have hg := actualPhysicalL2ZsProductContinuousState_intervalIntegrable u z F hF i j
  have hid := complex_absolutelyContinuous_eq_initial_add_integral_of_ae_hasDerivAt
    (hAC i j) hg (hODE i j)
  have htu : t ∈ Set.uIcc (0 : ℝ) 2 := by
    simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using ht
  have h := hid t htu
  have hi := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M i j) hinit
  rw [hi] at h
  exact h
end NlsGge.SpectralFoundations
end
