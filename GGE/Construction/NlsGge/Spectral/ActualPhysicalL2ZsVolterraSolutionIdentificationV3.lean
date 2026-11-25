import NlsGge.Spectral.ActualPhysicalL2ZsHomogeneousVolterraUniquenessV1
import NlsGge.Spectral.ActualPhysicalL2ZsDysonContinuousAndACV1
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-- Actual physical-L² coefficient times any continuous matrix state is
entrywise interval integrable on the doubled interval. -/
theorem actualPhysicalL2ZsProductContinuousState_intervalIntegrable
    (u : PhysicalL2) (z : ℂ)
    (F : ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (hF : ContinuousOn F (Set.Icc (0 : ℝ) 2)) (i j : Fin 2) :
    IntervalIntegrable (fun s => (zsCoefficientComplex
      (fun x => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (x : SpectralCircle))
      z s * F s) i j) volume 0 2 := by
  have hA (k : Fin 2) := actualPhysicalL2ZsCoefficient_all_entries_intervalIntegrable u z i k
  have hFc (k : Fin 2) : ContinuousOn (fun t => F t k j) (Set.uIcc (0 : ℝ) 2) := by
    simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2), Function.comp_def] using!
      (continuous_apply j).comp_continuousOn ((continuous_apply k).comp_continuousOn hF)
  simpa only [actualPhysicalL2ZsCoefficient, Matrix.mul_apply, Fin.sum_univ_two] using!
    ((hA 0).mul_continuousOn (hFc 0)).add ((hA 1).mul_continuousOn (hFc 1))

/-- Any continuous solution of the actual normalized rough-L² Volterra
equation agrees with the constructed Dyson matrix. The conclusion is
realized by the actual coefficient, not by an abstract structure assuming
uniqueness or spectral identification. -/
theorem actualPhysicalL2ZsVolterraSolution_eq_Dyson
    (u : PhysicalL2) (z : ℂ)
    (F : ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (hF : ContinuousOn F (Set.Icc (0 : ℝ) 2))
    (hVolterra : ∀ t ∈ Set.Icc (0 : ℝ) 2, ∀ i j : Fin 2,
      F t i j = (1 : Matrix (Fin 2) (Fin 2) ℂ) i j +
        ∫ s in (0 : ℝ)..t,
          (zsCoefficientComplex
            (fun x => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (x : SpectralCircle))
            z s * F s) i j) :
    ∀ t ∈ Set.Icc (0 : ℝ) 2,
      F t = actualComplexZsDysonTsum
        (fun x => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (x : SpectralCircle))
        z t := by
  let U : ℝ → ℂ := fun x =>
    (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (x : SpectralCircle)
  let X : ℝ → Matrix (Fin 2) (Fin 2) ℂ := actualComplexZsDysonTsum U z
  let H : ℝ → Matrix (Fin 2) (Fin 2) ℂ := fun t => F t - X t
  have hX : ContinuousOn X (Set.Icc (0 : ℝ) 2) :=
    continuousOn_pi.2 (fun i => continuousOn_pi.2
      (fun j => continuousOn_actualPhysicalL2ZsDysonTsum_entry u z i j))
  have hH : ContinuousOn H (Set.Icc (0 : ℝ) 2) := hF.sub hX
  have hHeq : ∀ t ∈ Set.Icc (0 : ℝ) 2, ∀ i j : Fin 2,
      H t i j = ∫ s in (0 : ℝ)..t, (zsCoefficientComplex U z s * H s) i j := by
    intro t ht i j
    have hsub : Set.uIcc (0 : ℝ) t ⊆ Set.uIcc (0 : ℝ) 2 := by
      simpa only [Set.uIcc_of_le ht.1,
        Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2), Function.comp_def] using!
        (show Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) 2 from
          fun s hs => ⟨hs.1, hs.2.trans ht.2⟩)
    have hAF := (actualPhysicalL2ZsProductContinuousState_intervalIntegrable u z F hF i j).mono_set hsub
    have hAX := (actualPhysicalL2ZsDysonProduct_intervalIntegrable u z i j).mono_set hsub
    have hproduct : (fun s => (zsCoefficientComplex U z s * H s) i j) =
        (fun s => (zsCoefficientComplex U z s * F s) i j -
          (zsCoefficientComplex U z s * X s) i j) := by
      funext s
      have hm := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M i j)
        (Matrix.mul_sub (zsCoefficientComplex U z s) (F s) (X s))
      simpa only [H] using! hm
    change F t i j - X t i j = _
    rw [hproduct, intervalIntegral.integral_sub hAF hAX]
    have hFt := hVolterra t ht i j
    have hXt := actualPhysicalL2ZsDysonTsum_integral_equationV2 u z t ht i j
    change X t i j = (1 : Matrix (Fin 2) (Fin 2) ℂ) i j +
      ∫ s in (0 : ℝ)..t, (zsCoefficientComplex U z s * X s) i j at hXt
    rw [hFt, hXt]
    ring
  have hzero := actualPhysicalL2ZsHomogeneousVolterra_continuous_eq_zero u z H hH hHeq
  intro t ht
  exact sub_eq_zero.mp (hzero t ht)
end NlsGge.SpectralFoundations
end
