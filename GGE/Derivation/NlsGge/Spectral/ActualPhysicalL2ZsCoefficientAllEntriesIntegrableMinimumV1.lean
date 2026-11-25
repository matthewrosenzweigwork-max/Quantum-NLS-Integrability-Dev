import NlsGge.Spectral.ActualPhysicalL2DoubledIntervalMemLpV1
import NlsGge.Spectral.FreeZakharovShabatFundamentalComplexV4
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Analysis.Matrix.Normed

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Matrix.Norms.Elementwise

namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-- The actual physical L² coefficient on the complete doubled source interval.
Its lower-left entry is `-i * star u`; no representative continuity is assumed. -/
def actualPhysicalL2ZsCoefficient (u : PhysicalL2) (z : ℂ) (t : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  zsCoefficientComplex
    (fun s => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (s : SpectralCircle)) z t

/-- Every one of the four actual rough physical coefficient entries is L¹ on `[0,2]`.
This is only the coefficient realization, not the Volterra fundamental matrix,
its a.e. differential equation, monodromy trace or any spectral/action claim. -/
theorem actualPhysicalL2ZsCoefficient_all_entries_intervalIntegrable
    (u : PhysicalL2) (z : ℂ) (i j : Fin 2) :
    IntervalIntegrable (fun t => actualPhysicalL2ZsCoefficient u z t i j) volume 0 2 := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 2)).mpr
  let U : ℝ → ℂ := fun t =>
    (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (t : SpectralCircle)
  have hU : Integrable U actualDoubledSourceMeasure :=
    naturalPhysicalCoverL2_integrable_doubledInterval u
  have hstar : Integrable (fun t => star (U t)) actualDoubledSourceMeasure := by
    exact ((starL ℝ : ℂ ≃L⋆[ℝ] ℂ).toContinuousLinearMap).integrable_comp hU
  have hconst (c : ℂ) : Integrable (fun _ : ℝ => c) actualDoubledSourceMeasure := by
    letI : IsFiniteMeasure actualDoubledSourceMeasure := by
      dsimp [actualDoubledSourceMeasure]
      exact Real.isFiniteMeasure_restrict_Ioc 0 2
    exact integrable_const c
  fin_cases i <;> fin_cases j
  · change Integrable (fun _ : ℝ => -Complex.I * z) actualDoubledSourceMeasure
    exact hconst _
  · change Integrable (fun t => Complex.I * U t) actualDoubledSourceMeasure
    exact hU.const_mul _
  · change Integrable (fun t => -Complex.I * star (U t)) actualDoubledSourceMeasure
    exact hstar.const_mul _
  · change Integrable (fun _ : ℝ => Complex.I * z) actualDoubledSourceMeasure
    exact hconst _

end NlsGge.SpectralFoundations
end
