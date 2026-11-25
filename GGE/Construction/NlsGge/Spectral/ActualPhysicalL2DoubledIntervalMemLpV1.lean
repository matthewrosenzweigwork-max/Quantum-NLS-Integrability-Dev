import NlsGge.Analysis.NaturalCover
import NlsGge.Schur.SourceInterval
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace NlsGge.Schur
open NlsGge.Pilot NlsGge.Analysis

abbrev actualDoubledSourceMeasure : Measure ℝ :=
  volume.restrict (Set.Ioc (0 : ℝ) 2)

/-- The actual physical L² class pulled back through the degree-two cover is
L² on the entire doubled source interval `(0,2]`. -/
theorem naturalPhysicalCoverL2_memLp_doubledInterval (u : PhysicalL2) :
    MemLp
      (fun t : ℝ =>
        (naturalPhysicalCoverL2 u : SpectralCircle → ℂ)
          (t : SpectralCircle))
      2 actualDoubledSourceMeasure := by
  let F : SpectralCircle → ℂ := naturalPhysicalCoverL2 u
  have hF : MemLp F 2 (volume : Measure SpectralCircle) :=
    (Lp.memLp (naturalPhysicalCoverL2 u)).of_haarAddCircle
  have hpull : MemLp (fun t : ℝ => F (t : SpectralCircle)) 2
      actualDoubledSourceMeasure := by
    simpa only [actualDoubledSourceMeasure, Function.comp_def, zero_add] using
      hF.comp_measurePreserving (AddCircle.measurePreserving_mk (2 : ℝ) 0)
  simpa only [F] using hpull

/-- The same actual representative is integrable on the full doubled source
interval. This uses finiteness of the interval measure and L²-to-L¹ inclusion. -/
theorem naturalPhysicalCoverL2_integrable_doubledInterval (u : PhysicalL2) :
    Integrable
      (fun t : ℝ =>
        (naturalPhysicalCoverL2 u : SpectralCircle → ℂ)
          (t : SpectralCircle))
      actualDoubledSourceMeasure := by
  letI : IsFiniteMeasure actualDoubledSourceMeasure := by
    dsimp [actualDoubledSourceMeasure]
    exact Real.isFiniteMeasure_restrict_Ioc 0 2
  have hmem := naturalPhysicalCoverL2_memLp_doubledInterval u
  have hmem₁ : MemLp
      (fun t : ℝ =>
        (naturalPhysicalCoverL2 u : SpectralCircle → ℂ)
          (t : SpectralCircle))
      1 actualDoubledSourceMeasure :=
    hmem.mono_exponent (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  exact memLp_one_iff_integrable.mp hmem₁

/-- The doubled-interval representative is interval-integrable, with no
continuity or boundedness premise on the physical field. -/
theorem naturalPhysicalCoverL2_intervalIntegrable_doubled (u : PhysicalL2) :
    IntervalIntegrable
      (fun t : ℝ =>
        (naturalPhysicalCoverL2 u : SpectralCircle → ℂ)
          (t : SpectralCircle))
      volume 0 2 := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le
    (by norm_num : (0 : ℝ) ≤ 2)).mpr
  simpa only [IntegrableOn, actualDoubledSourceMeasure] using
    naturalPhysicalCoverL2_integrable_doubledInterval u

end NlsGge.Schur

end
