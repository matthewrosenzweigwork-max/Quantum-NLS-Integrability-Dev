import NlsGge.Measure.ActualPhysicalBoundedHeightAmplitudeLp1Prerequisite35V3
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace NlsGge.SpectralFoundations
open NlsGge.Pilot NlsGge.Schur NlsGge.Analysis

/-- The primitive of the norm of the actual physical source-interval L²
representative. -/
def actualPhysicalSourceNormPrimitive35V2 (u : PhysicalL2) (s : ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..s, ‖actualPhysicalL2SourcePotential u r‖

/-- The actual source norm is interval-integrable on the correctly normalized
period-one source interval. -/
theorem actualPhysicalSourceNormIntervalIntegrable35V2 (u : PhysicalL2) :
    IntervalIntegrable (fun r : ℝ => ‖actualPhysicalL2SourcePotential u r‖)
      volume 0 1 := by
  let μ₁ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  haveI : IsFiniteMeasure μ₁ := by
    dsimp [μ₁]
    exact Real.isFiniteMeasure_restrict_Ioc 0 1
  have hU₂ : MemLp (actualPhysicalL2SourcePotential u) 2 μ₁ :=
    Lp.memLp (actualPhysicalL2SourcePotential u)
  have hU : Integrable (actualPhysicalL2SourcePotential u) μ₁ :=
    hU₂.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hnorm : Integrable (fun r : ℝ => ‖actualPhysicalL2SourcePotential u r‖) μ₁ :=
    hU.norm
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  simpa only [IntegrableOn, μ₁] using hnorm

/-- The actual source-norm primitive is continuous on the physical endpoint
interval. No continuity of the source representative is used. -/
theorem actualPhysicalSourceNormPrimitive35V2_continuousOn
    (u : PhysicalL2) :
    ContinuousOn (actualPhysicalSourceNormPrimitive35V2 u) (Set.Icc (0 : ℝ) 1) := by
  have hcont := intervalIntegral.continuousOn_primitive_interval'
    (a := (0 : ℝ)) (b₁ := (0 : ℝ)) (b₂ := (1 : ℝ))
    (f := fun r : ℝ => ‖actualPhysicalL2SourcePotential u r‖)
    (μ := volume) (actualPhysicalSourceNormIntervalIntegrable35V2 u)
    (Set.left_mem_uIcc : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) 1)
  change ContinuousOn
    (fun s : ℝ => ∫ r in (0 : ℝ)..s, ‖actualPhysicalL2SourcePotential u r‖)
    (Set.Icc (0 : ℝ) 1)
  rw [← Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact hcont

end NlsGge.SpectralFoundations
end
