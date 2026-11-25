import NlsGge.Schur.SourceInterval
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Filter
namespace NlsGge.Schur

/-- Interval-continuous actual states belong to the original unit-interval L²
carrier. A continuous clamped extension proves measurability without adding
global continuity or endpoint periodicity assumptions. -/
theorem sourceInterval_memLp_of_continuousOn
    (f : ℝ → ℂ) (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1)) :
    MemLp f 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  let c : ℝ → ℝ := fun t => max 0 (min 1 t)
  have hc : Continuous c := continuous_const.max (continuous_const.min continuous_id)
  have hcRange (t : ℝ) : c t ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  have hfc : Continuous (fun t => f (c t)) := hf.comp_continuous hc hcRange
  obtain ⟨C, hC, hbound⟩ :=
    (isCompact_Icc.image_of_continuousOn hf).isBounded.exists_pos_norm_le
  have hLp : MemLp (fun t => f (c t)) 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    MemLp.of_bound hfc.aestronglyMeasurable C (Eventually.of_forall (fun t =>
      hbound _ ⟨c t, hcRange t, rfl⟩))
  refine MemLp.ae_eq ?_ hLp
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have hct : c t = t := by
    dsimp only [c]
    rw [min_eq_right ht.2, max_eq_right ht.1.le]
  exact congrArg f hct

/-- The source L² class of an actual interval-continuous state, without any
assumed Fourier graph-domain or periodic trace conclusion. -/
def sourceIntervalL2OfContinuousOn (f : ℝ → ℂ)
    (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1)) : SourceIntervalL2 :=
  (sourceInterval_memLp_of_continuousOn f hf).toLp f

theorem sourceIntervalL2OfContinuousOn_ae
    (f : ℝ → ℂ) (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1)) :
    sourceIntervalL2OfContinuousOn f hf =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] f :=
  (sourceInterval_memLp_of_continuousOn f hf).coeFn_toLp

end NlsGge.Schur
end
