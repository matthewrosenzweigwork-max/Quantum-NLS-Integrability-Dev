import NlsGge.Schur.SourceIntervalL2FromActualContinuousOnV2
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Interval
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Filter
namespace NlsGge.Schur

/-- Continuity recovers both endpoints from an equality in the actual Ioc
interval carrier. This does not assume the endpoint lies in that carrier. -/
theorem sourceInterval_continuousOn_eq_of_ae
    (f g : ℝ → ℂ) (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (hg : ContinuousOn g (Set.Icc (0 : ℝ) 1))
    (hfg : f =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] g) :
    Set.EqOn f g (Set.Icc (0 : ℝ) 1) := by
  have hm : volume.restrict (Set.Ioc (0 : ℝ) 1) =
      volume.restrict (Set.Icc (0 : ℝ) 1) :=
    Measure.restrict_congr_set (Ioc_ae_eq_Icc'
      (μ := volume) (a := (0 : ℝ)) (b := 1) (by simp))
  rw [hm] at hfg
  exact Measure.eqOn_Icc_of_ae_eq volume (by norm_num) hfg hf hg

/-- A nonzero initial value gives a nonzero actual source L2 class, even
though the initial endpoint itself is a null set. -/
theorem sourceIntervalL2OfContinuousOn_ne_zero_of_initial
    (f : ℝ → ℂ) (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (h0 : f 0 ≠ 0) : sourceIntervalL2OfContinuousOn f hf ≠ 0 := by
  intro h
  have hz : sourceIntervalL2OfContinuousOn f hf =ᵐ[
      volume.restrict (Set.Ioc (0 : ℝ) 1)] (0 : ℝ → ℂ) :=
    Lp.eq_zero_iff_ae_eq_zero.mp h
  have hfg := (sourceIntervalL2OfContinuousOn_ae f hf).symm.trans hz
  have heq := sourceInterval_continuousOn_eq_of_ae f 0 hf continuousOn_const hfg
  exact h0 (heq (by norm_num))

end NlsGge.Schur
end
