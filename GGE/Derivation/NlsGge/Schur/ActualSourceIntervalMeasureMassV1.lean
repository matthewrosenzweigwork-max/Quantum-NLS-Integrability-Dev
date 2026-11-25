import NlsGge.Schur.SourceInterval
import Mathlib.Tactic

set_option autoImplicit false

open MeasureTheory

namespace NlsGge.Schur

/-- The actual source-interval restriction of Lebesgue measure has unit mass. -/
theorem actualSourceIntervalMeasure_univNNReal :
    measureUnivNNReal (volume.restrict (Set.Ioc (0 : ℝ) 1)) = 1 := by
  change ((volume.restrict (Set.Ioc (0 : ℝ) 1)) Set.univ).toNNReal = 1
  rw [Measure.restrict_apply_univ, Real.volume_Ioc]
  norm_num

end NlsGge.Schur
