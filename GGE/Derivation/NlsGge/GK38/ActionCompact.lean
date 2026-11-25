import NlsGge.GK38.ActionCompactIntegral

/-! # A4 real helper: weak sequential continuity of actual labelled actions

GK I.13, Proposition 13.2 real-integral component. Every integer label is
retained. Identification with the source complex contour waits for A2.
-/
set_option autoImplicit false
open Filter Topology Set Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

theorem gapAction_weak_tendsto38 (u : ℕ → PhysicalL2) (u₀ : PhysicalL2)
    (hw : IsWeakLim u u₀) (n : ℤ) :
    Tendsto (fun k => actualGapActionAllE02_38 (u k) n) atTop
      (𝓝 (actualGapActionAllE02_38 u₀ n)) := by
  have _hi (v : PhysicalL2) := gapAction_intervalIntegrable_L2_38 v n
  simpa only [one_mul, actualGapActionAllE02_38] using
    gapWeighted_weak_tendsto38 u u₀ hw (fun _ => 1) continuous_const n

end
end NlsGge.GK38
