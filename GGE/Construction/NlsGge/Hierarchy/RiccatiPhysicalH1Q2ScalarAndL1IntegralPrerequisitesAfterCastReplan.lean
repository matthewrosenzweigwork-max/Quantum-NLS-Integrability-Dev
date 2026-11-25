import NlsGge.Definitions.PilotInterfaces
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace NlsGge.Pilot

open MeasureTheory

local instance : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure
  infer_instance

theorem complex_quartic_real_identity_afterCastReplan (z : ℂ) :
    Complex.re (((starRingEnd ℂ) z * z) ^ 2) = ‖z‖ ^ 4 := by
  rw [Complex.conj_mul']
  rw [← Complex.ofReal_pow]
  rw [← Complex.ofReal_pow]
  simp only [Complex.ofReal_re]
  ring

theorem continuousMap_L1_integral_eq_integralCLM_afterCastReplan :
    (fun f : C(PhysicalCircle, ℂ) =>
      MeasureTheory.L1.integral ((ContinuousMap.toLp 1 spatialMeasure ℂ) f)) =
    (fun f : C(PhysicalCircle, ℂ) =>
      MeasureTheory.L1.integralCLM (α := PhysicalCircle) (E := ℂ) (μ := spatialMeasure)
        ((ContinuousMap.toLp 1 spatialMeasure ℂ) f)) := by
  funext f
  exact MeasureTheory.L1.integral_eq _

end NlsGge.Pilot
