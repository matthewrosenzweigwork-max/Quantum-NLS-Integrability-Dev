import NlsGge.Sobolev.PeriodicBridge
import Mathlib.Tactic

set_option autoImplicit false

/-! The actual Fourier isometry is complex-linear while the H¹ carrier is
real. These isolated statements make the real restriction explicit at the
genuine `lp ℂ 2` coordinate level. -/

namespace NlsGge.Pilot

theorem physicalFourierL2_map_add_actual (u v : PhysicalL2) :
    physicalFourierL2 (u + v) = physicalFourierL2 u + physicalFourierL2 v := by
  exact map_add physicalFourierL2 u v

theorem physicalFourierL2_map_real_smul_actual (r : ℝ) (u : PhysicalL2) :
    physicalFourierL2 (r • u) = (r : ℂ) • physicalFourierL2 u := by
  change physicalFourierL2 ((r : ℂ) • u) = (r : ℂ) • physicalFourierL2 u
  exact map_smul physicalFourierL2 (r : ℂ) u

theorem physicalFourierL2_map_add_actual_apply
    (u v : PhysicalL2) (n : ℤ) :
    physicalFourierL2 (u + v) n = physicalFourierL2 u n + physicalFourierL2 v n := by
  rw [physicalFourierL2_map_add_actual]
  rfl

theorem physicalFourierL2_map_real_smul_actual_apply
    (r : ℝ) (u : PhysicalL2) (n : ℤ) :
    physicalFourierL2 (r • u) n = (r : ℂ) * physicalFourierL2 u n := by
  rw [physicalFourierL2_map_real_smul_actual]
  change (((r : ℂ) • physicalFourierL2 u : lp (fun _ : ℤ => ℂ) 2) n) = _
  rfl

end NlsGge.Pilot
