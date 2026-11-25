import NlsGge.GK38.EigenvalueCompactnessDirectionRatios
import NlsGge.GK38.EigenvalueCompactnessPhaseConnected
import NlsGge.GK38.EigenvalueCompactnessPhaseDiscrete

/-! # S7: winding independence for nonscalar and signed-identity endpoints -/
set_option autoImplicit false
open Set Metric
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem periodicPhase_direction_independent38 (u : PhysicalL2) (x : ℝ) (n : ℤ) (a b : ℂ)
    (ha : EigenDirectionAt38 u x n a) (hb : EigenDirectionAt38 u x n b) :
    periodicPhase38 u x a 1 = periodicPhase38 u x b 1 := by
  by_cases hM : monodromyPair (realSlice u) (x : ℂ) =
      (Real.cos ((n : ℝ) * Real.pi) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
  · apply continuous_halfturn_constant38 (sphere 0 1) complex_unit_circle_preconnected38
      (fun c : ℂ => periodicPhase38 u x c 1) (periodicPhase_direction_continuous38 u x)
    · intro c hc
      have hu : ‖c‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hc
      have he : EigenDirectionAt38 u x n c := by
        refine ⟨hu, ?_⟩
        rw [hM, Matrix.smul_mulVec, Matrix.one_mulVec]
      obtain ⟨m, hm, _⟩ := periodicPhase_discrete38 u x n c he
      exact ⟨m, hm⟩
    · simpa only [mem_sphere, dist_zero_right] using ha.1
    · simpa only [mem_sphere, dist_zero_right] using hb.1
  · exact periodicPhase_nonscalar_direction_eq38 u x n a b ha hb hM

end
end NlsGge.GK38
