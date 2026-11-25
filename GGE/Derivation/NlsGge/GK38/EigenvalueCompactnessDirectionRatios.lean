import NlsGge.GK38.EigenvalueCompactnessDirectionAlgebra
import NlsGge.GK38.EigenvalueCompactnessPhaseIntegrable

/-! # S7: phase equality in a nonscalar real eigenspace -/
set_option autoImplicit false
open Set MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

theorem periodicPhase_wedge_eq38 (u : PhysicalL2) (x : ℝ) (a b : ℂ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hw : a * star b - b * star a = 0) :
    periodicPhase38 u x a 1 = periodicPhase38 u x b 1 := by
  have _hia := periodicPhase_intervalIntegrable38 u x a ha ⟨1, zero_le_one, le_rfl⟩
  have _hib := periodicPhase_intervalIntegrable38 u x b hb ⟨1, zero_le_one, le_rfl⟩
  unfold periodicPhase38
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 2 := by
    rw [uIcc_of_le zero_le_one] at ht
    exact ⟨ht.1, ht.2.trans (by norm_num)⟩
  have hratio := real_matrix_state_ratio38 (actualComplexZsDysonTsum (e02Pot38 u) (x : ℂ) t) a b hw
    (periodicState_first_ne_zero38 u x a (unit_direction_ne_zero38 a ha) t ht')
    (periodicState_first_ne_zero38 u x b (unit_direction_ne_zero38 b hb) t ht')
  change periodicState38 u x a t 1 / periodicState38 u x a t 0 =
    periodicState38 u x b t 1 / periodicState38 u x b t 0 at hratio
  change (e02Pot38 u t * (periodicState38 u x a t 1 / periodicState38 u x a t 0)).re =
    (e02Pot38 u t * (periodicState38 u x b t 1 / periodicState38 u x b t 0)).re
  rw [hratio]

theorem periodicPhase_nonscalar_direction_eq38 (u : PhysicalL2) (x : ℝ) (n : ℤ) (a b : ℂ)
    (ha : EigenDirectionAt38 u x n a) (hb : EigenDirectionAt38 u x n b)
    (hM : monodromyPair (realSlice u) (x : ℂ) ≠
      (Real.cos ((n : ℝ) * Real.pi) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) :
    periodicPhase38 u x a 1 = periodicPhase38 u x b 1 := by
  have hw := (real_eigenvectors_wedge_or_scalar38 _ _ a b ha.2 hb.2).resolve_right hM
  exact periodicPhase_wedge_eq38 u x a b ha.1 hb.1 hw

end
end NlsGge.GK38
