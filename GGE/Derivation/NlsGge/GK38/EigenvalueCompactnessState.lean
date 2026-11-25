import NlsGge.GK38.EigenvalueCompactnessDefs
import NlsGge.Spectral.ActualRealParameterDysonConjugationV3

/-! # S7: actual real initial states have nonvanishing first component

Unit directions are a special case of nonzero real initial directions.
-/
set_option autoImplicit false
open Filter Topology Set Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

def periodicState38 (u : PhysicalL2) (x : ℝ) (a : ℂ) (t : ℝ) : Fin 2 → ℂ :=
  actualPhysicalFloquetState33 u (x : ℂ) (realInitial38 a) t

theorem real_matrix_state_star38 (M : Matrix (Fin 2) (Fin 2) ℂ)
    (h0 : star (M 0 0) = M 1 1) (h1 : star (M 0 1) = M 1 0) (a : ℂ) :
    (M.mulVec (realInitial38 a)) 1 = star ((M.mulVec (realInitial38 a)) 0) := by
  simp only [realInitial38, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, star_add, star_mul, star_star]
  rw [h0, h1]
  ring

theorem periodicState_star38 (u : PhysicalL2) (x : ℝ) (a : ℂ) (t : ℝ) :
    periodicState38 u x a t 1 = star (periodicState38 u x a t 0) := by
  change (actualComplexZsDysonTsum (e02Pot38 u) (x : ℂ) t).mulVec (realInitial38 a) 1 =
    star ((actualComplexZsDysonTsum (e02Pot38 u) (x : ℂ) t).mulVec (realInitial38 a) 0)
  apply real_matrix_state_star38
  · simpa using actualComplexZsDysonTsum_real_entry_star (e02Pot38 u) x t 0 0
  · simpa using actualComplexZsDysonTsum_real_entry_star (e02Pot38 u) x t 0 1

theorem periodicState_first_ne_zero38 (u : PhysicalL2) (x : ℝ) (a : ℂ) (ha : a ≠ 0)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 2) : periodicState38 u x a t 0 ≠ 0 := by
  intro hz
  have hs : periodicState38 u x a t = 0 := by
    funext i
    fin_cases i
    · change periodicState38 u x a t 0 = 0
      exact hz
    · change periodicState38 u x a t 1 = 0
      rw [periodicState_star38, hz, star_zero]
  have hdet := actualPhysicalL2ZsDysonTsum_det_one u (x : ℂ) t ht
  have hi := Matrix.mulVec_injective_of_det_ne_zero (by rw [hdet]; norm_num)
  have he : realInitial38 a = 0 := hi (by
    change periodicState38 u x a t = _
    simpa only [Matrix.mulVec_zero] using hs)
  exact ha (by simpa only [realInitial38, Matrix.cons_val_zero, Pi.zero_apply] using congrFun he 0)

theorem periodicState_ratio_norm38 (u : PhysicalL2) (x : ℝ) (a : ℂ) (ha : a ≠ 0)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 2) :
    ‖periodicState38 u x a t 1 / periodicState38 u x a t 0‖ = 1 := by
  rw [periodicState_star38, norm_div, norm_star]
  exact div_self (norm_ne_zero_iff.mpr (periodicState_first_ne_zero38 u x a ha t ht))

end
end NlsGge.GK38
