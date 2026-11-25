                                                                                                 
                                                                                                                                  
                                                                                                                                               
                                                                                                                                               
import Mathlib
import NlsGge.Atomic.T.T029

set_option autoImplicit false

namespace NlsGge.ThirdConsultation.T
noncomputable section

def h2Tilt (c : ℕ → ℝ) (δ : ℝ) (j : ℕ) : ℝ :=
  c j - (if j = 0 then δ else if j = 2 then 16 * δ else 0)

theorem h2Tilt_numerator_bounds (cMinus cPlus : ℝ) (W : ℕ → ℝ)
    (hW : WeightClass cMinus cPlus W) :
    WeightClass (3 * cMinus / 4) cPlus (h2Tilt W (cMinus / 64)) := by
  obtain ⟨hpos, hle, hb⟩ := hW
  refine ⟨by linarith, by linarith, fun j => ?_⟩
  obtain ⟨hlo, hup⟩ := hb j
  unfold h2Tilt
  split_ifs <;> constructor <;> linarith

end
end NlsGge.ThirdConsultation.T
