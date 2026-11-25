import Mathlib
import NlsGge.Atomic.AL.AL080
import NlsGge.Hierarchy.ALCorrector38

                                                                               
                                                                                                            
                                              
                                                                                                            
                                                                                                          
                                                                                                         
set_option autoImplicit false

open NlsGge.Pilot NlsGge.AblowitzLadik NlsGge.Weights Filter Topology

namespace NlsGge.ThirdConsultation.AL

theorem al087 (lower upper : ℝ) (c : BoundedCoefficients lower upper) (N : ℕ)
    (hpos : ∀ k : ℤ, |k| ≤ (N : ℤ) → 0 < alRateFree38 c.val N k) :
    let D : FourierPlane N → FourierPlane N := fun z i =>
      (alCorrMul38 c.val N (modeIndex N i) : ℂ) * z i
    let Di : FourierPlane N → FourierPlane N := fun z i =>
      (alCorrInvMul38 c.val N (modeIndex N i) : ℂ) * z i
    (∀ g : ℤ → ℂ,
      alCorrCoef38 c.val N (alUhCoef38 c.val N g) = alPNUCoef38 c.val N g ∧
      alCorrInvCoef38 c.val N (alPNUCoef38 c.val N g) = alUhCoef38 c.val N g) ∧
    Function.LeftInverse Di D ∧ Function.RightInverse Di D := by
  intro D Di
  have hA := al080Aux.admissible c
  have hmul : ∀ i : Fin (2 * N + 1),
      (alCorrInvMul38 c.val N (modeIndex N i) : ℂ) * (alCorrMul38 c.val N (modeIndex N i) : ℂ) = 1 := by
    intro i
    have hb := modeIndex_bounds N i
    have hk : |modeIndex N i| ≤ (N : ℤ) := abs_le.2 ⟨hb.1, hb.2⟩
    have hf := hpos _ hk
    have hc : 0 < alRateCont38 c.val (modeIndex N i) :=
      (alRateComp_pos38 hA _).trans_le (alRateComp_le_cont38 hA _)
    unfold alCorrInvMul38 alCorrMul38
    rw [if_pos hk, if_pos hk, ← Complex.ofReal_mul, ← Real.sqrt_mul (div_nonneg hc.le hf.le)]
    have hprod : alRateCont38 c.val (modeIndex N i) / alRateFree38 c.val N (modeIndex N i) *
        (alRateFree38 c.val N (modeIndex N i) / alRateCont38 c.val (modeIndex N i)) = 1 := by
      field_simp
    rw [hprod, Real.sqrt_one, Complex.ofReal_one]
  have hmul' : ∀ i : Fin (2 * N + 1),
      (alCorrMul38 c.val N (modeIndex N i) : ℂ) * (alCorrInvMul38 c.val N (modeIndex N i) : ℂ) = 1 :=
    fun i => by rw [mul_comm]; exact hmul i
  refine ⟨fun g => ⟨alCorr_Uh_coef38 hA N hpos g, alCorrInv_PNU_coef38 hA N hpos g⟩, ?_, ?_⟩
  · intro z
    funext i
    simp only [D, Di]
    rw [← mul_assoc, hmul i, one_mul]
  · intro z
    funext i
    simp only [D, Di]
    rw [← mul_assoc, hmul' i, one_mul]

end NlsGge.ThirdConsultation.AL
