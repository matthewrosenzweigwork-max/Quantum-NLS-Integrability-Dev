                                                                                                                                              
import NlsGge.NLS38.Functionals38

                                                                                    
                                                                                                    
                                                                                          
                                                                                                      
                                             

set_option autoImplicit false
open NlsGge.NLS38 NlsGge.Birkhoff

namespace NlsGge.ThirdConsultation.PDE
noncomputable section

def massH1 (x : H1C38) : ℝ := mass (carrierCoe38 ((1 : ℕ) : ℝ) x)

def hamH1 (x : H1C38) : ℝ := ham (carrierCoe38 ((1 : ℕ) : ℝ) x)

theorem mass_hamiltonian_continuous :
    Continuous massH1 ∧ Continuous hamH1 ∧
    ∀ x : H1C38, 0 ≤ quart (carrierCoe38 ((1 : ℕ) : ℝ) x) ∧
      quart (carrierCoe38 ((1 : ℕ) : ℝ) x) ≤
        C1 ^ 2 * (hn 1 (carrierCoe38 ((1 : ℕ) : ℝ) x)) ^ 4 := by
  refine ⟨continuous_mass_coe, continuous_ham_coe, fun x => ?_⟩
  have hmem := carrierCoe38_mem ((1 : ℕ) : ℝ) x
  have hrt : carrierMk38 ((1 : ℕ) : ℝ) (carrierCoe38 ((1 : ℕ) : ℝ) x) hmem = x := rfl
  have hnorm : ‖x‖ = hn 1 (carrierCoe38 ((1 : ℕ) : ℝ) x) := by
    have h := norm_carrierMk38_eq_hn 1 (carrierCoe38 ((1 : ℕ) : ℝ) x) hmem
    rw [hrt] at h
    exact h
  have hq : quart (carrierCoe38 ((1 : ℕ) : ℝ) x) = ‖convMk x x‖ ^ 2 := by
    unfold quart
    exact (norm_sq_convMk x x).symm
  have hC := norm_convMk_le x x
  refine ⟨?_, ?_⟩
  · rw [hq]
    positivity
  · rw [hq, ← hnorm]
    have h0 : 0 ≤ ‖convMk x x‖ := norm_nonneg _
    calc ‖convMk x x‖ ^ 2 ≤ (C1 * ‖x‖ * ‖x‖) ^ 2 := pow_le_pow_left₀ h0 hC 2
      _ = C1 ^ 2 * ‖x‖ ^ 4 := by ring

end
end NlsGge.ThirdConsultation.PDE
