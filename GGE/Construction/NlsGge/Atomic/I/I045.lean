import NlsGge.Hierarchy.FullEnergyPlaneConvergence38

                                                                                             
                                                                                                                  
                                                                                             
                                                                                                               
                                                                                                            
                                                                                       

set_option autoImplicit false
open NlsGge.HierarchyRiccati.Core

namespace NlsGge.ThirdConsultation.I
noncomputable section

theorem l1Poly38_p_one : l1Poly38 (p 1) = 1 := by
  rw [p_one]
  unfold l1Poly38
  simp [MvPolynomial.support_X, MvPolynomial.coeff_X']

theorem i045 :
    l1Poly38 (p 1) = 1 ∧
    ∀ k : ℕ, 1 ≤ k →
      l1Poly38 (p (k + 1)) ≤ (k : ℤ) * l1Poly38 (p k) +
        ∑ l ∈ Finset.Icc 1 (k - 1), l1Poly38 (p (k - l)) * l1Poly38 (p l) ∧
      l1Poly38 (p k) ≤ (4 : ℤ) ^ (k - 1) * ((k - 1).factorial : ℤ) := by
  refine ⟨l1Poly38_p_one, fun k hk => ⟨?_, ?_⟩⟩
  · obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
    have h := l1Poly38_p_succ n
    simpa using h
  · unfold l1Poly38
    exact riccati_p_abs_coeff_sum_le38 k hk

end
end NlsGge.ThirdConsultation.I
