import NlsGge.Birkhoff.S01Translation38

                                                                                                      
                                                                                                                                  
                                                                                                                                
                                                                 
                                                                                                              
set_option autoImplicit false
open NlsGge.Birkhoff

namespace NlsGge.ThirdConsultation.PDE
noncomputable section

def D (F : (ℤ → ℂ) → ℝ) (x v : ℤ → ℂ) : ℝ :=
  deriv (fun s : ℝ => F (fun n : ℤ => x n + (s : ℂ) * v n)) 0

theorem coordinate_translation_hamiltonian_hasDerivAt
    (x v : ℤ → ℂ)
    (hx : x ∈ seqSobolev38 (1 : ℝ))
    (hv : v ∈ seqSobolev38 (1 : ℝ)) :
    HasDerivAt
      (fun s : ℝ =>
        Real.pi * momSeq38 (fun n : ℤ => x n + (s : ℂ) * v n))
      (stdSymplectic38 (canField38 x) v) 0 := by
  have hx' : x ∈ seqSobolev38 ((1 : ℕ) : ℝ) := by simpa using hx
  have hv' : v ∈ seqSobolev38 ((1 : ℕ) : ℝ) := by simpa using hv
  exact canonical_hamilton38 x v hx' hv'

theorem coordinate_translation_hamiltonian
    (x v : ℤ → ℂ)
    (hx : x ∈ seqSobolev38 (1 : ℝ))
    (hv : v ∈ seqSobolev38 (1 : ℝ)) :
    D (fun y : ℤ → ℂ => Real.pi * momSeq38 y) x v =
      stdSymplectic38 (canField38 x) v := by
  unfold D
  exact (coordinate_translation_hamiltonian_hasDerivAt x v hx hv).deriv

end
end NlsGge.ThirdConsultation.PDE
