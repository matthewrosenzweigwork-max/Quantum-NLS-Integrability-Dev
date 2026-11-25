import NlsGge.Ramer.RamerStep5

                                                                                                            
                                                                                                        
                                                                                                                                
                                                                                                                        
                                                                                                                          
                                                                                                                                

set_option autoImplicit false
open NlsGge.Pilot

namespace NlsGge.ThirdConsultation.R
noncomputable section

theorem exists_tail_small {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ) (hs : 0 < s)
    (M ε : ℝ) (hM : 0 < M) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ h : NlsGge.Ramer.ActualCM c, ‖h‖ ≤ M →
      ‖cmToFullWeightedHilbert c s hs.le
        (h - ((NlsGge.Ramer.cmTrunc c N h : NlsGge.Ramer.actualCMHead c N) : NlsGge.Ramer.ActualCM c))‖ ≤ ε := by
  obtain ⟨n₀, hn₀⟩ := NlsGge.Ramer.exists_tail_small c s hs (M + 1) ε hε
  refine ⟨n₀, fun h hh => ?_⟩
  rw [map_sub]
  have hlt := hn₀ n₀ le_rfl h (by linarith)
  exact hlt.le.trans (by linarith)

end
end NlsGge.ThirdConsultation.R
