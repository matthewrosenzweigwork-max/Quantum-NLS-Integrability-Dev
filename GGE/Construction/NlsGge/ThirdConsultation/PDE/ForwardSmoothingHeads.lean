import Mathlib
import NlsGge.ThirdConsultation.PDE.ForwardSmoothing
import NlsGge.ThirdConsultation.PDE.BirkhoffRealization

                                                                                                                  
                                                                                                                    
                                                                                                                   
                                                                 
set_option autoImplicit false
open Set
open NlsGge.Sobolev38 NlsGge.Birkhoff
namespace NlsGge.ThirdConsultation.PDE
noncomputable section

theorem actualT38_smooth
    (r : ℕ) (hr : 1 ≤ r) :
    ∀ x ∈ seqSobolev38 (r : ℝ),
      actualBirkhoffInput38.T x - x ∈
        seqSobolev38 ((r + 1 : ℕ) : ℝ) :=
  actualT38_smooth_top r hr

theorem actualT38_analytic_smooth
    (r : ℕ) (hr : 1 ≤ r) :
    AnalyticOnNhd ℝ
      (carrierMap38 (r : ℝ) ((r + 1 : ℕ) : ℝ)
        (fun x => actualBirkhoffInput38.T x - x)
        (actualT38_smooth r hr)) Set.univ :=
  actualT38_analytic_smooth_top r hr

end
end NlsGge.ThirdConsultation.PDE
