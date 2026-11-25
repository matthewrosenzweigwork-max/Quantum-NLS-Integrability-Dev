import NlsGge.Composition.Main

                                                                                                                                 
                                                                                                                        
                                                                                                                                 
                                                   
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.R
noncomputable section
open NlsGge.Composition

theorem r094_srcWeight_composition_analytic {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [CompleteSpace X] [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
    {a : ℝ} (ha : 0 < a) (b : ℝ) {F : X → Y} {O : Set X} (hO : IsOpen O)
    (hF : AnalyticOnNhd ℝ F O) :
    AnalyticOnNhd ℝ (compMap (srcWeight_admissible ha b) F) (rangeSet (srcWeight a b) O) :=
  (NlsGge.Composition.srcWeight_composition_analytic ha b hO hF).2.1

end
end NlsGge.ThirdConsultation.R
