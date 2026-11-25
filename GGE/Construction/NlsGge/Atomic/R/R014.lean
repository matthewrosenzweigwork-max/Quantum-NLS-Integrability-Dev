import NlsGge.Ramer.General.RamerDensityG

                                                                                                                      
                                                                                                                  
                                                                                                            
                                                                                                                    
                                                                                           
                                                                                                           

set_option autoImplicit false

namespace NlsGge.ThirdConsultation.R
noncomputable section

theorem continuous_hsDerivH (S : NlsGge.Ramer.General.RamerSetting) {K : S.E → S.H}
    (hK : ContDiff ℝ 1 K) :
    Continuous (fun x => S.hsDerivH K x) :=
  NlsGge.Ramer.General.RamerSetting.continuous_hsDerivH S K hK

end
end NlsGge.ThirdConsultation.R
