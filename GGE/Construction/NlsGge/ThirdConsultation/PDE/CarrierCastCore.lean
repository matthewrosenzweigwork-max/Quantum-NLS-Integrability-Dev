import Mathlib
import NlsGge.Birkhoff.BirkhoffAPI38

                                                                                                         
                                                                                                                       
                                                                                                                    
                                                                        

set_option autoImplicit false
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff

namespace NlsGge.ThirdConsultation.PDE.CarrierCastAux

theorem carrier_cast_mem {a b : ℝ} (h : a = b) (y : SobolevCarrier38 a) :
    carrierCoe38 a y ∈ seqSobolev38 b := h ▸ carrierCoe38_mem a y

theorem carrier_cast_analytic {a b : ℝ} (h : a = b) :
    AnalyticOnNhd ℝ (fun y : SobolevCarrier38 a =>
      carrierMk38 b (carrierCoe38 a y) (carrier_cast_mem h y)) Set.univ := by
  subst h
  have e : (fun y : SobolevCarrier38 a => carrierMk38 a (carrierCoe38 a y) (carrier_cast_mem rfl y)) =
      fun y => y := funext fun y => carrierExt38 rfl
  rw [e]
  exact analyticOnNhd_id

end NlsGge.ThirdConsultation.PDE.CarrierCastAux
