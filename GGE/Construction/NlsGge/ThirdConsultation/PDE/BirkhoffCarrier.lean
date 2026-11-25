import NlsGge.ThirdConsultation.PDE.BirkhoffCarrierCore
import NlsGge.ThirdConsultation.PDE.BirkhoffRawG6
import NlsGge.ThirdConsultation.PDE.BirkhoffRawInv

                                                                                                             
                                                                                                                         
                                                                                                                  
                                                                                                            
set_option autoImplicit false
open Set
open scoped Classical ENNReal Topology
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.SpectralFoundations
open NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.Common
namespace NlsGge.ThirdConsultation.PDE
noncomputable section

theorem actualT38_carrier_eq (m : ℕ) :
    carrierMap38 (m : ℝ) (m : ℝ) actualT38 (actualT38_mapsTo m) =
      actualTC38 m :=
  BirkhoffCarrierCore.t_carrier_eq_of G6023 m (actualT38_mapsTo m)

theorem actualTinv38_carrier_eq (m : ℕ) :
    carrierMap38 (m : ℝ) (m : ℝ) actualTinv38 (actualTinv38_mapsTo m) =
      actualTinvC38 m :=
  BirkhoffCarrierCore.tinv_carrier_eq_of G6013.2.2.2.2.2 G6023 m (actualTinv38_mapsTo m)

end
end NlsGge.ThirdConsultation.PDE
