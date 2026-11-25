import NlsGge.ThirdConsultation.PDE.BirkhoffCarrierCore
import NlsGge.ThirdConsultation.PDE.BirkhoffRawG6
import NlsGge.ThirdConsultation.PDE.BirkhoffRawInv

/- BKCAR glue (proof development, AUTHOR; not reviewed).  Target NlsGge/ThirdConsultation/PDE/BirkhoffCarrier.lean.
   followup13 DEFINITIONS/BIRKHOFF_REALIZATION.lean.md: actualT38_carrier_eq and actualTinv38_carrier_eq, heads VERBATIM,
   proved BEFORE any Top/Analytic record.  Producers: landed actualT38_mapsTo (BirkhoffRawG6), actualTinv38_mapsTo
   (BirkhoffRawInv), G6013 conjunct 6 and G6023, applied to the conditional cores in BirkhoffCarrierCore. -/
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
