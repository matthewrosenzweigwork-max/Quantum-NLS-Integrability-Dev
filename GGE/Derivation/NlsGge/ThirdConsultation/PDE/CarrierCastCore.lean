import Mathlib
import NlsGge.Birkhoff.BirkhoffAPI38

/- CARRIER CAST CORE PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Proposed target
   NlsGge/ThirdConsultation/PDE/CarrierCastCore.lean. Birkhoff API only. For equal real indices a = b (e.g. (r:ℝ)+1 and
   ((r+1:ℕ):ℝ)), the coordinate-preserving reindexing SobolevCarrier38 a → SobolevCarrier38 b is analytic (it is the
   identity after `subst`). Theorems only; the map is written inline. -/

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
