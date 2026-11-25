import Mathlib
import NlsGge.NLS38.PhysicalFlow38
import NlsGge.Atomic.PDE.PDE034
import NlsGge.ThirdConsultation.Sobolev.Round5

                                                                                                                             
                                                                                            
                                                                                                             
                                                                                                
                                                                                               
set_option autoImplicit false
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.NLS38 NlsGge.GKDefinitionDesign
noncomputable section

namespace NlsGge.ThirdConsultation.PDE.PDE066Aux

theorem flow_eq_of_solution (U : ℝ → PhysicalL2) (hU : IsPhysicalNLSSolution U)
    (u : PhysicalL2) (h0 : U 0 = u) (hu : SobolevSquareSummable 1 (physicalFourier u)) (t : ℝ) :
    U t = nlsFlowL2 t u := by
  have hx : physicalFourier u ∈ NlsGge.ThirdConsultation.PDE.h1 := physicalFourier_mem_one38 hu
  have hA := ((isPhysicalNLSSolution_iff U).1 hU).2
  have hB := ((isPhysicalNLSSolution_iff _).1 (nlsFlowL2_isPhysicalNLSSolution hu)).2
  have hAB := (NlsGge.ThirdConsultation.PDE.h1_global_unique (physicalFourier u) hx).unique
    (y₁ := fun s => physicalFourier (U s)) (y₂ := fun s => physicalFourier (nlsFlowL2 s u))
    ⟨hA, by show physicalFourier (U 0) = _; rw [h0]⟩
    ⟨hB, by show physicalFourier (nlsFlowL2 0 u) = _; rw [nlsFlowL2_zero]⟩
  exact physicalFourier_injective38 (congrFun hAB t)

theorem seqEmbed_coe (m : ℕ) (c : SobolevCarrier38 (m : ℝ)) (n : ℤ) :
    (sequenceSobolevEmbed m c : ℤ → ℂ) n = carrierCoe38 (m : ℝ) c n := by
  exact congrFun (carrierCoe38_incl38 (r := 0) (s := (m : ℝ)) (Nat.cast_nonneg m) c) n

end NlsGge.ThirdConsultation.PDE.PDE066Aux
