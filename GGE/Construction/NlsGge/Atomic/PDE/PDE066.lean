import Mathlib
import NlsGge.ThirdConsultation.PDE.Round14InverseRotation
import NlsGge.ThirdConsultation.PDE.PDE066Core
import NlsGge.ThirdConsultation.PDE.BirkhoffRaw
import NlsGge.ThirdConsultation.Common.Actions
import NlsGge.Atomic.PDE.PDE065
import NlsGge.Atomic.G6.G6027
import NlsGge.Atomic.G6.G6013
import NlsGge.Atomic.G6.G6029

                                                                                                  
                                                                                    
                                                                                                            
                                           
                                                                                                          
                                                                                               
                                                                                              
                                                                                                                      
                                                   
                                                                                           
                                                                                                                      
                                            
                                                                                                            
set_option autoImplicit false
open Set Filter Topology Metric MeasureTheory
open scoped BigOperators ENNReal InnerProductSpace
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.SpectralFoundations NlsGge.GK38 NlsGge.Atomic.Common
open NlsGge.GKDefinitionDesign NlsGge.NLS38
open NlsGge.ThirdConsultation.Common
namespace NlsGge.ThirdConsultation.PDE

theorem actual_finitegap_rotation
    (u : PhysicalL2) (hfin : FiniteSupportSequence (actualPhi u))
    (t : ℝ) (n : ℤ) :
  actualPhi (nlsFlowL2 t u) n =
    Complex.exp (-Complex.I *
      ((t * actualOmega n (actions (actualPhi u)) : ℝ) : ℂ)) * actualPhi u n := by
  obtain ⟨-, -, -, -, -, hinvB⟩ := G6027 3 (by norm_num)
  obtain ⟨-, -, -, -, hL, hR⟩ := G6013
  have hG29 : ∀ u : PhysicalL2,
      ((Function.support (physicalBirkhoff u : ℤ → ℂ)).Finite ↔ finiteGap u) ∧
      (finiteGap u → ∀ m : ℕ, fourierSeq38 u ∈ seqSobolev38 (m : ℝ)) :=
    fun u => ⟨(G6029 u).1, (G6029 u).2.1⟩
  have h65 := fun (z0 : Lib.L2Z) (hz : FiniteSupportSequence z0) =>
    (inverse_rotation_is_actual_nls z0 hz).2
  have hgap : finiteGap u := (hG29 u).1.1 hfin
  have hu : SobolevSquareSummable 1 (physicalFourier u) := by
    have h := (fourierSeq38_mem_iff _ u).1 ((hG29 u).2 hgap 1)
    rwa [Nat.cast_one] at h
  have hcurve : ∀ s : ℝ, actualPhi (inverseRotationPhysical (actualPhi u) hfin s) =
      sequenceSobolevEmbed 3 (rotationCurve ((3 : ℕ) : ℝ) (actualPhi u) hfin s) := by
    intro s
    show physicalBirkhoff (physicalSobolevEmbed 3
      (inverseBirkhoffSobolev 3 (rotationCurve ((3 : ℕ) : ℝ) (actualPhi u) hfin s))) = _
    rw [(hinvB _).2]
    exact hR _
  have hcoef : ∀ (s : ℝ) (k : ℤ),
      (sequenceSobolevEmbed 3 (rotationCurve ((3 : ℕ) : ℝ) (actualPhi u) hfin s) : ℤ → ℂ) k =
        rotationSequence (actualPhi u) s k := fun s k => by
    rw [PDE066Aux.seqEmbed_coe]
    rfl
  have hstart : sequenceSobolevEmbed 3 (rotationCurve ((3 : ℕ) : ℝ) (actualPhi u) hfin 0) =
      actualPhi u := by
    apply lp.ext
    funext k
    rw [hcoef]
    simp [rotationSequence]
  have h0 : inverseRotationPhysical (actualPhi u) hfin 0 = u := by
    show physicalSobolevEmbed 3
      (inverseBirkhoffSobolev 3 (rotationCurve ((3 : ℕ) : ℝ) (actualPhi u) hfin 0)) = u
    rw [(hinvB _).2, hstart]
    exact hL u
  have heq := PDE066Aux.flow_eq_of_solution _ (h65 (actualPhi u) hfin) u h0 hu t
  rw [← heq, hcurve, hcoef]
  rfl

end NlsGge.ThirdConsultation.PDE
