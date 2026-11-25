                                                                                                                                                                                                                                                             
                                                                             
import NlsGge.Hierarchy.RiccatiMonomialSobolevCMM38
import NlsGge.Hierarchy.RiccatiLocalRemainderPaperForm38
import NlsGge.Atomic.PhysicalSobolev

                                                 
                                        
                                                                                      
                                                   
                                                                                           
                                                                  
                                                                             
                                                                                
                                                                                                   
                                                                                         
                                                                                              

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology ContDiff
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.HierarchyRiccati.Core
open NlsGge.SpectralFoundations NlsGge.Birkhoff NlsGge.Measure
open NlsGge.Atomic.Common

namespace NlsGge.ThirdConsultation.F

def highDerivativeFactorCount (s : ℕ) (q : Jet →₀ ℕ) : ℕ :=
  ((riccatiActualMonomialSlotFinsetRecovery31Fourth q).filter
    (fun occurrence => occurrence.1.2 = s)).card

/-- F-002, Pro's signature. -/
theorem f002 (m : ℕ) (hm : 2 ≤ m) (q : Jet →₀ ℕ) (c : ℤ)
    (hord : ∀ v ∈ q.support, v.2 ≤ m - 1)
    (htop : highDerivativeFactorCount (m - 1) q ≤ 2) :
    ∃ A : ContinuousMultilinearMap ℝ
        (fun _ : Fin (monomialSlotCount38 q) =>
          SobolevCarrier38 ((m - 1 : ℕ) : ℝ)) ℝ,
      (∀ y : Fin (monomialSlotCount38 q) → SobolevCarrier38 ((m - 1 : ℕ) : ℝ),
        Integrable (fun t : PhysicalCircle =>
          ∏ i, (monomialSlotMap38 (m - 1) q i (y i) : PhysicalCircle → ℂ) t)
          spatialMeasure ∧
        A y = ((c : ℂ) * ∫ t : PhysicalCircle,
          ∏ i, (monomialSlotMap38 (m - 1) q i (y i) : PhysicalCircle → ℂ) t
            ∂spatialMeasure).re) ∧
      (∀ (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1)
        (y : SobolevHilbert ((m - 1 : ℕ) : ℝ)),
        (∀ n : ℤ, (show WeightedHilbert
            (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from y) n =
          smoothFourier38 U hU hper n) →
        A (fun _ => toCarrier38 _ y) =
          (∫ t in (0 : ℝ)..1,
            riccatiJetEvaluation U t (MvPolynomial.monomial q c)).re) := by
  have htop' : ((riccatiActualMonomialSlotFinsetRecovery31Fourth q).filter
      (fun σ => σ.1.2 = m - 1)).card ≤ 2 := htop
  refine ⟨riccatiMonomialSobolevCMM38 (m - 1) q c htop', ?_, ?_⟩
  · intro y
    refine ⟨?_, ?_⟩
    · exact mixedProduct_integrable38 (E := SobolevCarrier38 ((m - 1 : ℕ) : ℝ))
        (monomialSlotTop38 (m - 1) q) (monomialSlot_highCount_le_two38 (m - 1) q htop')
        (monomialSlotMap38 (m - 1) q) y
    · exact riccatiMonomialSobolevCMM38_apply (m - 1) q c htop' y
  · intro U hU hper y hy
    exact riccatiMonomialSobolevCMM38_diag_smooth (m - 1) q c htop' hord U hU hper y
      (fun n => hy n)


end NlsGge.ThirdConsultation.F
