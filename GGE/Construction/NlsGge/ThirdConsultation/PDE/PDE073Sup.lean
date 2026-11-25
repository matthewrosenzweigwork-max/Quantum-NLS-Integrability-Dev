import Mathlib
import NlsGge.ThirdConsultation.PDE.BirkhoffTop
import NlsGge.ThirdConsultation.PDE.BirkhoffRaw
import NlsGge.ThirdConsultation.Common.FiniteSupport
import NlsGge.Birkhoff.S04FiniteGapInvariance38
import NlsGge.Atomic.PDE.PDE046
import NlsGge.Atomic.PDE.PDE072
import NlsGge.Atomic.G6.G6029

                                                                                                                           
                                                                                                                
                                                                                                        
                                                                                                                    
                                                                                                              
set_option autoImplicit false
open Set Filter Topology Metric MeasureTheory
open scoped BigOperators ENNReal InnerProductSpace
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.SpectralFoundations NlsGge.GK38 NlsGge.Atomic.Common
open NlsGge.GKDefinitionDesign NlsGge.NLS38
open NlsGge.ThirdConsultation.Common
namespace NlsGge.ThirdConsultation.PDE

namespace PDE073Aux

theorem actual_densΛ38_twist (c : ℕ → ℝ) (Lambda : Finset ℤ) (t : ℝ) (z : Lambda → ℂ) :
    actualBirkhoffTop38.densΛ38 c Lambda (NlsGge.NLS38.twist (NlsGge.Birkhoff.kappaΛ38 actualOmega Lambda t) z) =
      actualBirkhoffTop38.densΛ38 c Lambda z := by
  have hPhi := @NlsGge.ThirdConsultation.PDE.actualBirkhoffTop38_Phi
  have hG29 : ∀ u : PhysicalL2,
      ((Function.support (physicalBirkhoff u : ℤ → ℂ)).Finite ↔ finiteGap u) ∧
      (finiteGap u → ∀ m : ℕ, fourierSeq38 u ∈ seqSobolev38 (m : ℝ)) :=
    fun u => ⟨(G6029 u).1, (G6029 u).2.1⟩
  have hrot : ∀ (Lambda : Finset ℤ) (z : Lambda → ℂ) (t : ℝ),
      nlsFlowL2 t (actualBirkhoffTop38.finiteGapField38 Lambda z) =
        actualBirkhoffTop38.finiteGapField38 Lambda
          (NlsGge.NLS38.twist (NlsGge.Birkhoff.kappaΛ38 actualOmega Lambda t) z) :=
    fun Lambda z t => actual_finiteGapField_twist Lambda z t
  have hfs : FiniteSupportSequence (actualPhi (actualBirkhoffTop38.finiteGapField38 Lambda z)) := by
    have h := actualBirkhoffTop38.finite_support_Φ_finiteGapField38 Lambda z
    simpa only [FiniteSupportSequence, hPhi] using h
  have hgap : finiteGap (actualBirkhoffTop38.finiteGapField38 Lambda z) := (hG29 _).1.1 hfs
  have hu : SobolevSquareSummable 3 (physicalFourier (actualBirkhoffTop38.finiteGapField38 Lambda z)) := by
    have h := (fourierSeq38_mem_iff _ _).1 ((hG29 _).2 hgap 3)
    simpa using h
  unfold BirkhoffTop38.densΛ38
  rw [← hrot Lambda z t, actual_full_energy_conserved hu t]

end PDE073Aux

end NlsGge.ThirdConsultation.PDE
