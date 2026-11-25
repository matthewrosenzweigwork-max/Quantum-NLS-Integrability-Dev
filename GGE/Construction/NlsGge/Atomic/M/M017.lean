import Mathlib
import NlsGge.Atomic.M.M016
import NlsGge.Atomic.M.M016SmoothLift
import NlsGge.Atomic.M.M017RealCore
import NlsGge.Atomic.G6.G6029
import NlsGge.Atomic.M.M017Cx

                                                                                                                                                                                                                     
                                                                                                       
                                                                                                                      
                                                                                                                     
                                                                                                                   
                                                                                              
                                                                                                                      
                                                                 
set_option autoImplicit false
open Set Filter Topology Metric
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations
open NlsGge.GKDefinitionDesign
open NlsGge.Birkhoff

namespace NlsGge.ThirdConsultation.M

theorem higher_action_trace_finitegap_real
    (N : ℕ) (φ : KSPS.SobolevC N)
    (hreal : MRiccati.RealPair φ)
    (hfg : finiteGap (MRiccati.realPhysicalFromPair φ))
    (k : ℕ) (hk : 2 ≤ k) (hkN : k ≤ N + 1) :
    Summable (fun n : ℤ => higherAction (MRiccati.realPhysicalFromPair φ) n k) ∧
    (∑' n : ℤ, higherAction (MRiccati.realPhysicalFromPair φ) n k) =
      (-((2 * Complex.I) ^ (k - 1))⁻¹ *
        hierarchyCharge φ ⟨k, (by omega), hkN⟩).re := by
  set u : PhysicalL2 := MRiccati.realPhysicalFromPair φ with hu
  have hall : ∀ m : ℕ, fourierSeq38 u ∈ seqSobolev38 (m : ℝ) := (G6029 u).2.1 hfg
  obtain ⟨R, F, hrep, -, hcoef⟩ :=
    finitegap_primitive_laurent_real u hfg (NlsGge.ThirdConsultation.M016SM.smooth_lift u hall)
  have hu1 : SobolevSquareSummable 1 (physicalFourier u) := by
    simpa using (fourierSeq38_mem_iff ((1 : ℕ) : ℝ) u).1 (hall 1)
  have hfin : {n : ℤ | actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n}.Finite :=
    Set.Finite.subset hfg (fun n hn => ne_of_lt hn)
  exact NlsGge.ThirdConsultation.M017R.trace_real_core u hu1 hfin R F hrep.2 N φ (hcoef N φ hreal) k hk hkN

end NlsGge.ThirdConsultation.M
