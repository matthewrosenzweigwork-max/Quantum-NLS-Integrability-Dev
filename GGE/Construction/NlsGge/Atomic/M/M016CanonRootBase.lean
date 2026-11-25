import Mathlib
import NlsGge.GK38.TauGammaExterior
import NlsGge.GK38.StdRootBranchesProducts
import NlsGge.GK38.PairRealBridge

                                                                                                
                                                                                                                   
                                                                                                                         
                                                                                                                          
                                                                                                                        
set_option autoImplicit false
noncomputable section
open Set Filter Topology
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.ThirdConsultation.M016ChartAux

/-- **(S4b)** The canonical root tends to `0` at the base endpoint inside the cut-free fiber. -/
theorem canonRoot_tendsto_base (φ : PotPair) (hφ : φ ∈ gkW) :
    Filter.Tendsto (canonRoot38 φ)
      (nhdsWithin (lamMinus φ 0) {z | z ∉ gapSegments38 φ}) (nhds 0) := by
  have hz : perChar φ (lamMinus φ 0) = 0 := by
    rw [exterior_perChar_factor38 φ 0 (lamMinus φ 0)]; simp
  have hc : Filter.Tendsto (fun z => Real.sqrt ‖perChar φ z‖) (nhds (lamMinus φ 0)) (nhds 0) := by
    have h := ((analyticOnNhd_perChar_z φ (lamMinus φ 0) (Set.mem_univ _)).continuousAt.norm.sqrt).tendsto
    simpa [hz] using h
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine (hc.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hzc
  have hsq := canonRoot_sq38 φ hφ z hzc
  rw [← hsq, norm_pow, Real.sqrt_sq (norm_nonneg _)]

end NlsGge.ThirdConsultation.M016ChartAux
