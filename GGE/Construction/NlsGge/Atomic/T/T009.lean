import Mathlib
import NlsGge.Hierarchy.A01Spectral38
import NlsGge.Hierarchy.ExponentialH2Moment38
import NlsGge.Hierarchy.RelativePartition38
import NlsGge.ThirdConsultation.Common.FiniteSupport
import NlsGge.ThirdConsultation.T.TDefsHost
import NlsGge.ThirdConsultation.T.TDefs2Host
import NlsGge.Atomic.T.T008
import NlsGge.Birkhoff.F09Limit38e
import NlsGge.Birkhoff.F09Limit38g
import NlsGge.ThirdConsultation.PDE.BirkhoffRealization
import NlsGge.ThirdConsultation.PDE.OneSmoothing

                                                                                                               
                                                                                                                   
                                                                                                                    
                                                                                                              
                                                                                                          
                                                                                                                        
                                                                                                                        
                                                                                                                       
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped ENNReal Topology BigOperators ContDiff
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights NlsGge.Sobolev38
open NlsGge.Birkhoff NlsGge.HierarchyRiccati.Core
open NlsGge.ThirdConsultation.Common

namespace NlsGge.ThirdConsultation.T
noncomputable section

theorem fullFourier_normalizers_limit_lower
    (lo up : ℝ) (c : BoundedCoefficients lo up) :
    0 < ZW c ∧
    Tendsto (relativePartition c) atTop (𝓝 (ZW c)) ∧
    ∃ zmin : ℝ, 0 < zmin ∧ ∀ N : ℕ, zmin ≤ relativePartition c N := by
  -- One fixed admissible window s = 5/8 (1/2 < 5/8 < 3/4) for the landed window producers. Neither object depends
  -- on s: the obtained facts below are stated with no s at all (ZW38 c.val, relativePartition38 c N).
  have hs : (1 : ℝ) / 2 < 5 / 8 := by norm_num
  have hs' : (5 / 8 : ℝ) < 3 / 4 := by norm_num
  have hZ : Tendsto (fun N : ℕ => relativePartition38 c N) atTop
        (𝓝 (PDE.actualBirkhoffInput38.ZW38 c.val)) ∧ 0 < PDE.actualBirkhoffInput38.ZW38 c.val :=
    PDE.actualBirkhoffInput38.Z_tendsto_38 PDE.actualOneSmoothingInput38 c hs hs'
  have hinf : ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, δ ≤ relativePartition38 c N :=
    PDE.actualBirkhoffInput38.inf_Z_pos38 PDE.actualOneSmoothingInput38 c hs hs'
  obtain ⟨hlim, hpos⟩ := hZ
  obtain ⟨δ, hδ, hlow⟩ := hinf
  rw [ZW_eq_actual lo up c]
  exact ⟨hpos, hlim, δ, hδ, hlow⟩

end
end NlsGge.ThirdConsultation.T
