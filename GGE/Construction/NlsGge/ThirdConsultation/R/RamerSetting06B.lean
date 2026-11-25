import Mathlib
import NlsGge.ThirdConsultation.R.RamerSetting06
import NlsGge.Atomic.R.R025

                                                                                                                         
                                                                                                                                                       
                                                                                                      
                                                                                                                
                                                                                                          
                                                                                 
set_option autoImplicit false

open Set Metric Filter MeasureTheory
open scoped Topology ENNReal BigOperators RealInnerProductSpace

namespace NlsGge.ThirdConsultation.R
noncomputable section
section ActualRamerSetting
variable {lower upper : ℝ}
variable (c : NlsGge.Pilot.BoundedCoefficients lower upper)
variable (s : ℝ) (hs : (1 : ℝ) / 2 < s)

local notation "E" => RamerE c s
local notation "H" => RamerH c
local notation "μ" => ramerGaussian c s
local notation "i" => cmEmbedding c s hs
local notation "P" => NlsGge.Ramer.headProj c
local notation "Q" => ambientProjection c s
local notation "J" => ramerJac c s hs
local notation "Smap" => TM c s hs

def LocalClosedDiv (K : E → H) (d : E → ℝ) (U : Set E) : Prop :=
  ∀ x₀ ∈ U, ∃ r : ℝ, 0 < r ∧ ball x₀ r ⊆ U ∧
    ∃ (G : E → H) (e : E → ℝ),
      EqOn G K (ball x₀ r) ∧ IsClosedDiv c s G e ∧
      d =ᵐ[(μ).restrict (ball x₀ r)] e

def V2LocalClosedDivergence (K : E → H) (d : E → ℝ) : Prop :=
  AEStronglyMeasurable d μ ∧ LocalClosedDiv c s K d Set.univ

def RamerDensityConclusion
    (T : E ≃ₜ E) (K : E → H) (d : E → ℝ) : Prop :=
  V2LocalClosedDivergence c s K d ∧
    ((μ).map T.symm = (μ).withDensity
      (fun x : E => ENNReal.ofReal (jacobianWithDiv c s hs K d x))) ∧
    (∀ x : E, 0 < jacobianWithDiv c s hs K d x) ∧
    Integrable (jacobianWithDiv c s hs K d) μ ∧
    (∫ x : E, jacobianWithDiv c s hs K d x ∂μ) = 1 ∧
    TendstoInMeasure μ (cylindricalDensity c s K)
      atTop (jacobianWithDiv c s hs K d)

end ActualRamerSetting
end
end NlsGge.ThirdConsultation.R
