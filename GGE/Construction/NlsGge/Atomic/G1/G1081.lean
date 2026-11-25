import Mathlib
import NlsGge.Atomic.G1.S4Asm

                                                                                         
                                                                                                                        
                                                                                                     
set_option autoImplicit false
open Set Filter Topology Metric MeasureTheory
open scoped BigOperators ENNReal InnerProductSpace
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.SpectralFoundations NlsGge.GK38 NlsGge.Atomic.Common
namespace NlsGge.GKDefinitionDesign

theorem G1_081 (n : ℤ) :
    (∃! f : ℝ → PhysicalL2 → PhysicalL2, completeGapFlow n f) ∧
    completeGapFlow n (singleGapFlow n) ∧
    AnalyticOnNhd ℝ
      (fun p : ℝ × PhysicalL2 => singleGapFlow n p.1 p.2) Set.univ ∧
    (∀ s t : ℝ, ∀ u : PhysicalL2,
      singleGapFlow n (s+t) u = singleGapFlow n s (singleGapFlow n t u)) ∧
    (∀ t : ℝ, ∀ u : PhysicalL2,
      isospectral u (singleGapFlow n t u)) :=
  NlsGge.Atomic.G1081S4Asm.g1081_assembly_analytic n

end NlsGge.GKDefinitionDesign
