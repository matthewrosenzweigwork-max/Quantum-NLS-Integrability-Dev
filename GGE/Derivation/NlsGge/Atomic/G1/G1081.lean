import Mathlib
import NlsGge.Atomic.G1.S4Asm

/- G1-081 PACKET (proof development, AUTHOR; not reviewed). Target NlsGge/Atomic/G1/G1081.lean.
   Head VERBATIM from Pro round 14 Cluster 2 "G1-081" block. Proof: S4Asm.g1081_assembly_analytic (analytic conjunct via
   S4PicardAnalytic L1, S4L2, S4L3, S4Glob; remaining conjuncts via Sup5/Sup6; G1080 compactness). -/
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
