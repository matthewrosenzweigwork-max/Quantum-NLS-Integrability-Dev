import Mathlib
import NlsGge.Atomic.G5.G5029Sup4Core
import NlsGge.Atomic.G5.G5020
import NlsGge.Atomic.G4.G4041

/- G5-029 SUPPORT 4 (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/Atomic/G5/G5029Sup4.lean, namespace NlsGge.GKDefinitionDesign.
   Head `continuousOn_angleIntegralBracket` VERBATIM from PRO_DEFINITION_RESPONSE_FP80_14.md "G5029: all-left density" (no repair).
   Route (Pro): analytic dependence of beta (G5020Aux.term_analytic, G3-023) and betaSum (betaSum_analyticOnNhd_sourceBetaW, G3031All) on the
   existing source domains, analytic Cartesian X/Y (G4041) with nonzero radius on the open m-gap locus (G5025Sup3.radius_ne_zero),
   joint continuity of pairPoissonCLM (G5019Sup3).  Proof body in G5029Sup4Core; this file discharges its three hypotheses by the landed theorems. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem continuousOn_angleIntegralBracket
    (k l m n : ℤ) :
  ContinuousOn
    (fun u : PhysicalL2 =>
      pairPoissonCLM (angleIntegralDerivative k m (realSlice u))
        (angleIntegralDerivative l n (realSlice u)))
    {u : PhysicalL2 | gamma2 (realSlice u) m ≠ 0 ∧
      gamma2 (realSlice u) n ≠ 0} :=
  G5029Sup4Aux.continuousOn_bracket_core k l m n G4041 betaSum_analyticOnNhd_sourceBetaW
    G5020Aux.term_analytic

end
end NlsGge.GKDefinitionDesign
