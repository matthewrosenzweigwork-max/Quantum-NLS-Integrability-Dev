import Mathlib
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.W04WeightedSmoothing38c
import NlsGge.Birkhoff.W08Compact38
import NlsGge.Birkhoff.W08Compact38b
import NlsGge.Measure.WeightedScalarResidual
import NlsGge.Ramer.RamerLemma52
import NlsGge.Analysis.RegularizedDeterminant.IdealAndTransport

/- R-122 PRODUCTION01 (proof development, AUTHOR; not reviewed). PACKET R-122, target NlsGge/Atomic/R/R122.lean (TASK_INDEX,
   REUSE/EXTRACT). Head and preamble VERBATIM from followup13 STATEMENTS/R.md §R-122 (= r14, string-checked; r16 no change)
   with OWNER-APPROVED REPAIR 24 only: `B.detTN` -> `(B).detTN` (×2). Proof: the printed exact landed source reuse
   W08Compact38b.eventually_inv_abs_detTN_le_two at the actual pair. Uniformity check (r16 Q2): the producer's conclusion is
   literally the printed one — R fixed, eventually in N, uniformly over x ∈ ballV38 N R — with det ≠ 0 stated before the
   reciprocal (no totalized inverse used as an invertibility certificate). R-070 (TASK_INDEX prerequisite) is not used.
   Own imports (B1 lesson): OneSmoothing (notations, actual pair), W08Compact38b (producer); rest = preamble namespaces.
   MAIN-ONLY. -/
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators InnerProductSpace
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Ramer
open NlsGge.Analysis.RegularizedDeterminant
namespace NlsGge.ThirdConsultation.R
local notation "B" => PDE.actualBirkhoffInput38
local notation "O" => PDE.actualOneSmoothingInput38

theorem r122_main  (R : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ x ∈ ballV38 N R, (B).detTN N x ≠ 0 ∧ |(B).detTN N x|⁻¹ ≤ 2 :=
  (B).eventually_inv_abs_detTN_le_two O R

end NlsGge.ThirdConsultation.R
