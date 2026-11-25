import Mathlib
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.W04WeightedSmoothing38c
import NlsGge.Birkhoff.W05FiniteGap38
import NlsGge.Birkhoff.W08Compact38
import NlsGge.Measure.WeightedScalarResidual
import NlsGge.Ramer.RamerLemma52
import NlsGge.Analysis.RegularizedDeterminant.IdealAndTransport

/- R-104 PRODUCTION01 (proof development, AUTHOR; not reviewed). PACKET R-104, target NlsGge/Atomic/R/R104.lean (TASK_INDEX,
   REUSE/EXTRACT). Head and preamble VERBATIM from followup13 STATEMENTS/R.md §R-104 (= r14, string-checked; r16 no change).
   No `B.` in the head, so repair 24 is not needed. Proof: r14 "exact already landed content behind the nonexistent task
   edge KEEP-E03-CONT": W05FiniteGap38 BirkhoffInput38.continuous_remainder_physOfE38 at the actual pair
   B = PDE.actualBirkhoffInput38, O = PDE.actualOneSmoothingInput38 (the physical remainder is remainder38, not Rbar38).
   Own imports (B1 lesson): PDE.OneSmoothing for the preamble notations' quotation precheck; W05FiniteGap38 for the reused
   theorem; the rest provide the preamble namespaces. MAIN-ONLY (OneSmoothing). -/
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators InnerProductSpace
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Ramer
open NlsGge.Analysis.RegularizedDeterminant
namespace NlsGge.ThirdConsultation.R
local notation "B" => PDE.actualBirkhoffInput38
local notation "O" => PDE.actualOneSmoothingInput38

theorem r104_main {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ)  (hs : s < 3 / 4) :
    Continuous (fun x : ECarrier38 c s => remainder38 c.val (physOfE38 c s x)) :=
  BirkhoffInput38.continuous_remainder_physOfE38 B c s O hs

end NlsGge.ThirdConsultation.R
