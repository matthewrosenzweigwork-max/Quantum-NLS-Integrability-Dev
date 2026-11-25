import Mathlib
import NlsGge.ThirdConsultation.PDE.BirkhoffRealization
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.W07Probability38b
import NlsGge.Measure.WeightedScalarResidual
import NlsGge.Ramer.RamerLemma52
import NlsGge.Analysis.RegularizedDeterminant.IdealAndTransport

/- R-112 PRODUCTION01 (proof development, AUTHOR; not reviewed; needs ROOT MAIN PROBE). PACKET R-112, target
   NlsGge/Atomic/R/R112.lean (TASK_INDEX, REUSE/EXTRACT). Head and preamble VERBATIM from followup13 STATEMENTS/R.md
   §R-112 (`r112_main`) except the owner-APPROVED lexical repair 24 (`B.yN38` → `(B).yN38`, three occurrences).
   Proof: the printed exact landed source reuse W07Probability38b.lean:fN38_decomp at
   B = PDE.actualBirkhoffInput38, O = PDE.actualOneSmoothingInput38 (landed order B O c hs' hs1 N x).
   R-107 is not needed (fN38_decomp is self-contained). B1 lesson: own imports declare both notation right-hand
   sides (PDE/BirkhoffRealization, PDE/OneSmoothing), the head's names (W07Probability38b and its Ramer imports)
   and the sources of the opened namespaces. No hypothesis added. -/
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators InnerProductSpace
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Ramer
open NlsGge.Analysis.RegularizedDeterminant
namespace NlsGge.ThirdConsultation.R
local notation "B" => PDE.actualBirkhoffInput38
local notation "O" => PDE.actualOneSmoothingInput38

theorem r112_main {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ) (hs' : s < 3 / 4) (hs1 : s ≤ 1) (N : ℕ) (x : FullWeightedHilbert c s) :
    fN38 c s N x =
      Real.exp (-(remainder38 c.val (physOfE38 c s (projE38 c s N x)))) *
        Real.exp (-(‖(B).yN38 O c hs1 N x -
          ((cmTrunc c N ((B).yN38 O c hs1 N x) : actualCMHead c N) : ActualCM c)‖ ^ 2 / 2)) *
        Real.exp (-(‖(headPt c N (coordE c s x) : ActualCM c) +
          ((cmTrunc c N ((B).yN38 O c hs1 N x) : actualCMHead c N) : ActualCM c)‖ ^ 2 -
            ‖(headPt c N (coordE c s x) : ActualCM c)‖ ^ 2) / 2) :=
  BirkhoffInput38.fN38_decomp B O c hs' hs1 N x

end NlsGge.ThirdConsultation.R
