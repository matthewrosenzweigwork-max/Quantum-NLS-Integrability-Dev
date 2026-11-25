import Mathlib
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.W06Jacobian38
import NlsGge.Measure.WeightedScalarResidual
import NlsGge.Ramer.RamerLemma52
import NlsGge.Analysis.RegularizedDeterminant.IdealAndTransport
import NlsGge.ThirdConsultation.R.R109Host
import NlsGge.ThirdConsultation.R.R111Host

/- R-111 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). PACKET R-111, target
   NlsGge/Atomic/R/R111.lean (TASK_INDEX, REUSE/EXTRACT; prerequisites R-110 queued, R-104, R-055 landed). Head and
   preamble VERBATIM from followup13 STATEMENTS/R.md §R-111 (= r14 L7368; r16 no change) except owner-APPROVED lexical
   repair 24 (`(B).muW38`). Route as printed: the exact final conjunct of density_W06_38 with the canonical
   Jacobian (Classical.choose_spec of the landed ramer_W06_38 at the actual pair — the same witness as canonicalDelta,
   strictly positive, so equivalence holds before pushforward and is preserved by the measurable physFW06_38).
   actualFourierGaussian is BY DEFINITION the map in that conjunct (gammaF_eq_W06_38 identifies the same named law).
   No injectivity of physical totalizations is used. R-110 is not needed in Lean. Needs ROOT MAIN PROBE. -/
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators InnerProductSpace
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Ramer
open NlsGge.Analysis.RegularizedDeterminant
namespace NlsGge.ThirdConsultation.R
local notation "B" => PDE.actualBirkhoffInput38
local notation "O" => PDE.actualOneSmoothingInput38

theorem actual_mutually_absolutelyContinuous {lo up : ℝ}
    (c : BoundedCoefficients lo up) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) :
    (B).muW38 c.val ≪ actualFourierGaussian c s ∧
      actualFourierGaussian c s ≪ (B).muW38 c.val := by
  have hs1 : s ≤ 1 := by linarith
  obtain ⟨-, hmap, hpos, hint, -⟩ := Classical.choose_spec
    (NlsGge.Birkhoff.ramer_W06_38 PDE.actualBirkhoffInput38 PDE.actualOneSmoothingInput38 c s hs hs1)
  exact (NlsGge.Birkhoff.density_W06_38 PDE.actualBirkhoffInput38 c s
    PDE.actualOneSmoothingInput38 hs hs' _ hmap hint hpos).2.2.2.2.2

end NlsGge.ThirdConsultation.R
