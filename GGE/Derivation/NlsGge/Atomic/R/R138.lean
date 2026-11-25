import Mathlib
import NlsGge.ThirdConsultation.PDE.BirkhoffRealization
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.W10Localized38g
import NlsGge.Measure.WeightedScalarResidual
import NlsGge.Ramer.RamerLemma52
import NlsGge.Analysis.RegularizedDeterminant.IdealAndTransport

/- R-138 PRODUCTION01 (proof development, AUTHOR; not reviewed; needs ROOT MAIN PROBE). PACKET R-138, target
   NlsGge/Atomic/R/R138.lean (TASK_INDEX, REUSE/EXTRACT; prerequisites R-111/R-108/R-131/R-095 not used directly).
   Head and preamble VERBATIM from followup13 STATEMENTS/R.md §R-138 (`r138_main`) except the owner-APPROVED lexical
   repair 24 (`B.muW38` → `(B).muW38`). χ, hχ, R, hR and the window 1/2 < s < 3/4 are retained.
   Proof: the printed exact landed source reuse W10Localized38g.lean:muW_chiR_pos38 at B = PDE.actualBirkhoffInput38,
   O = PDE.actualOneSmoothingInput38 (landed order B O c hs hs' hχ hR, as in W10Localized38h). The landed proof proves
   integrability (domination by the density J) and nonnegativity before the real integral, positivity by
   integral_pos_iff_support_of_nonneg on a nonempty open set where χ_R = 1 and J > 0, and uses the normalizer only as
   1/Z with Z > 0 proved (ZW38_pos_le_one): no totalized division by zero; positivity is derived from the actual
   density, not imposed. B1 lesson: own imports declare both notation right-hand sides and the opened namespaces.
   No hypothesis added. -/
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators InnerProductSpace
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Ramer
open NlsGge.Analysis.RegularizedDeterminant
namespace NlsGge.ThirdConsultation.R
local notation "B" => PDE.actualBirkhoffInput38
local notation "O" => PDE.actualOneSmoothingInput38

theorem r138_main {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ) (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) {χ : ℝ → ℝ} {R : ℝ}
    (hχ : CutoffProfile38 χ) (hR : 0 < R) : 0 < ∫ u, chiR38 χ R u ∂((B).muW38 c.val) :=
  BirkhoffInput38.muW_chiR_pos38 B O c hs hs' hχ hR

end NlsGge.ThirdConsultation.R
