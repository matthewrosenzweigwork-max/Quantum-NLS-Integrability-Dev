import Mathlib
import NlsGge.ThirdConsultation.PDE.BirkhoffRealization
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.W09Approx38b
import NlsGge.Birkhoff.W10Localized38e
import NlsGge.Birkhoff.W10Localized38f
import NlsGge.Measure.WeightedScalarResidual
import NlsGge.Ramer.RamerLemma52
import NlsGge.Analysis.RegularizedDeterminant.IdealAndTransport

/- R-137 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). PACKET R-137, target
   NlsGge/Atomic/R/R137.lean (TASK_INDEX, REUSE/EXTRACT; listed prerequisites R-133, R-134, R-136 (h774, not landed),
   R-110 (landed)). Head and preamble VERBATIM from followup13 STATEMENTS/R.md §R-137 (r16 no change), with OWNER-APPROVED
   lexical repair 24 only: `B.ZW38` → `(B).ZW38`, `B.muW38` → `(B).muW38` (one occurrence each).
   Imports declare both notation right-hand sides (PDE.BirkhoffRealization, PDE.OneSmoothing; B1 lesson) and the
   defining modules W10Localized38f (producer; with its chain for physOfE38, projE38, chiR38, fN38, CutoffProfile38,
   fullWeightedSequenceGaussian, ZW38, muW38).
   Proof: the printed exact landed source reuse `Birkhoff/W10Localized38f.lean:W10_localized_Es38` at the actual pair
   B = PDE.actualBirkhoffInput38, O = PDE.actualOneSmoothingInput38; its type is the head verbatim.  The dominated
   convergence (integrable dominating bound from hFb and the cutoff, a.e. strong measurability) is carried out inside the
   landed producer (B.tendsto_localIntegral38 / B.integral_gLoc_comp_symm38), so no limit is exchanged here.
   This proof does NOT use the unlanded R-133/R-134/R-136 (TASK_INDEX prerequisites only); the landed W10 producers
   already contain their content. -/
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators InnerProductSpace
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Ramer
open NlsGge.Analysis.RegularizedDeterminant
namespace NlsGge.ThirdConsultation.R
local notation "B" => PDE.actualBirkhoffInput38
local notation "O" => PDE.actualOneSmoothingInput38

theorem r137_main {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ) (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) {χ : ℝ → ℝ} {R : ℝ}
    (hχ : CutoffProfile38 χ) (hR : 0 < R) (F : PhysicalL2 → ℝ)
    (hF : Continuous (fun y : ECarrier38 c s => F (physOfE38 c s y)))
    (hFb : ∃ M, ∀ y : ECarrier38 c s, |F (physOfE38 c s y)| ≤ M) :
    Tendsto (fun N : ℕ => ∫ x, F (physOfE38 c s (projE38 c s N x)) *
        chiR38 χ R (physOfE38 c s (projE38 c s N x)) * fN38 c s N x
        ∂(fullWeightedSequenceGaussian c s))
      atTop (𝓝 ((B).ZW38 c.val * ∫ u, F u * chiR38 χ R u ∂((B).muW38 c.val))) :=
  (B).W10_localized_Es38 O c hs hs' hχ hR F hF hFb

end NlsGge.ThirdConsultation.R
