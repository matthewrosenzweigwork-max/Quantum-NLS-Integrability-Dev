import Mathlib
import NlsGge.ThirdConsultation.I.I030Core
import NlsGge.ThirdConsultation.I.ActualEnsembleBridge
import NlsGge.ThirdConsultation.PDE.BirkhoffRealization

/- I030 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). GLUE. Target NlsGge/Atomic/I/I030.lean,
   namespace NlsGge.ThirdConsultation.I.  Head `i030` VERBATIM from followup13 STATEMENTS/I.md "## I-030" (r14 l.7426:
   retain; r17 Q3: retain real moment exponents), under the DEFINITIONS/I.lean.md preamble l.39-46 (verbatim).
   Proof: I030Aux.i030_of (lane-checked core, lane 61c651b9) at B := PDE.actualBirkhoffTop38,
   hM := PDE.actualBirkhoffMolnar38, μ := physicalLaw (weight c.val), hμ := (actual_ensemble_eq_I lower upper c).2.2.1
   (actualMuW c.val = physicalLaw (weight c.val); actualMuW is definitionally actualBirkhoffTop38.muW38), exactly the
   instantiation used by landed I-029.  Replica glue (generic μ, same preamble and head) lane ae54a88f exit 0.
   Prerequisite KEEP-E06-POLY: not a landing gate (root ruling AUDIT_DEFERRED_NOTES01 l.153); only landed anchors imported.
   MAIN-ONLY (ActualEnsembleBridge / BirkhoffRealization): needs ROOT MAIN PROBE (I030_RECEIVER01). -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology ContDiff
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights
open NlsGge.HierarchyRiccati.Core NlsGge.SpectralFoundations
open NlsGge.Birkhoff NlsGge.Sobolev38 NlsGge.GKDefinitionDesign
open scoped BoundedContinuousFunction

namespace NlsGge.ThirdConsultation.I

theorem i030 (lower upper : ℝ) (c : BoundedCoefficients lower upper) :
    (∀ j : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ d : ℕ,
      ∀ u : PhysicalL2, SobolevSquareSummable ((j + 1 : ℕ) : ℝ) (physicalFourier u) →
        |chargeFn38 (j + 2) j u| ≤ C * (1 + ‖physFS38 (j + 1) u‖) ^ d) ∧
    (∀ (j : ℕ) (q : ℝ), 0 ≤ q →
      Integrable (fun u : PhysicalL2 => |chargeFn38 (j + 2) j u| ^ q)
        (physicalLaw (weight c.val))) ∧
    (∀ᵐ u ∂physicalLaw (weight c.val),
      ∃ (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1),
        smoothL2_38 U hU hper = u ∧
        ∀ j : ℕ, chargeFn38 (j + 2) j u = localCharge38 U j) :=
  NlsGge.ThirdConsultation.I030Aux.i030_of lower upper c PDE.actualBirkhoffTop38 PDE.actualBirkhoffMolnar38
    (physicalLaw (weight c.val)) (actual_ensemble_eq_I lower upper c).2.2.1

end NlsGge.ThirdConsultation.I
