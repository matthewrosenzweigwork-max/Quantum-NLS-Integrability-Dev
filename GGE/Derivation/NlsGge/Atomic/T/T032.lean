import Mathlib
import NlsGge.ThirdConsultation.T.TDefs2Host
import NlsGge.Birkhoff.W12Tilt38c
import NlsGge.Spectral.ActualLabelledGapActionAllNE02_38
import NlsGge.ThirdConsultation.Common.FiniteSupport

/- T-032 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted; needs ROOT MAIN PROBE; STAGED AFTER
   T-028 per root, although the proof uses neither T-027 nor T-028). Proposed target NlsGge/Atomic/T/T032.lean.
   Head `lowerWeightTilt_spectralDefect` VERBATIM from followup13 STATEMENTS/T.md §T-032 (r17: retain_head_unchanged).
   HOST PENDING ROOT RULING: `spectralDefect` (DEFINITIONS/T.lean.md l.118-119) is not in TDefsHost/T027Host/T028Host;
   this file assumes it is hosted in h774's TDefs2Host (import line above; swap if root rules otherwise).
   Preamble: DEFINITIONS/T.lean.md common opens PLUS `open NlsGge.SpectralFoundations` (repair-22-class open; the head
   names actualGapActionAllE02_38, which lives in NlsGge.SpectralFoundations; without it the printed head fails to
   elaborate: T032_REPLICA01_RUN01 27b1a329 "Unknown identifier actualGapActionAllE02_38"). NEEDS ROOT/REVIEWER CONFIRM
   (precedent: R-141, R-147, KO-018, T-017; landed T-021/T-025/T-026 open the same namespace).
   Common.FiniteSupport is imported so the printed `open NlsGge.ThirdConsultation.Common` resolves (as in T026Host).
   Proof: exact landed reuse W12Tilt38c remainder_tilt_identity38 (printed route); spectralDefect c u is by definition
   remainder38 c u. The three Summable premises are hypotheses of the printed head (precise finiteness domain);
   EB38 ≠ ⊤ is a conclusion proved in ENNReal by the producer before toReal is taken. No hypothesis added. -/
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped ENNReal Topology BigOperators ContDiff
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights NlsGge.Sobolev38
open NlsGge.Birkhoff NlsGge.HierarchyRiccati.Core
open NlsGge.ThirdConsultation.Common
open NlsGge.SpectralFoundations
namespace NlsGge.ThirdConsultation.T

theorem lowerWeightTilt_spectralDefect
    (lo up : ℝ) (c : BoundedCoefficients lo up) (delta : ℝ)
    (hd0 : 0 < delta) (hd : delta * up < lo) (u : PhysicalL2)
    (hW : Summable (fun n : ℤ => remainderSummand38 c.val u n))
    (hWt : Summable (fun n : ℤ => remainderSummand38 (tiltCoef38 c.val delta) u n))
    (hA : Summable (fun n : ℤ => bRate38 c.val n * actualGapActionAllE02_38 u n)) :
    EB38 c.val u ≠ ⊤ ∧
    spectralDefect (tiltCoef38 c.val delta) u = spectralDefect c.val u -
      delta * ((EB38 c.val u).toReal -
        ∑' n : ℤ, bRate38 c.val n * actualGapActionAllE02_38 u n) :=
  remainder_tilt_identity38 c hd0 hd u hW hWt hA

end NlsGge.ThirdConsultation.T
