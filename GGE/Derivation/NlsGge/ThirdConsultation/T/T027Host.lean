import Mathlib
import NlsGge.ThirdConsultation.T.T026Host

/- T-027 HOST (proof development, AUTHOR; not reviewed; needs ROOT MAIN PROBE). Intended target
   NlsGge/ThirdConsultation/T/T027Host.lean, namespace NlsGge.ThirdConsultation.T.
   Hosts ONCE `lowerEnergy`, body VERBATIM (comment line included) from followup13
   definitions_design_20261027/DEFINITIONS/T.lean.md l.307–310. grep NlsGge/ and Work/ (2026-11-03): no
   `def lowerEnergy` exists. Opens = the DEFINITIONS/T.lean.md common block (= landed T026Host). The body uses only
   landed names: EB38 (Birkhoff/W12Tilt38c, reached through T026Host → W12Tilt38g) and physicalInclusion (T026Host).
   The body elaborated in worker selftest T027_REPLICA04_RUN01 (9c23d292, exit 0; Common open dropped there because
   ThirdConsultation is absent from the worker mirror). -/
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped ENNReal Topology BigOperators ContDiff
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights NlsGge.Sobolev38
open NlsGge.Birkhoff NlsGge.HierarchyRiccati.Core
open NlsGge.ThirdConsultation.Common
namespace NlsGge.ThirdConsultation.T
noncomputable section

-- This is the finite-energy E_s accessor only. The global energy is EB38.
def lowerEnergy {lo up : ℝ} (c : BoundedCoefficients lo up)
    (s : ℝ) (x : ECarrier38 c s) : ℝ :=
  (EB38 c.val (physicalInclusion c s x)).toReal

end
end NlsGge.ThirdConsultation.T
