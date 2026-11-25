import Mathlib
import NlsGge.Birkhoff.W12Tilt38g
import NlsGge.ThirdConsultation.Common.FiniteSupport

/- T-026 HOST (proof development, AUTHOR; not reviewed; needs ROOT MAIN PROBE). Intended target
   NlsGge/ThirdConsultation/T/T026Host.lean, namespace NlsGge.ThirdConsultation.T.
   Hosts ONCE the four definitions used by the T-026 head, bodies VERBATIM from followup13
   definitions_design_20261027/DEFINITIONS/T.lean.md: lowerEnergyGapTerms (l.98–100), convergentWeightedFields
   (l.102–105), physicalInclusion (l.258–260, = r14 PRO_DEFINITION_RESPONSE_FP80_14.md l.5971), UniformVanishingTails
   (l.312–315, = r14 l.6025). grep NlsGge/ (2026-11-03): none of the four names exists. Opens = the union of the two
   Pro blocks' opens. Bodies use only landed Birkhoff names (gapIntegral38, bCoef38, ECarrier38, physOfE38).
   The bodies elaborated in a worker selftest (T026Host_RUN01, without the Common open, absent from the mirror). -/
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped ENNReal Topology BigOperators ContDiff
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights NlsGge.Sobolev38
open NlsGge.Birkhoff NlsGge.HierarchyRiccati.Core
open NlsGge.ThirdConsultation.Common
namespace NlsGge.ThirdConsultation.T
noncomputable section

def lowerEnergyGapTerms {lo up : ℝ}
    (c : BoundedCoefficients lo up) (u : PhysicalL2) (n : ℤ) : ℝ :=
  gapIntegral38 (bCoef38 c.val) u n

def convergentWeightedFields {lo up : ℝ}
    (c : BoundedCoefficients lo up) (s : ℝ)
    (u : ℕ → ECarrier38 c s) : Prop :=
  ∃ v, Tendsto u atTop (𝓝 v)

def physicalInclusion {lo up : ℝ} (c : BoundedCoefficients lo up)
    (s : ℝ) : ECarrier38 c s → PhysicalL2 :=
  physOfE38 c s

def UniformVanishingTails (a : ℕ → ℤ → ℝ) : Prop :=
  (∀ N : ℕ, Summable (a N)) ∧
    ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ N : ℕ,
      |∑' n : ℤ, if K < n.natAbs then a N n else 0| ≤ ε

end
end NlsGge.ThirdConsultation.T
