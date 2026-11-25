import Mathlib
import NlsGge.Birkhoff.F05Identity38
import NlsGge.Spectral.ChargeJensenSobolev38

/- F025HOST PRODUCTION03 (proof development continuing proof development; not independently reviewed).
   Target NlsGge/Atomic/F/F025Host.lean, namespace NlsGge.ThirdConsultation.F.
   Hosts `tiltedTerminal` once. Its declaration body is verbatim from followup13
   handoff/definitions_design_20261027/DEFINITIONS/F.lean.md:281-282, as authorized by the 2026-11-04 root ruling. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology ContDiff
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.HierarchyRiccati.Core
open NlsGge.SpectralFoundations NlsGge.Birkhoff NlsGge.Measure

namespace NlsGge.ThirdConsultation.F

def tiltedTerminal (m : ℕ) (β : ℕ → ℝ) (δ : ℝ) (u : Hm1 m) : ℝ :=
  Real.exp (-Vm38 m β u + δ * (chargeSobolev38 m 0 u) ^ m)

end NlsGge.ThirdConsultation.F
