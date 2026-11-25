import Mathlib
import NlsGge.Birkhoff.F08Bare38d

/- F030 HOST PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Proposed target
   NlsGge/Atomic/F/F030Host.lean. Hosts ONCE `finiteOrderRelativeZ` (root assignment; R14_AUDIT_F2 F-030 HOSTABLE),
   body byte-identical to followup13 definitions_design_20261027/DEFINITIONS/F.lean.md:284-285 (sha256 b429288d...),
   namespace NlsGge.ThirdConsultation.F. ZcalBare38/gaussConst38 are the landed Birkhoff/F08Bare38d objects.
   grep NlsGge/ (2026-11-02): the name does not exist. Opens: F.lean.md:46-50 header minus NlsGge.Atomic.Common
   (unused). The block's Lean-3 `local attribute [instance] Classical.propDecidable` (F.lean.md:235) is omitted
   (recorded repair; the body uses no decidability). Other names of that block are not hosted here. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology ContDiff
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.HierarchyRiccati.Core
open NlsGge.SpectralFoundations NlsGge.Birkhoff NlsGge.Measure

namespace NlsGge.ThirdConsultation.F

def finiteOrderRelativeZ (m : ℕ) (β : ℕ → ℝ) (N : ℕ) : ℝ :=
  ZcalBare38 m β N / gaussConst38 m β N

end NlsGge.ThirdConsultation.F
