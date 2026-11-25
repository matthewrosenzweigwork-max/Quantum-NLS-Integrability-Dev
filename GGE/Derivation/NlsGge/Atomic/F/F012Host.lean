import Mathlib
import NlsGge.Birkhoff.F05Identity38
import NlsGge.ThirdConsultation.G6.SobolevBirkhoff
import NlsGge.Atomic.F.F027

/- F012 HOST PRODUCTION02 (proof development, AUTHOR; not self-reviewed, not accepted). Proposed target
   NlsGge/Atomic/F/F012Host.lean. Fixes integration defect B1 of PRODUCTION01 (proof development/REVIEW_F030012_01.md):
   `sobolevCoe` is NOT redeclared; it is imported from the landed NlsGge/Atomic/F/F027.lean:20 (commit 4f4483e36), whose
   body is byte-identical to DEFINITIONS/F.lean.md:137-138 (same pattern as F036.lean:14).
   Hosts ONCE finiteT, finiteA, finiteD (root assignment), bodies byte-identical to followup13
   definitions_design_20261027/DEFINITIONS/F.lean.md:140-143 and :180-184 (sha256 b429288d...), namespace
   NlsGge.ThirdConsultation.F, block opens (F.lean.md:46-50 header + `open NlsGge.GKDefinitionDesign`).
   grep NlsGge/ (2026-11-02): finiteT, finiteA, finiteD do not exist elsewhere. birkhoffSobolev from the landed G6
   SobolevBirkhoff host; Hm1/Vm38/Rm38/FinvH38 from Birkhoff/F05Identity38. The block's Lean-3 line
   `local attribute [instance] Classical.propDecidable` (F.lean.md:134) is omitted (recorded repair; no body uses
   decidability). Needs ROOT MAIN PROBE (G6 SobolevBirkhoff, F027 absent from mirror); the finiteA/finiteD bodies and
   the identical sobolevCoe body elaborated in mirror selftest F012_SELFTEST01 (ae633052). -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology ContDiff
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.HierarchyRiccati.Core
open NlsGge.SpectralFoundations NlsGge.Birkhoff NlsGge.Measure
open NlsGge.Atomic.Common

namespace NlsGge.ThirdConsultation.F
open NlsGge.GKDefinitionDesign

def finiteT (m : ℕ) (x : Hm1 m) : Hm1 m :=
  ofCarrier38 _ (birkhoffSobolev (m - 1)
    ((physicalSobolevFourierEquiv38 ((m - 1 : ℕ) : ℝ)).symm
      (toCarrier38 _ x)))

def finiteA (m : ℕ) (β : ℕ → ℝ) (x : Hm1 m) : ℝ :=
  ∑' n : ℤ, finiteHierarchyRate38 m β n * ‖sobolevCoe _ x n‖ ^ 2

def finiteD (m : ℕ) (β : ℕ → ℝ) (x : Hm1 m) : ℝ :=
  Vm38 m β (FinvH38 m x) - Rm38 m β (FinvH38 m x)

end NlsGge.ThirdConsultation.F
