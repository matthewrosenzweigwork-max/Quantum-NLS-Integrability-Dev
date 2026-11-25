/- KO-003 Basic module (proof development, AUTHOR; not self-reviewed).  Target NlsGge/ThirdConsultation/KO/Basic.lean, owner packet KO-003 (Pro ruling,
   PRO_DEFINITION_RESPONSE_FP80_02_03.md:1119).  The four definitions finiteGap, SmoothPhysical, spectralBand, bandInterior are Pro's bodies
   (DEFINITIONS/KO.lean.md:25-52) verbatim; imports as printed; independent of KO008.  One elaboration repair, listed: `open scoped Topology Matrix`
   became `open scoped Topology Matrix ContDiff` so that `∞` parses (error before repair: `expected token` at `ContDiff ℝ ∞ U`, request 90693baf);
   repaired elaboration: request 0cc8663d-f29a-450d-8409-e4851f53c358, exit 0. -/
import NlsGge.Spectral.ActualGapActionAllNE02_38
import NlsGge.Spectral.ActualQuasimomentumBoundaryFunctionE02_38
import NlsGge.Spectral.ActualQuasimomentumFullInfinityE02_38
import NlsGge.GK38.ActionRealBridge
import NlsGge.GK38.ActionBranchUpper
import NlsGge.Hierarchy.A01Spectral38
import Mathlib

noncomputable section
open MeasureTheory Filter
open scoped Topology Matrix ContDiff
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations
open NlsGge.HierarchyRiccati.Core

namespace NlsGge.ThirdConsultation

def finiteGap (u : PhysicalL2) : Prop :=
  {n : ℤ | actualGapLowerAllE02_38 u n ≠
    actualGapUpperAllE02_38 u n}.Finite

namespace KO

def SmoothPhysical (u : PhysicalL2) : Prop :=
  ∃ (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U)
    (hper : Function.Periodic U 1), smoothL2_38 U hU hper = u

def spectralBand (u : PhysicalL2) (n : ℤ) : Set ℝ :=
  Set.Icc (actualGapUpperAllE02_38 u n) (actualGapLowerAllE02_38 u (n + 1))

def bandInterior (u : PhysicalL2) (n : ℤ) : Set ℝ :=
  Set.Ioo (actualGapUpperAllE02_38 u n) (actualGapLowerAllE02_38 u (n + 1))

end KO
end NlsGge.ThirdConsultation
