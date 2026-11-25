import Mathlib
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Measure.WeightedScalarResidual
import NlsGge.Ramer.RamerLemma52

/- R142HOST HOST01 (proof development, AUTHOR; not self-reviewed, not accepted). SUPPORTING host (no packet increment), target
   NlsGge/ThirdConsultation/R/R142Host.lean. Hosts ONLY `L1Converges`, body VERBATIM from followup13
   DEFINITIONS/R.lean.md L100-102, under the `open` lines of that printed block (its design import list is not copied;
   this host imports only what the opens and the body need). grep NlsGge/ (2026-11-03): not declared (DEFGAP scan
   lists it). OneSmoothing is imported so the opened `NlsGge.ThirdConsultation.Common` namespace exists (B1). Needs ROOT
   MAIN PROBE. -/
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped ENNReal Topology BigOperators RealInnerProductSpace
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38
open NlsGge.Birkhoff NlsGge.Ramer
open NlsGge.ThirdConsultation.Common

namespace NlsGge.ThirdConsultation.R
noncomputable section

def L1Converges {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : ℕ → X → ℝ) (g : X → ℝ) : Prop :=
  Tendsto (fun N => eLpNorm (fun x => f N x-g x) 1 μ) atTop (𝓝 0)

end
end NlsGge.ThirdConsultation.R
