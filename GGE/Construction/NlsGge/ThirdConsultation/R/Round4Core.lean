import Mathlib
import NlsGge.Atomic.R.R023
import NlsGge.Sobolev.WeightedProjection

                                                                                                        
                                                                                                                                                                         
set_option autoImplicit false

open MeasureTheory Filter
open scoped Topology

namespace NlsGge.ThirdConsultation.R
noncomputable section

def HDeriv
    {E H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (i : H →L[ℝ] E) (Φ : E → H) (x : E) : H →L[ℝ] H :=
  (fderiv ℝ Φ x).comp i

def ambientProjectionCLM
    {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (s : ℝ) (N : ℕ) : RamerE c s →L[ℝ] RamerE c s :=
  (NlsGge.Pilot.weightedProjectionContinuous
    (NlsGge.Pilot.fullModeWeight c s)
    (NlsGge.Pilot.symmetricModes N)).restrictScalars ℝ

def TendstoInL2 {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : ℕ → X → ℝ) (g : X → ℝ) : Prop :=
  Tendsto (fun N => eLpNorm (fun x => f N x-g x) 2 μ) atTop (𝓝 0)

end
end NlsGge.ThirdConsultation.R
