import Armstrong.Frozen.RawBeta.GKArcCurve38

set_option autoImplicit false
open Set Filter Topology Metric MeasureTheory intervalIntegral
namespace NlsGge.GK38
noncomputable section

def GKArcSheet38 {φ : GKPotential38} {m : ℤ}
    (a : GKRootedC1Arc38 φ m) : ℝ → ℂ := a.1.2


end
end NlsGge.GK38
